"""The measured benchmark CLI as a session client, on a real execution server.

A run ends cleanly when its wait timeout passes (the timeout is on the run
request) or on Ctrl-C (StopExecution): the batch is cancelled and no execution
server is left running. A run never writes into its source plate: it executes
on a workspace mirrored from it, so a read-only source stays byte-identical.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

import psutil
import pytest

from benchmark.contracts.measured_run_receipt import MeasuredPipelineRunReceipt
from benchmark.contracts.run_artifacts import MeasuredPipelineRunArtifact

from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
RUN_DEADLINE_SECONDS = 300.0
SERVER_EXIT_SECONDS = 60.0


def _measured_inputs(tmp_path: Path) -> tuple[Path, Path]:
    """A plate large enough that its run is still going when it is stopped."""

    plate = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(plate),
        grid_size=(3, 3),
        tile_size=(256, 256),
        wavelengths=2,
        z_stack_levels=3,
        num_cells=40,
        wells=["A01", "A02", "B01", "B02", "C01", "C02"],
        format="ImageXpress",
        random_seed=11,
    ).generate_dataset()
    source = tmp_path / "pipeline.py"
    source.write_text(
        PipelineDocumentCodec.render(
            PipelineDocumentCodec.from_values(
                pipeline_config=PipelineConfig(),
                pipeline_steps=[
                    FunctionStep(name="Blur", func=(gaussian_blur, {"sigma": 4.0}))
                ],
            )
        ),
        encoding="utf-8",
    )
    return plate, source


def _source_state(root: Path) -> dict[str, tuple]:
    """Every entry's content digest, mtime and mode, relative to ``root``."""

    state: dict[str, tuple] = {}
    for path in sorted(root.rglob("*")):
        stat = path.lstat()
        digest = (
            hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
        )
        state[str(path.relative_to(root))] = (digest, stat.st_mtime_ns, stat.st_mode)
    return state


def _set_writable(root: Path, writable: bool) -> None:
    for path in (root, *root.rglob("*")):
        mode = path.stat().st_mode
        path.chmod(mode | 0o200 if writable else mode & ~0o222)


def _port(offset: int) -> int:
    return 26000 + offset + os.getpid() % 10000


def _command(
    plate: Path, source: Path, output_dir: Path, port: int, wait_ms: int
) -> tuple[str, ...]:
    return (
        sys.executable,
        "-c",
        "import sys; from benchmark.cellprofiler_benchmark_cli import main; "
        "sys.exit(main(sys.argv[1:]))",
        "run-measured",
        "--plate",
        str(plate),
        "--pipeline-source-file",
        str(source),
        "--output-dir",
        str(output_dir),
        "--run-id",
        "stopped",
        "--port",
        str(port),
        "--no-persistent",
        "--wait-timeout-ms",
        str(wait_ms),
    )


def _environment(tmp_path: Path) -> dict[str, str]:
    environment = {**os.environ, "PYTHONPATH": str(REPOSITORY_ROOT)}
    environment.setdefault("XDG_DATA_HOME", str(tmp_path / "xdg"))
    environment.pop("DISPLAY", None)
    return environment


def _servers_on(port: int) -> list[psutil.Process]:
    servers = []
    for process in psutil.process_iter(["cmdline"]):
        command = " ".join(process.info["cmdline"] or ())
        if "zmq_execution_server_launcher" in command and str(port) in command:
            servers.append(process)
    return servers


def _assert_no_server_left(port: int) -> None:
    deadline = time.monotonic() + SERVER_EXIT_SECONDS
    while _servers_on(port):
        if time.monotonic() > deadline:
            leftover = _servers_on(port)
            for process in leftover:
                process.kill()
            pytest.fail(f"Execution server left running on port {port}: {leftover}")
        time.sleep(0.5)


def _final_row(stderr: str) -> dict:
    rows = [json.loads(line) for line in stderr.splitlines() if line.startswith("{")]
    assert rows, stderr
    return rows[-1]


def test_wait_timeout_stops_the_run_and_its_server(tmp_path: Path) -> None:
    plate, source = _measured_inputs(tmp_path)
    port = _port(0)
    completed = subprocess.run(
        _command(plate, source, tmp_path / "evidence", port, wait_ms=1),
        cwd=REPOSITORY_ROOT,
        env=_environment(tmp_path),
        capture_output=True,
        text=True,
        timeout=RUN_DEADLINE_SECONDS,
    )

    assert completed.returncode == 1, completed.stderr[-4000:]
    assert "did not complete" in completed.stderr
    assert "exceeded 1 ms" in completed.stderr
    assert _final_row(completed.stderr)["terminal_status"] == "cancelled"
    assert not (tmp_path / "evidence" / "measured_pipeline_receipt.json").exists()
    _assert_no_server_left(port)


def test_ctrl_c_stops_the_run_and_its_server(tmp_path: Path) -> None:
    plate, source = _measured_inputs(tmp_path)
    port = _port(1)
    process = subprocess.Popen(
        _command(plate, source, tmp_path / "evidence", port, wait_ms=600_000),
        cwd=REPOSITORY_ROOT,
        env=_environment(tmp_path),
        stderr=subprocess.PIPE,
        stdout=subprocess.PIPE,
        text=True,
    )
    stderr_lines: list[str] = []
    try:
        for line in process.stderr:
            stderr_lines.append(line)
            if "Ordinary pipeline run started" in line:
                break
        else:
            pytest.fail("".join(stderr_lines)[-4000:])
        time.sleep(1.0)
        process.send_signal(signal.SIGINT)
        _stdout, rest = process.communicate(timeout=RUN_DEADLINE_SECONDS)
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    stderr = "".join(stderr_lines) + rest

    assert process.returncode == 130, stderr[-4000:]
    assert _final_row(stderr)["terminal_status"] == "cancelled"
    _assert_no_server_left(port)


def test_read_only_source_plate_completes_and_stays_byte_identical(
    tmp_path: Path,
) -> None:
    generated, source = _measured_inputs(tmp_path)
    plate = tmp_path / "evidence_source"
    shutil.copytree(generated, plate)
    _set_writable(plate, False)
    before = _source_state(plate)
    output_dir = tmp_path / "evidence"
    port = _port(2)
    try:
        completed = subprocess.run(
            _command(plate, source, output_dir, port, wait_ms=int(RUN_DEADLINE_SECONDS * 1000)),
            cwd=REPOSITORY_ROOT,
            env=_environment(tmp_path),
            capture_output=True,
            text=True,
            timeout=RUN_DEADLINE_SECONDS,
        )
        after = _source_state(plate)
    finally:
        _set_writable(plate, True)

    assert completed.returncode == 0, completed.stderr[-4000:]
    receipt = MeasuredPipelineRunReceipt.read(
        MeasuredPipelineRunArtifact.RECEIPT.path_in(output_dir)
    )
    assert receipt.plate_id == str(plate)
    assert Path(receipt.execution_plate_id).is_relative_to(output_dir / "workspace")
    assert after == before
    _assert_no_server_left(port)
