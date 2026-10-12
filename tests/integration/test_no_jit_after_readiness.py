"""Every Numba kernel is compiled by catalog preparation, never after readiness.

Benchmarks time pipeline compilation and execution, so neither may contain a
one-time cost. One cold run (empty Numba cache, empty catalog cache) of two
pipelines over a real execution server is counted with Numba's own compile
event, in every process: the server, the workers it forks and the client.

What this cannot see: a kernel reached only with a signature (dtype, rank,
layout) or on a branch that neither pipeline nor any preparation exercises; the
second test narrows that to signatures, since it fails for any kernel that
preparation leaves with no compiled signature at all. GPU kernels (CuPy,
pyclesperanto program builds) are not counted: the run is CPU-only.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

REPOSITORY = Path(__file__).resolve().parents[2]
TRACER = Path(__file__).resolve().parent / "helpers" / "numba_trace"
PIPELINES = (
    "tests/integration/test_main.py",
    "tests/integration/test_cellprofiler_generated_pipeline.py"
    "::test_cppipe_import_executes_through_canonical_zmq_path",
)


@pytest.fixture(scope="module")
def cold_run_events(tmp_path_factory: pytest.TempPathFactory) -> list[dict]:
    """Run the pipelines from empty caches and return what each process recorded."""
    root = tmp_path_factory.mktemp("cold_run")
    trace = root / "trace"
    trace.mkdir()
    environment = {
        **os.environ,
        "PYTHONPATH": os.pathsep.join(
            (str(TRACER), str(REPOSITORY), os.environ.get("PYTHONPATH", ""))
        ),
        "OPENHCS_NUMBA_TRACE_DIR": str(trace),
        "NUMBA_CACHE_DIR": str(root / "numba"),
        "XDG_DATA_HOME": str(root / "data"),
        "OPENHCS_CPU_ONLY": "1",
        "QT_QPA_PLATFORM": "offscreen",
        "DISPLAY": "",
        "WAYLAND_DISPLAY": "",
    }
    completed = subprocess.run(
        [
            sys.executable, "-m", "pytest", *PIPELINES,
            "--it-backends", "disk", "--it-microscopes", "ImageXpress",
            "--it-dims", "3d", "--it-exec-mode", "multiprocessing",
            "--it-zmq-mode", "zmq", "--it-visualizers", "none",
            "-q", "--tb=short", "-p", "no:cacheprovider", "-p", "no:randomly",
            f"--basetemp={root / 'pipelines'}",
        ],
        cwd=REPOSITORY,
        env=environment,
        capture_output=True,
        text=True,
        timeout=1800,
    )
    assert completed.returncode == 0, completed.stdout[-4000:] + completed.stderr[-2000:]
    return sorted(
        (
            json.loads(line)
            for path in trace.glob("*.jsonl")
            for line in path.read_text().splitlines()
        ),
        key=lambda event: event["time"],
    )


def _readiness_by_server(events: list[dict]) -> dict[int, dict]:
    """The first readiness mark of each execution server, by its process id."""
    ready: dict[int, dict] = {}
    for event in events:
        if event["kind"] == "ready":
            ready.setdefault(event["pid"], event)
    assert ready, "no execution server reported readiness; the tracer saw no server"
    return ready


def _is_after_readiness(event: dict, ready: dict[int, dict]) -> bool:
    """A server and the children it forks are judged against its own readiness.

    Any other process is a client: it executes nothing, so it has no reason to
    compile or load a kernel at any time.
    """
    server = ready.get(event["pid"]) or ready.get(event["parent"])
    return server is None or event["time"] > server["time"]


def test_no_kernel_is_compiled_or_loaded_after_readiness(
    cold_run_events: list[dict],
) -> None:
    ready = _readiness_by_server(cold_run_events)
    numba_events = [
        event for event in cold_run_events if event["kind"] in ("compiled", "loaded")
    ]
    assert any(
        event["kind"] == "compiled" and not _is_after_readiness(event, ready)
        for event in numba_events
    ), "preparation compiled nothing, so the counter proves nothing"

    late = [
        f"{event['kind']} pid {event['pid']} {event['kernel']} {event['signature']}"
        for event in numba_events
        if _is_after_readiness(event, ready)
    ]
    assert late == [], (
        "Numba worked after the server was ready, or in a client. Extend the "
        "preparation of the kernel's owner so catalog preparation compiles it:\n"
        + "\n".join(late)
    )


def test_preparation_compiles_every_kernel(cold_run_events: list[dict]) -> None:
    """Derived from the code, not from a pipeline: every kernel has a signature."""
    unprepared = sorted(
        {
            kernel
            for event in _readiness_by_server(cold_run_events).values()
            for kernel in event["unprepared"]
        }
    )
    assert unprepared == [], (
        "No preparation reaches these kernels, so their first use would compile "
        "them. Reach each from its owner's preparation, or delete it if nothing "
        "calls it:\n" + "\n".join(unprepared)
    )
