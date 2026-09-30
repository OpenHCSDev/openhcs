"""Native batch completion evidence survives loss of its controller process."""

import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

import benchmark.matched_cellprofiler_batch as matched_batch


def wait_for_path(path: Path, timeout: float = 10) -> None:
    deadline = time.monotonic() + timeout
    while not path.exists():
        if time.monotonic() >= deadline:
            pytest.fail(f"Worker did not write {path}")
        time.sleep(0.01)


@pytest.mark.parametrize("failure", ("returncode", "missing-report", "timeout"))
def test_native_bridge_keeps_failure_evidence(tmp_path, monkeypatch, failure):
    request = tmp_path / "request.json"
    request.write_text("{}")

    def run(command, **kwargs):
        kwargs["stdout"].write("progress before failure\n")
        kwargs["stderr"].write("native failure details\n")
        if failure == "timeout":
            raise subprocess.TimeoutExpired(command, 1)
        return subprocess.CompletedProcess(command, 7 if failure == "returncode" else 0)

    monkeypatch.setattr(matched_batch.subprocess, "run", run)
    error = {
        "returncode": subprocess.CalledProcessError,
        "missing-report": FileNotFoundError,
        "timeout": subprocess.TimeoutExpired,
    }[failure]
    with pytest.raises(error):
        matched_batch._invoke_native_worker(
            native_python=Path(sys.executable),
            worker_script=tmp_path / "worker.py",
            request_path=request,
            evidence_prefix=tmp_path / "native",
            project_root=tmp_path,
            repetitions=1,
        )
    assert (tmp_path / "native_stdout.log").read_text() == "progress before failure\n"
    assert (tmp_path / "native_stderr.log").read_text() == "native failure details\n"


def test_native_worker_finishes_report_after_controller_termination(tmp_path):
    worker = tmp_path / "worker.py"
    worker.write_text("""
import json,os,sys,time
from pathlib import Path
request=json.loads(Path(sys.argv[1]).read_text())
root=Path(request['root'])
print('live native progress',flush=True)
print('live native diagnostics',file=sys.stderr,flush=True)
(root/'started.json').write_text(json.dumps({'pid':os.getpid()}))
deadline=time.monotonic()+15
while not (root/'continue').exists():
    if time.monotonic()>=deadline:raise RuntimeError('test controller did not release worker')
    time.sleep(.01)
Path(request['report_path']).write_text(json.dumps({'worker_completed':True}))
print('worker complete',flush=True)
(root/'finished').touch()
""")
    request = tmp_path / "request.json"
    request.write_text(json.dumps({"root": str(tmp_path)}))
    project_root = Path(__file__).resolve().parents[2]
    program = """
import sys
from pathlib import Path
from benchmark.matched_cellprofiler_batch import _invoke_native_worker
root=Path(sys.argv[1])
_invoke_native_worker(native_python=Path(sys.executable),worker_script=root/'worker.py',request_path=root/'request.json',evidence_prefix=root/'native',project_root=root,repetitions=1)
"""
    worker_pid = None
    with (tmp_path / "controller.log").open("w") as log:
        controller = subprocess.Popen(
            [sys.executable, "-c", program, str(tmp_path)],
            cwd=project_root,
            stdout=log,
            stderr=subprocess.STDOUT,
        )
        try:
            wait_for_path(tmp_path / "started.json")
            worker_pid = json.loads((tmp_path / "started.json").read_text())["pid"]
            assert (
                tmp_path / "native_stdout.log"
            ).read_text() == "live native progress\n"
            assert (
                tmp_path / "native_stderr.log"
            ).read_text() == "live native diagnostics\n"
            controller.terminate()
            controller.wait(timeout=5)
            (tmp_path / "continue").touch()
            wait_for_path(tmp_path / "finished")
            assert json.loads((tmp_path / "native_report.json").read_text()) == {
                "worker_completed": True
            }
            assert "worker complete" in (tmp_path / "native_stdout.log").read_text()
        finally:
            if controller.poll() is None:
                controller.terminate()
                controller.wait(timeout=5)
            (tmp_path / "continue").touch()
            if worker_pid is not None and not (tmp_path / "finished").exists():
                try:
                    os.kill(worker_pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
