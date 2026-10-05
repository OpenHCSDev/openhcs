"""Bound runtime emitters preserve the shared sink's gating and output effects."""

import logging
import builtins
from concurrent.futures import ThreadPoolExecutor
from threading import Barrier

import pytest

from openhcs.core.runtime_profile import (
    PROFILE_RUNTIME_ENV,
    PROFILE_RUNTIME_PATH_ENV,
    RuntimeProfiler,
    RuntimeProfileLogger,
)


def test_bound_profiler_disabled_has_no_output_effects(monkeypatch, tmp_path, caplog):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "false")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.bound.runtime.disabled"))

    with caplog.at_level(logging.INFO):
        with RuntimeProfileLogger.run():
            profiler.log("phase", 0.125, objects=3)

    assert not profiler.enabled()
    assert not path.exists()
    assert not caplog.records


def test_bound_profiler_buffers_without_io_then_flushes_once(
    monkeypatch, tmp_path, caplog
):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "TRUE")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.bound.runtime.enabled"))
    writes = []
    original_open = builtins.open

    def track_open(*args, **kwargs):
        writes.append(args[0])
        return original_open(*args, **kwargs)

    monkeypatch.setattr(builtins, "open", track_open)
    metadata = {"CHANNEL": 2}

    with caplog.at_level(logging.INFO):
        with RuntimeProfileLogger.run():
            profiler.log("phase", 0.125, objects=3, source="nuclei")
            profiler.log("metadata", 0.25, components=metadata)
            metadata["CHANNEL"] = 7
            assert not path.exists()
            assert not caplog.records
            assert not writes

    assert profiler.enabled()
    expected = "RUNTIME_PROFILE phase 0.125000s objects=3 source=nuclei"
    second = "RUNTIME_PROFILE metadata 0.250000s components={'CHANNEL': 2}"
    assert path.read_text() == expected + "\n" + second + "\n"
    assert [record.getMessage() for record in caplog.records][:2] == [expected, second]
    assert len(writes) == 1


def test_profile_error_flush_keeps_original_failure_and_next_run_clean(
    monkeypatch, tmp_path
):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "true")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.runtime.failure"))
    from openhcs.core.orchestrator.cancellation import ExecutionCancelledError

    with pytest.raises(ExecutionCancelledError, match="cancelled"):
        with RuntimeProfileLogger.run(execution_id="cancelled"):
            profiler.log("before_cancel", 0.5)
            raise ExecutionCancelledError("cancelled")
    profiler.log("out_of_run", 1.0)
    with RuntimeProfileLogger.run(execution_id="next"):
        profiler.log("next", 0.125)
    lines = path.read_text().splitlines()
    assert len(lines) == 2
    assert "before_cancel" in lines[0] and "execution_id=cancelled" in lines[0]
    assert "execution_id=next" in lines[1] and "out_of_run" not in path.read_text()


def test_profile_runs_remain_independent_in_concurrent_worker_threads(
    monkeypatch, tmp_path
):
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "true")
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    barrier = Barrier(2)
    profiler = RuntimeProfiler(logging.getLogger("test.runtime.concurrent"))

    def worker(name):
        with RuntimeProfileLogger.run(execution_id=name):
            profiler.log("first", 0.1, owner=name)
            barrier.wait()
            profiler.log("last", 0.2, owner=name)

    with ThreadPoolExecutor(max_workers=2) as executor:
        tuple(executor.map(worker, ("left", "right")))
    lines = path.read_text().splitlines()
    assert len(lines) == 4
    for name in ("left", "right"):
        owned = [line for line in lines if f"execution_id={name}" in line]
        assert len(owned) == 2 and all(f"owner={name}" in line for line in owned)
