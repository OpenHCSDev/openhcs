"""Bound runtime emitters preserve the shared sink's gating and output effects."""

import logging

from openhcs.core.runtime_profile import (
    PROFILE_RUNTIME_ENV,
    PROFILE_RUNTIME_PATH_ENV,
    RuntimeProfiler,
)


def test_bound_profiler_disabled_has_no_output_effects(monkeypatch, tmp_path, caplog):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "false")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.bound.runtime.disabled"))

    with caplog.at_level(logging.INFO):
        profiler.log("phase", 0.125, objects=3)

    assert not profiler.enabled()
    assert not path.exists()
    assert not caplog.records


def test_bound_profiler_enabled_writes_same_event_to_both_sinks(
    monkeypatch, tmp_path, caplog
):
    path = tmp_path / "profile.log"
    monkeypatch.setenv(PROFILE_RUNTIME_ENV, "TRUE")
    monkeypatch.setenv(PROFILE_RUNTIME_PATH_ENV, str(path))
    profiler = RuntimeProfiler(logging.getLogger("test.bound.runtime.enabled"))

    with caplog.at_level(logging.INFO):
        profiler.log("phase", 0.125, objects=3, source="nuclei")

    assert profiler.enabled()
    expected = "RUNTIME_PROFILE phase 0.125000s objects=3 source=nuclei"
    assert path.read_text() == expected + "\n"
    assert [record.getMessage() for record in caplog.records] == [expected]
