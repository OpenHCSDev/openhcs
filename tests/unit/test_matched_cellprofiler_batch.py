"""The matched pilot preserves interpreter and output evidence identities."""

import hashlib
from pathlib import Path

import pytest
from objectstate.context_manager import config_context

from benchmark.matched_cellprofiler_batch import (
    _candidate_pipeline_config,
    _global_config,
    _native_python_executable,
    _output_inventory,
    _source_input_inventory,
    _worker_axis_evidence,
)
from openhcs.core.config import MultiprocessingStartMethod, PipelineConfig
from openhcs.core.progress.types import ProgressEvent


def test_native_python_keeps_virtual_environment_symlink(tmp_path: Path) -> None:
    base = tmp_path / "base-python"
    base.touch()
    venv_python = tmp_path / "venv-python"
    venv_python.symlink_to(base)

    selected = _native_python_executable(Path("venv-python"), tmp_path)

    assert selected == venv_python
    assert selected != selected.resolve()


def test_output_inventory_retains_relative_paths_and_content_digests(
    tmp_path: Path,
) -> None:
    images = tmp_path / "images"
    images.mkdir()
    output = images / "overlay.tiff"
    output.write_bytes(b"pixel evidence")

    inventory = _output_inventory(tmp_path, frozenset({output}))

    assert inventory == (
        {
            "path": "images/overlay.tiff",
            "sha256": hashlib.sha256(b"pixel evidence").hexdigest(),
        },
    )


def test_source_input_inventory_hashes_symlink_target(tmp_path: Path) -> None:
    source = tmp_path / "source.tif"
    source.write_bytes(b"microscopy pixels")
    staged = tmp_path / "staged"
    staged.mkdir()
    (staged / "source.tif").symlink_to(source)

    inventory = _source_input_inventory(staged)

    assert inventory == (
        {
            "path": "source.tif",
            "source_path": str(source),
            "size_bytes": len(b"microscopy pixels"),
            "sha256": hashlib.sha256(b"microscopy pixels").hexdigest(),
        },
    )


def test_candidate_worker_count_uses_ordinary_global_config(tmp_path: Path) -> None:
    config = _global_config(
        tmp_path,
        ("A01", "A12"),
        worker_count=2,
        start_method=MultiprocessingStartMethod.FORK,
    )

    assert config.num_workers == 2
    assert config.multiprocessing_start_method is MultiprocessingStartMethod.FORK
    assert config.materialize_runtime_artifacts is False


def test_candidate_pipeline_inherits_benchmark_worker_count(tmp_path: Path) -> None:
    global_config = _global_config(
        tmp_path,
        ("A01", "A12"),
        worker_count=2,
        start_method=MultiprocessingStartMethod.FORK,
    )

    with config_context(global_config):
        imported = PipelineConfig(
            num_workers=1,
            use_threading=True,
            multiprocessing_start_method=MultiprocessingStartMethod.SPAWN,
        )
        candidate = _candidate_pipeline_config(
            imported, global_config, tmp_path, ("A01", "A12")
        )

        assert candidate.num_workers == 2
        assert candidate.use_threading is False
        assert candidate.multiprocessing_start_method is MultiprocessingStartMethod.FORK


def _axis_event(axis_id: str, phase: str, pid: int, timestamp: float) -> ProgressEvent:
    return ProgressEvent.from_dict(
        {
            "execution_id": "job-1",
            "plate_id": "plate-1",
            "axis_id": axis_id,
            "step_name": "pipeline",
            "phase": phase,
            "status": "started" if phase == "axis_started" else "success",
            "percent": 0.0 if phase == "axis_started" else 100.0,
            "completed": 0 if phase == "axis_started" else 1,
            "total": 1,
            "timestamp": timestamp,
            "pid": pid,
        }
    )


def test_worker_axis_evidence_proves_distinct_overlapping_processes() -> None:
    events = (
        _axis_event("A01", "axis_started", 11, 1.0),
        _axis_event("A12", "axis_started", 22, 1.2),
        _axis_event("A12", "axis_completed", 22, 2.8),
        _axis_event("A01", "axis_completed", 11, 3.0),
    )

    evidence = _worker_axis_evidence(
        events, execution_id="job-1", expected_axes=2, expected_workers=2
    )

    assert evidence["worker_process_ids"] == (11, 22)
    assert evidence["worker_interval_overlap_seconds"] == pytest.approx(1.6)


def test_worker_axis_evidence_rejects_one_process_for_two_workers() -> None:
    events = (
        _axis_event("A01", "axis_started", 11, 1.0),
        _axis_event("A12", "axis_started", 11, 1.2),
        _axis_event("A12", "axis_completed", 11, 2.8),
        _axis_event("A01", "axis_completed", 11, 3.0),
    )

    with pytest.raises(RuntimeError, match="expected 2"):
        _worker_axis_evidence(
            events, execution_id="job-1", expected_axes=2, expected_workers=2
        )
