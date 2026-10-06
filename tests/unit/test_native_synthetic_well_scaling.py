"""Synthetic native wells retain source bytes and a declared image universe."""

import hashlib
from pathlib import Path

import pytest

from benchmark.native_synthetic_well_scaling import (
    _concurrent_timing,
    _source_paths,
    _stage_wells,
)


def test_concurrent_timing_includes_preparation_before_module_callbacks() -> None:
    reports = tuple(
        {
            "observations": [
                {
                    "repetition": 0,
                    "invocation_started_monotonic_seconds": invocation,
                    "pipeline_started_monotonic_seconds": pipeline,
                    "completed_monotonic_seconds": completion,
                }
            ]
        }
        for invocation, pipeline, completion in ((1.0, 2.0, 10.0), (1.5, 3.0, 11.0))
    )

    timing = _concurrent_timing(reports, 0)

    assert timing["pipeline_execution_makespan_seconds"] == 9.0
    assert timing["pipeline_overlap_seconds"] == 7.0
    assert timing["invocation_through_completion_makespan_seconds"] == 10.0


def test_staging_reuses_exact_declared_source_bytes(tmp_path: Path) -> None:
    source_a = tmp_path / "source" / "Ch1_1.tif"
    source_a.parent.mkdir()
    source_a.write_bytes(b"channel one")
    source_b = source_a.with_name("Ch6_1.tif")
    source_b.write_bytes(b"channel six")
    mappings = {
        "virtual/ch6": {"backend": "disk", "backend_address": str(source_b)},
        "virtual/ch1": {"backend": "disk", "backend_address": str(source_a)},
    }

    paths = _source_paths(mappings)
    inventory = _stage_wells(paths, tmp_path / "inputs", ("W001", "W002"))

    assert paths == (source_a, source_b)
    assert [row["path"] for row in inventory] == [
        "W001/Ch1_1.tif",
        "W001/Ch6_1.tif",
        "W002/Ch1_1.tif",
        "W002/Ch6_1.tif",
    ]
    for row in inventory:
        staged = tmp_path / "inputs" / row["path"]
        assert staged.is_symlink()
        assert staged.resolve() == Path(row["source_path"])
        assert staged.read_bytes() == Path(row["source_path"]).read_bytes()
        assert row["sha256"] == hashlib.sha256(staged.read_bytes()).hexdigest()


def test_source_plane_selection_rejects_ambiguous_flat_staging(
    tmp_path: Path,
) -> None:
    first = tmp_path / "first" / "image.tif"
    second = tmp_path / "second" / "image.tif"
    first.parent.mkdir()
    second.parent.mkdir()
    first.touch()
    second.touch()

    with pytest.raises(ValueError, match="unique source basenames"):
        _source_paths(
            {
                "first": {"backend": "disk", "backend_address": str(first)},
                "second": {"backend": "disk", "backend_address": str(second)},
            }
        )
