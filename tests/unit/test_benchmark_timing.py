from __future__ import annotations

import csv
import json
from pathlib import Path

import pytest
from zmqruntime.messages import ExecutionRecord

from benchmark.timing import (
    BenchmarkPhase,
    PhaseTimingRecord,
    PhaseTimingTrace,
    additive_phase_total_seconds,
    completed_server_execution_seconds,
    write_phase_timing_csv,
    write_phase_timing_jsonl,
)
from openhcs.core.config import Backend


class FakeFileManager:
    def __init__(self) -> None:
        self.saved: dict[Path, tuple[str, str]] = {}
        self.directories: list[tuple[Path, str]] = []

    def ensure_directory(self, directory: Path, backend: str) -> str:
        self.directories.append((Path(directory), backend))
        return str(directory)

    def save(self, data: str, output_path: Path, backend: str) -> None:
        self.saved[Path(output_path)] = (data, backend)


def test_phase_timing_trace_records_typed_phase_payload() -> None:
    trace = PhaseTimingTrace(run_id="run-1", pipeline_name="pipe", tool="OpenHCS")

    trace.record(BenchmarkPhase.COMPILE_DIALECT, seconds=0.25)

    assert trace.payloads() == (
        {
            "run_id": "run-1",
            "pipeline_name": "pipe",
            "tool": "OpenHCS",
            "phase": "COMPILE_DIALECT",
            "seconds": 0.25,
            "cached": False,
        },
    )
    assert PhaseTimingRecord.from_payload(trace.payloads()[0]) == trace.records[0]


def test_phase_timing_rejects_unknown_persisted_phase() -> None:
    with pytest.raises(ValueError, match="Unknown benchmark phase"):
        PhaseTimingRecord.from_payload(
            {
                "run_id": "run-1",
                "pipeline_name": "pipe",
                "tool": "OpenHCS",
                "phase": "NOT_A_DECLARED_PHASE",
                "seconds": 0.25,
                "cached": False,
            }
        )


def test_additive_total_excludes_overlapping_server_and_progress_windows() -> None:
    assert (
        additive_phase_total_seconds(
            {
                BenchmarkPhase.SUBMIT_OPENHCS.name: 1.0,
                BenchmarkPhase.WAIT_OPENHCS.name: 25.0,
                BenchmarkPhase.COMPILE_OPENHCS.name: 15.0,
                BenchmarkPhase.EXECUTE_OPENHCS.name: 10.0,
                BenchmarkPhase.SERVER_COMPILATION_JOB.name: 15.0,
                BenchmarkPhase.SERVER_PIPELINE_JOB.name: 10.0,
                BenchmarkPhase.COMPARE_EQUIVALENCE.name: 2.0,
            }
        )
        == 28.0
    )
    assert (
        additive_phase_total_seconds({BenchmarkPhase.SERVER_PIPELINE_JOB.name: 10.0})
        is None
    )


@pytest.mark.parametrize("seconds", (float("nan"), float("inf"), -1.0))
def test_phase_timing_rejects_invalid_duration(seconds: float) -> None:
    trace = PhaseTimingTrace(run_id="run-1", pipeline_name="pipe", tool="OpenHCS")
    with pytest.raises(ValueError, match="finite and non-negative"):
        trace.record(BenchmarkPhase.SERVER_PIPELINE_JOB, seconds=seconds)


def test_completed_server_duration_uses_exact_ordinary_job() -> None:
    record = ExecutionRecord(
        execution_id="execution-1",
        plate_id="plate",
        client_address=None,
        status="complete",
        start_time=10.0,
        end_time=12.5,
    )
    assert (
        completed_server_execution_seconds(record, expected_execution_id="execution-1")
        == 2.5
    )
    with pytest.raises(ValueError, match="no valid server time bounds"):
        completed_server_execution_seconds(record, expected_execution_id="other")


@pytest.mark.parametrize(
    ("start_time", "end_time"),
    ((None, 2.0), (2.0, None), (2.0, 1.0), (0.0, float("nan"))),
)
def test_completed_server_duration_rejects_invalid_bounds(
    start_time: float | None, end_time: float | None
) -> None:
    record = ExecutionRecord(
        execution_id="execution-1",
        plate_id="plate",
        client_address=None,
        status="complete",
        start_time=start_time,
        end_time=end_time,
    )
    with pytest.raises(ValueError, match="no valid server time bounds"):
        completed_server_execution_seconds(record)


def test_phase_timing_writers_can_use_filemanager_vfs() -> None:
    records = (
        PhaseTimingRecord(
            run_id="run-1",
            pipeline_name="pipe",
            tool="OpenHCS",
            phase=BenchmarkPhase.EXECUTE_OPENHCS,
            seconds=1.5,
        ),
    )
    filemanager = FakeFileManager()

    write_phase_timing_jsonl(
        Path("reports/phases.jsonl"),
        records,
        filemanager=filemanager,
        backend=Backend.DISK,
    )
    write_phase_timing_csv(
        Path("reports/phases.csv"),
        records,
        filemanager=filemanager,
        backend=Backend.DISK,
    )

    jsonl, jsonl_backend = filemanager.saved[Path("reports/phases.jsonl")]
    csv_text, csv_backend = filemanager.saved[Path("reports/phases.csv")]
    assert json.loads(jsonl)["phase"] == "EXECUTE_OPENHCS"
    assert csv.DictReader(csv_text.splitlines()).fieldnames == [
        "run_id",
        "pipeline_name",
        "tool",
        "phase",
        "seconds",
        "cached",
    ]
    assert jsonl_backend == Backend.DISK.value
    assert csv_backend == Backend.DISK.value
