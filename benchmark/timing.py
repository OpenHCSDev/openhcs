"""Typed phase timing for benchmark runs."""

from __future__ import annotations

import csv
import io
import json
import time
from collections.abc import Mapping
from contextlib import contextmanager
from dataclasses import asdict, dataclass
from enum import StrEnum, auto
from math import isfinite
from pathlib import Path
from typing import Iterator

from python_introspect import dataclass_from_mapping
from zmqruntime.messages import ExecutionRecord, ExecutionStatus

from openhcs.core.config import Backend
from openhcs.core.vfs_protocol import FileManagerLike


class BenchmarkPhase(StrEnum):
    """Semantic benchmark phases reported independently."""

    RESOLVE_SOURCE = auto()
    PARSE_CPPIPE = auto()
    COMPILE_DIALECT = auto()
    MATERIALIZE_SOURCE_SCHEMA = auto()
    INITIALIZE_RUNTIME = auto()
    COMPILE_OPENHCS = auto()
    EXECUTE_OPENHCS = auto()
    SERVER_COMPILATION_JOB = auto()
    SERVER_PIPELINE_JOB = auto()
    SUBMIT_OPENHCS = auto()
    WAIT_OPENHCS = auto()
    EXECUTE_NATIVE_CP = auto()
    VALIDATE_RUNTIME = auto()
    SNAPSHOT_OUTPUTS = auto()
    COMPARE_EQUIVALENCE = auto()
    READ_CACHE = auto()
    WRITE_CACHE = auto()

    @property
    def is_nested_runtime_observation(self) -> bool:
        """Whether this interval overlaps the client submit/wait wall phases."""
        return self in {
            BenchmarkPhase.COMPILE_OPENHCS,
            BenchmarkPhase.EXECUTE_OPENHCS,
            BenchmarkPhase.SERVER_COMPILATION_JOB,
            BenchmarkPhase.SERVER_PIPELINE_JOB,
        }


def additive_phase_total_seconds(phase_seconds: Mapping[str, float]) -> float | None:
    """Sum only disjoint benchmark phases, never nested runtime observations."""
    additive: list[float] = []
    for phase_name, seconds in phase_seconds.items():
        try:
            phase = BenchmarkPhase[phase_name]
        except KeyError as exc:
            raise ValueError(f"Unknown benchmark phase: {phase_name!r}.") from exc
        if not isfinite(seconds) or seconds < 0:
            raise ValueError(f"Invalid benchmark phase duration: {phase_name!r}.")
        if not phase.is_nested_runtime_observation:
            additive.append(seconds)
    return sum(additive) if additive else None


def completed_server_execution_seconds(
    record: ExecutionRecord, *, expected_execution_id: str | None = None
) -> float:
    """Measure a completed ordinary job using its server-owned time bounds."""
    start_time = record.start_time
    end_time = record.end_time
    if (
        record.status != ExecutionStatus.COMPLETE.value
        or (
            expected_execution_id is not None
            and record.execution_id != expected_execution_id
        )
        or not isinstance(start_time, (int, float))
        or not isinstance(end_time, (int, float))
        or not isfinite(start_time)
        or not isfinite(end_time)
        or end_time < start_time
    ):
        raise ValueError(
            f"Completed OpenHCS job {record.execution_id!r} has no valid server time bounds."
        )
    return float(end_time - start_time)


@dataclass(frozen=True, slots=True)
class PhaseTimingRecord:
    """One observed benchmark phase duration."""

    run_id: str
    pipeline_name: str
    tool: str
    phase: BenchmarkPhase
    seconds: float
    cached: bool = False

    def as_payload(self) -> dict[str, object]:
        """Return a JSON/CSV-stable record payload."""
        payload = asdict(self)
        payload["phase"] = self.phase.name
        return payload

    @classmethod
    def from_payload(cls, payload: Mapping[str, object]) -> "PhaseTimingRecord":
        """Decode the stable phase name rather than the enum's ordinal value."""

        phase_name = payload.get("phase")
        if not isinstance(phase_name, str):
            raise TypeError("Phase timing phase must be a declared name.")
        try:
            phase = BenchmarkPhase[phase_name]
        except KeyError as exc:
            raise ValueError(f"Unknown benchmark phase: {phase_name!r}.") from exc
        return dataclass_from_mapping(cls, {**payload, "phase": phase})


class PhaseTimingTrace:
    """Append-only phase timing trace for one benchmark run."""

    def __init__(self, *, run_id: str, pipeline_name: str, tool: str) -> None:
        if not run_id:
            raise ValueError("PhaseTimingTrace.run_id cannot be empty.")
        if not pipeline_name:
            raise ValueError("PhaseTimingTrace.pipeline_name cannot be empty.")
        if not tool:
            raise ValueError("PhaseTimingTrace.tool cannot be empty.")
        self.run_id = run_id
        self.pipeline_name = pipeline_name
        self.tool = tool
        self._records: list[PhaseTimingRecord] = []

    @property
    def records(self) -> tuple[PhaseTimingRecord, ...]:
        """Recorded phases in observation order."""
        return tuple(self._records)

    @contextmanager
    def phase(
        self,
        phase: BenchmarkPhase,
        *,
        cached: bool = False,
    ) -> Iterator[None]:
        """Time a benchmark phase and append its record."""
        normalized_phase = BenchmarkPhase(phase)
        started_at = time.perf_counter()
        try:
            yield
        finally:
            self.record(
                normalized_phase,
                seconds=time.perf_counter() - started_at,
                cached=cached,
            )

    def record(
        self,
        phase: BenchmarkPhase,
        *,
        seconds: float,
        cached: bool = False,
    ) -> None:
        """Append an externally measured phase duration."""
        if not isfinite(seconds) or seconds < 0:
            raise ValueError(
                "PhaseTimingRecord.seconds must be finite and non-negative."
            )
        self._records.append(
            PhaseTimingRecord(
                run_id=self.run_id,
                pipeline_name=self.pipeline_name,
                tool=self.tool,
                phase=BenchmarkPhase(phase),
                seconds=float(seconds),
                cached=bool(cached),
            )
        )

    def payloads(self) -> tuple[dict[str, object], ...]:
        """Return JSON/CSV-stable payloads for all records."""
        return tuple(record.as_payload() for record in self._records)


def write_phase_timing_jsonl(
    path: Path,
    records: tuple[PhaseTimingRecord, ...],
    *,
    filemanager: FileManagerLike | None = None,
    backend: Backend = Backend.DISK,
) -> None:
    """Write phase timing records as newline-delimited JSON."""
    content = "".join(
        json.dumps(record.as_payload(), sort_keys=True) + "\n" for record in records
    )
    _save_text(path, content, filemanager=filemanager, backend=backend)


def write_phase_timing_csv(
    path: Path,
    records: tuple[PhaseTimingRecord, ...],
    *,
    filemanager: FileManagerLike | None = None,
    backend: Backend = Backend.DISK,
) -> None:
    """Write phase timing records as a long-table CSV."""
    fieldnames = ("run_id", "pipeline_name", "tool", "phase", "seconds", "cached")
    handle = io.StringIO()
    writer = csv.DictWriter(handle, fieldnames=fieldnames)
    writer.writeheader()
    for record in records:
        writer.writerow(record.as_payload())
    _save_text(path, handle.getvalue(), filemanager=filemanager, backend=backend)


def _save_text(
    path: Path,
    content: str,
    *,
    filemanager: FileManagerLike | None,
    backend: Backend,
) -> None:
    """Save text through FileManager when available, otherwise use local disk."""
    if filemanager is not None:
        filemanager.ensure_directory(path.parent, backend.value)
        filemanager.save(content, path, backend.value)
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")
