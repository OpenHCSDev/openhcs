"""Lightweight agent-facing benchmark inspection contracts."""

from __future__ import annotations

from dataclasses import dataclass

from benchmark.contracts.run_artifacts import (
    ComparisonRunArtifact,
    StructuredArtifactFormat,
)
from benchmark.contracts.run_receipt import ComparisonSuiteRunStatus


@dataclass(frozen=True, slots=True)
class BenchmarkRunInspectionRequest:
    """Select one benchmark output directory for read-only inspection."""

    output_dir: str


@dataclass(frozen=True, slots=True)
class BenchmarkStructuredArtifact:
    """One discovered structured result artifact."""

    path: str
    relative_path: str
    format: StructuredArtifactFormat
    mime_type: str
    size_bytes: int
    declared_identity: ComparisonRunArtifact | None


@dataclass(frozen=True, slots=True)
class BenchmarkRunInspection:
    """Agent-facing projection of benchmark progress, rerun data, and outputs."""

    schema_version: str
    output_dir: str
    suite_id: str | None
    recorded_status: ComparisonSuiteRunStatus | None
    completed_observation_count: int
    expected_observation_count: int | None
    progress_fraction: float | None
    manifest_path: str | None
    rerun_command: tuple[str, ...]
    rerun_working_directory: str | None
    structured_artifacts: tuple[BenchmarkStructuredArtifact, ...]
    warnings: tuple[str, ...]
