"""Lightweight agent-facing benchmark inspection contracts."""

from __future__ import annotations

from dataclasses import dataclass

from benchmark.contracts.measured_run_receipt import MeasuredPipelineRunReceipt
from benchmark.contracts.run_artifacts import (
    ComparisonRunArtifact,
    MeasuredPipelineRunArtifact,
    StructuredArtifactFormat,
)
from benchmark.contracts.run_receipt import ComparisonSuiteRunStatus


@dataclass(frozen=True, slots=True)
class BenchmarkCaseDiscoveryRequest:
    """Select exact case names from one comparison manifest."""

    manifest_path: str
    case_names: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class BenchmarkCaseSummary:
    """Source readiness projected from one manifest-owned case."""

    name: str
    dataset_id: str
    dataset_path: str
    cppipe_path: str
    dataset_present: bool
    cppipe_present: bool
    microscope_type: str | None


@dataclass(frozen=True, slots=True)
class BenchmarkCaseCatalog:
    """Read-only selected work; no dataset acquisition or run submission."""

    schema_version: str
    manifest_path: str
    cases: tuple[BenchmarkCaseSummary, ...]
    warnings: tuple[str, ...]


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


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunInspectionRequest:
    """Select one completed ordinary-pipeline measurement directory."""

    output_dir: str


@dataclass(frozen=True, slots=True)
class MeasuredSourceEvidence:
    """Bounded digest check for one declared source snapshot."""

    artifact: MeasuredPipelineRunArtifact
    path: str
    expected_sha256: str
    actual_sha256: str | None
    valid: bool


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunInspection:
    """Receipt-derived inspection; it does not reconstruct runtime job state."""

    schema_version: str
    output_dir: str
    receipt: MeasuredPipelineRunReceipt | None
    source_evidence: tuple[MeasuredSourceEvidence, ...]
    observation_present: bool
    results_summary_present: bool
    warnings: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunReport:
    """Human-readable report derived from the same typed inspection."""

    schema_version: str
    output_dir: str
    markdown: str
    warnings: tuple[str, ...]
