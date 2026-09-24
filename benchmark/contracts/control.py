"""Lightweight agent-facing benchmark inspection contracts."""

from __future__ import annotations

from dataclasses import dataclass
from typing import ClassVar

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

    DEFAULT_ARTIFACT_OFFSET: ClassVar[int] = 0
    DEFAULT_ARTIFACT_LIMIT: ClassVar[int] = 128
    MAX_ARTIFACT_LIMIT: ClassVar[int] = 512

    output_dir: str
    artifact_offset: int = DEFAULT_ARTIFACT_OFFSET
    artifact_limit: int = DEFAULT_ARTIFACT_LIMIT

    def __post_init__(self) -> None:
        if type(self.artifact_offset) is not int or self.artifact_offset < 0:
            raise ValueError("artifact_offset must be a non-negative integer.")
        if (
            type(self.artifact_limit) is not int
            or not 1 <= self.artifact_limit <= self.MAX_ARTIFACT_LIMIT
        ):
            raise ValueError(
                f"artifact_limit must be between 1 and {self.MAX_ARTIFACT_LIMIT}."
            )


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
    case_names: tuple[str, ...]
    repeats: int | None
    rerun_command: tuple[str, ...]
    rerun_working_directory: str | None
    structured_artifacts: tuple[BenchmarkStructuredArtifact, ...]
    next_artifact_offset: int | None
    warnings: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class BenchmarkRunReport:
    """Bounded human-readable report derived from a comparison-run receipt."""

    schema_version: str
    output_dir: str
    markdown: str
    warnings: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunInspectionRequest:
    """Select one completed ordinary-pipeline measurement directory."""

    output_dir: str


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunFinalizationRequest:
    """Label evidence for an already-completed ordinary execution job."""

    job_id: str
    run_id: str
    pipeline_name: str


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
    """Receipt/source/job-evidence inspection; output files are not verified."""

    schema_version: str
    output_dir: str
    receipt: MeasuredPipelineRunReceipt | None
    unreceipted_artifacts: tuple[MeasuredPipelineRunArtifact, ...]
    source_evidence: tuple[MeasuredSourceEvidence, ...]
    observation_present: bool
    results_summary_present: bool
    observation_integrity_verified: bool
    results_summary_integrity_verified: bool
    retained_evidence_valid: bool
    warnings: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class MeasuredPipelineRunReport:
    """Human-readable report derived from the same typed inspection."""

    schema_version: str
    output_dir: str
    markdown: str
    warnings: tuple[str, ...]
