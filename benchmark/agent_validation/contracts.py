"""Typed contracts for blind autonomous image-analysis validation."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from pathlib import Path

import numpy as np

TaskParameterValue = str | int | float | bool
ExpectedValue = np.ndarray | int | float | tuple[str, ...] | None


class EvidenceClass(Enum):
    """Relationship between an expected result and biological truth."""

    INDEPENDENT_GROUND_TRUTH = "independent_ground_truth"
    DETERMINISTIC_PARITY = "deterministic_parity"
    VISUAL_QC_ONLY = "visual_qc_only"


class OutputKind(Enum):
    """Materialized result family emitted by one validation task."""

    ARRAY = "array"
    LABEL_IMAGE = "label_image"
    SCALAR = "scalar"
    TABLE = "table"


class FunctionAvailabilityExpectation(Enum):
    """Expected catalogue decision before a pipeline is authored."""

    REGISTRY_FIRST = "registry_first"
    CUSTOM_FUNCTION_REQUIRED = "custom_function_required"


class DiagnosticCheck(Enum):
    """Observable image-analysis failure classes scored across attempts."""

    MULTI_PERCENTILE = "multi_percentile"
    NORMALIZATION_SCOPE = "normalization_scope"
    MISSED_SIGNAL = "missed_signal"
    UNSUPPORTED_MASK = "unsupported_mask"
    SPLIT = "split"
    MERGE = "merge"
    DISCONNECTED_TRACE = "disconnected_trace"
    CROSSING_OWNERSHIP = "crossing_ownership"
    TILE_SEAM = "tile_seam"
    SATURATION = "saturation"
    COUNT_DISTRIBUTION = "count_distribution"
    AREA_DISTRIBUTION = "area_distribution"
    FOREGROUND_DISTRIBUTION = "foreground_distribution"


class DslRequirement(Enum):
    """OpenHCS mental-model boundaries that must appear in run evidence."""

    VARIABLE_COMPONENTS = "variable_components"
    GROUP_BY = "group_by"
    SEQUENTIAL_FUNCTION_PATTERN = "sequential_function_pattern"
    SOURCE_BINDINGS = "source_bindings"
    ARTIFACT_MATERIALIZATION = "artifact_materialization"
    COMPILE_RUN_BOUNDARY = "compile_run_boundary"
    SIGNATURE_DERIVED_EXPOSURE = "signature_derived_exposure"


class ArchitectureViolation(Enum):
    """Practices that invalidate or weaken native OpenHCS fluency evidence."""

    BYPASS_DSL = ("bypass_dsl", 1.0, True)
    DIRECT_VIEWER_AUTOMATION = ("direct_viewer_automation", 0.25, False)
    UNTYPED_BOUNDARY = ("untyped_boundary", 0.25, False)
    DUPLICATED_METADATA = ("duplicated_metadata", 0.25, False)
    EXTERNAL_PREPROCESSING = ("external_preprocessing", 1.0, True)
    UNREGISTERED_CALLABLE = ("unregistered_callable", 1.0, True)

    def __new__(
        cls,
        value: str,
        penalty: float,
        disqualifying: bool,
    ) -> "ArchitectureViolation":
        member = object.__new__(cls)
        member._value_ = value
        member.penalty = penalty
        member.disqualifying = disqualifying
        return member


class AttemptPhase(Enum):
    """Monotonic lifecycle for one agent-authored candidate."""

    AUTHORED = "authored"
    COMPILED = "compiled"
    EXECUTED = "executed"
    REVIEWED = "reviewed"
    FROZEN = "frozen"
    SCORED = "scored"


class ViewKind(Enum):
    """Required visual evidence families."""

    RAW = "raw"
    NORMALIZED = "normalized"
    MASK = "mask"
    ROI = "roi"
    MEASUREMENT = "measurement"
    OVERLAY = "overlay"


@dataclass(frozen=True, slots=True)
class UpstreamTaskSource:
    """Pinned upstream task identity and licence evidence."""

    repository_url: str
    commit: str
    notebook_path: Path
    notebook_sha256: str
    check_source_sha256: str
    licence: str


@dataclass(frozen=True, slots=True)
class TaskInput:
    """One named source plane in a hidden scoring case."""

    name: str
    array: np.ndarray
    channel: int = 1
    z_index: int = 1
    stack_axis: int | None = None


@dataclass(frozen=True, slots=True)
class ScoringCase:
    """Held-out inputs and expected result owned by one task declaration."""

    case_id: str
    inputs: tuple[TaskInput, ...]
    expected: ExpectedValue
    parameters: tuple[tuple[str, TaskParameterValue], ...] = ()


@dataclass(frozen=True, slots=True)
class SemanticChange:
    """One declared change between adjacent diagnostic attempts."""

    authority: str
    field_path: str
    before: str
    after: str
    hypothesis: str


@dataclass(frozen=True, slots=True)
class PercentileWindow:
    """Declared display percentile pair and its computed intensity bounds."""

    percentile_low: float
    percentile_high: float
    intensity_low: float
    intensity_high: float


@dataclass(frozen=True, slots=True)
class ValidationView:
    """One evidence view at a reproducible native-data coordinate."""

    kind: ViewKind
    artifact_path: Path
    coordinate: tuple[int, ...]
    crop_shape: tuple[int, ...]
    display_window: PercentileWindow | None = None


@dataclass(frozen=True, slots=True)
class RuntimeObservation:
    """Measured execution cost for one bounded attempt."""

    elapsed_seconds: float
    peak_rss_bytes: int


@dataclass(frozen=True, slots=True)
class DslEvidenceArtifact:
    """MCP/UI/runtime evidence for one OpenHCS semantic obligation."""

    requirement: DslRequirement
    artifact_path: Path
    explanation: str


@dataclass(frozen=True, slots=True)
class AttemptRecord:
    """Evidence required from one diagnose-edit-rerun cycle."""

    attempt_id: str
    task_id: str
    phase: AttemptPhase
    pipeline_sha256: str
    output_paths: tuple[Path, ...]
    views: tuple[ValidationView, ...]
    diagnostic_checks: frozenset[DiagnosticCheck]
    dsl_evidence: tuple[DslEvidenceArtifact, ...]
    architecture_violations: frozenset[ArchitectureViolation]
    runtime: RuntimeObservation | None
    change: SemanticChange | None = None


@dataclass(frozen=True, slots=True)
class TaskAuthoringSpec:
    """Answer-free task information safe to expose to an authoring agent."""

    task_id: str
    prompt: str
    evidence_class: EvidenceClass
    output_kind: OutputKind
    function_availability: FunctionAvailabilityExpectation
    source: UpstreamTaskSource
    required_diagnostics: tuple[DiagnosticCheck, ...]
    required_dsl: tuple[DslRequirement, ...]
    required_views: tuple[ViewKind, ...]
    dsl_instruction: str
    input_root: Path


@dataclass(frozen=True, slots=True)
class InputFileRecord:
    """One materialized source file in an answer-free bundle."""

    input_name: str
    channel: int
    z_index: int
    path: Path
    sha256: str


@dataclass(frozen=True, slots=True)
class TaskParameterRecord:
    """One public callable parameter supplied to a scoring case."""

    name: str
    value: TaskParameterValue


@dataclass(frozen=True, slots=True)
class TaskCaseRecord:
    """Answer-free mapping from a case identity to its source planes."""

    case_id: str
    site: int
    files: tuple[InputFileRecord, ...]
    parameters: tuple[TaskParameterRecord, ...]


@dataclass(frozen=True, slots=True)
class TaskBundleRecord:
    """Public task projection written for an authoring agent."""

    spec: TaskAuthoringSpec
    cases: tuple[TaskCaseRecord, ...]


@dataclass(frozen=True, slots=True)
class CorpusBundleRecord:
    """Top-level blind authoring bundle identity."""

    task_ids: tuple[str, ...]
    answer_material_included: bool = False
    freeze_required_before_scoring: bool = True


@dataclass(frozen=True, slots=True)
class DiagnosticChallengeRecord:
    """Public projection of one opaque, intentionally flawed candidate."""

    probe_id: str
    task_id: str
    prompt: str
    candidate_path: Path
    cases: tuple[TaskCaseRecord, ...]
    required_action: str
    expected_failure_hidden: bool = True


@dataclass(frozen=True, slots=True)
class DiagnosticCorpusRecord:
    """Top-level diagnostic probe bundle identity."""

    probe_ids: tuple[str, ...]
    failure_labels_included: bool = False


@dataclass(frozen=True, slots=True)
class AssertionResult:
    """Outcome of one upstream-equivalent held-out assertion."""

    name: str
    passed: bool
    detail: str


@dataclass(frozen=True, slots=True)
class TaskScore:
    """Separated result, diagnostic, and OpenHCS-fluency scores."""

    task_id: str
    assertions: tuple[AssertionResult, ...]
    diagnostic_fraction: float
    dsl_fraction: float
    architecture_violations: tuple[ArchitectureViolation, ...]
    lifecycle_passed: bool

    @property
    def result_parity_passed(self) -> bool:
        return bool(self.assertions) and all(item.passed for item in self.assertions)
