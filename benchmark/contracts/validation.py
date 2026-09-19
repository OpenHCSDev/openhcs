"""Contracts for blinded, independent-reference image-analysis validation."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from enum import Enum
from pathlib import Path


class ValidationArtifactKind(Enum):
    """How one pinned validation source is materialized."""

    ZIP_ARCHIVE = "zip_archive"
    FILE = "file"


class ValidationArtifactRole(Enum):
    """Semantic role of one validation source artifact."""

    INPUT = "input"
    REFERENCE = "reference"
    METADATA = "metadata"
    REPRODUCTION = "reproduction"


class ValidationEvidenceKind(Enum):
    """Kind of independent evidence a dataset supplies."""

    INSTANCE_MASKS = "instance_masks"
    MANUAL_OUTLINES = "manual_outlines"
    PLATE_BIOLOGY = "plate_biology"


class ValidationDatasetLayout(Enum):
    """Registered source-layout strategy used to prepare a corpus."""

    PARTITIONED_INSTANCE_MASKS = "partitioned_instance_masks"
    PAIRED_MANUAL_OUTLINES = "paired_manual_outlines"
    TRANSLOCATION_PLATE = "translocation_plate"


class ValidationMetricProfile(Enum):
    """Registered scoring strategy applied after a pipeline is frozen."""

    INSTANCE_SEGMENTATION = "instance_segmentation"
    BOUNDARY_AND_INSTANCE = "boundary_and_instance"
    TRANSLOCATION_ASSAY = "translocation_assay"


class ValidationPartition(Enum):
    """Canonical partitions retained from upstream dataset declarations."""

    TRAINING = "training"
    VALIDATION = "validation"
    TEST = "test"
    COMPLETE = "complete"


class ValidationAssayRole(Enum):
    """Plate-well role used by biological assay scoring."""

    NEGATIVE_CONTROL = "negative_control"
    POSITIVE_CONTROL = "positive_control"
    DOSE = "dose"
    EMPTY = "empty"


class ValidationFunctionSurface(Enum):
    """Function surface an autonomous authoring trial is required to exercise."""

    CATALOG = "catalog"
    REGISTERED_CUSTOM = "registered_custom"


class ValidationSelectionOrder(Enum):
    """Deterministic ordering used to select development source sets."""

    LEXICOGRAPHIC = "lexicographic"
    SHA256 = "sha256"

    def key(self, selection_key: str, *, salt: str) -> str:
        """Return the stable sort key owned by this ordering declaration."""

        if self is ValidationSelectionOrder.LEXICOGRAPHIC:
            return selection_key
        if self is ValidationSelectionOrder.SHA256:
            return hashlib.sha256(f"{salt}:{selection_key}".encode()).hexdigest()
        raise AssertionError(f"Unsupported validation selection order: {self!r}")


@dataclass(frozen=True, slots=True)
class ValidationSourceSetSelection:
    """Declarative selection of source sets for one trial surface."""

    partitions: tuple[ValidationPartition, ...]
    include_selection_keys: tuple[str, ...] = ()
    limit: int | None = None
    order: ValidationSelectionOrder = ValidationSelectionOrder.LEXICOGRAPHIC
    salt: str = ""

    def __post_init__(self) -> None:
        if not self.partitions:
            raise ValueError("Validation source-set selection needs a partition.")
        if self.limit is not None and self.limit <= 0:
            raise ValueError("Validation source-set selection limit must be positive.")
        if len(self.include_selection_keys) != len(set(self.include_selection_keys)):
            raise ValueError("Validation selection keys must be unique.")
        if self.order is ValidationSelectionOrder.SHA256 and not self.salt:
            raise ValueError("SHA-256 validation selection requires a declared salt.")


@dataclass(frozen=True, slots=True)
class ValidationTrialSplit:
    """One provenance-bearing development/held-out split declaration."""

    development: ValidationSourceSetSelection
    held_out: ValidationSourceSetSelection
    expected_development_source_sets: int
    expected_held_out_source_sets: int

    def __post_init__(self) -> None:
        if self.expected_development_source_sets <= 0:
            raise ValueError("Expected development source-set count must be positive.")
        if self.expected_held_out_source_sets <= 0:
            raise ValueError("Expected held-out source-set count must be positive.")


@dataclass(frozen=True, slots=True)
class ValidationArtifactSpec:
    """Immutable, content-addressed upstream artifact declaration."""

    name: str
    url: str
    sha256: str
    size_bytes: int
    kind: ValidationArtifactKind
    role: ValidationArtifactRole

    def __post_init__(self) -> None:
        if not self.name or Path(self.name).name != self.name:
            raise ValueError("ValidationArtifactSpec.name must be one file name.")
        if not self.url.startswith(("https://", "http://")):
            raise ValueError("ValidationArtifactSpec.url must be HTTP(S).")
        normalized_digest = self.sha256.lower()
        if len(normalized_digest) != 64 or any(
            character not in "0123456789abcdef" for character in normalized_digest
        ):
            raise ValueError("ValidationArtifactSpec.sha256 must be a SHA-256 digest.")
        if self.size_bytes <= 0:
            raise ValueError("ValidationArtifactSpec.size_bytes must be positive.")
        object.__setattr__(self, "sha256", normalized_digest)


@dataclass(frozen=True, slots=True)
class ValidationChannelSpec:
    """One canonical source channel exposed to an authoring agent."""

    alias: str
    value: str

    def __post_init__(self) -> None:
        if not self.alias.strip() or not self.value.strip():
            raise ValueError("Validation channel alias and value cannot be empty.")
        if not self.alias.isidentifier():
            raise ValueError(
                "Validation channel alias must be a valid Python/MCP parameter name."
            )


@dataclass(frozen=True, slots=True)
class PublishedAssayReference:
    """Published plate-level result used as a biological reference, not pixel GT."""

    name: str
    value: float
    citation_url: str

    def __post_init__(self) -> None:
        if not self.name.strip() or not self.citation_url.startswith("https://"):
            raise ValueError("Published assay references require a name and HTTPS URL.")


@dataclass(frozen=True, slots=True)
class ValidationRepositorySource:
    """Pinned repository evidence accompanying a dataset declaration."""

    name: str
    url: str
    revision: str
    licence_name: str
    materialized_size_bytes: int
    paths: tuple[str, ...]

    def __post_init__(self) -> None:
        if len(self.revision) != 40 or any(
            character not in "0123456789abcdef" for character in self.revision.lower()
        ):
            raise ValueError("Validation repository revision must be a full Git SHA.")
        if self.materialized_size_bytes <= 0:
            raise ValueError("Repository materialized size must be positive.")
        if not self.paths:
            raise ValueError("Validation repository source paths cannot be empty.")


@dataclass(frozen=True, slots=True)
class ValidationAuthoringTrack:
    """One declared OpenHCS DSL authoring challenge over a validation dataset."""

    name: str
    function_surface: ValidationFunctionSurface
    objective: str
    expected_artifacts: tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.name.strip() or not self.objective.strip():
            raise ValueError(
                "Validation authoring track name/objective cannot be empty."
            )
        if not self.expected_artifacts:
            raise ValueError(
                "Validation authoring track must declare output artifacts."
            )


@dataclass(frozen=True, slots=True)
class IndependentValidationSpec:
    """Declaration-owned independent validation contract for one dataset."""

    record_url: str
    licence_name: str
    licence_url: str
    evidence_kind: ValidationEvidenceKind
    layout: ValidationDatasetLayout
    metric_profile: ValidationMetricProfile
    artifacts: tuple[ValidationArtifactSpec, ...]
    channels: tuple[ValidationChannelSpec, ...]
    expected_input_planes: int
    trial_split: ValidationTrialSplit
    source_identity_fields: tuple[str, ...] = ("well", "site")
    execution_group_fields: tuple[str, ...] = ("well",)
    reference_decoder_revision: str | None = None
    reference_decoder_url: str | None = None
    repository_sources: tuple[ValidationRepositorySource, ...] = ()
    published_assay_references: tuple[PublishedAssayReference, ...] = ()
    authoring_tracks: tuple[ValidationAuthoringTrack, ...] = ()

    def __post_init__(self) -> None:
        if self.expected_input_planes <= 0:
            raise ValueError("expected_input_planes must be positive.")
        if not self.artifacts:
            raise ValueError("IndependentValidationSpec.artifacts cannot be empty.")
        if not self.channels:
            raise ValueError("IndependentValidationSpec.channels cannot be empty.")
        if not self.authoring_tracks:
            raise ValueError(
                "IndependentValidationSpec.authoring_tracks cannot be empty."
            )
        if not self.source_identity_fields or not self.execution_group_fields:
            raise ValueError("Validation source/group identity fields cannot be empty.")
        if not set(self.execution_group_fields).issubset(self.source_identity_fields):
            raise ValueError("Execution group fields must belong to source identity.")
        if len(self.source_identity_fields) != len(set(self.source_identity_fields)):
            raise ValueError("Validation source identity fields must be unique.")
        names = tuple(artifact.name for artifact in self.artifacts)
        if len(names) != len(set(names)):
            raise ValueError("Validation artifact names must be unique.")
        aliases = tuple(channel.alias for channel in self.channels)
        values = tuple(channel.value for channel in self.channels)
        if len(aliases) != len(set(aliases)) or len(values) != len(set(values)):
            raise ValueError("Validation channel aliases and values must be unique.")
        if (self.reference_decoder_revision is None) != (
            self.reference_decoder_url is None
        ):
            raise ValueError(
                "Reference decoder URL and revision must be declared together."
            )
        reference_artifacts = self.artifacts_for(ValidationArtifactRole.REFERENCE)
        if self.evidence_kind is ValidationEvidenceKind.PLATE_BIOLOGY:
            if not self.published_assay_references:
                raise ValueError(
                    "Plate-biology validation requires published assay references."
                )
        elif not reference_artifacts:
            raise ValueError(
                "Pixel/object validation requires a declared reference artifact."
            )

    @property
    def acquisition_urls(self) -> tuple[str, ...]:
        """Return artifact URLs derived from this single declaration."""

        return tuple(artifact.url for artifact in self.artifacts)

    @property
    def acquisition_size_bytes(self) -> int:
        """Return exact total compressed/source byte count."""

        return sum(artifact.size_bytes for artifact in self.artifacts)

    @property
    def archive_size_bytes(self) -> int:
        """Return the bytes represented by the legacy archive URL projection."""

        return sum(
            artifact.size_bytes
            for artifact in self.artifacts
            if artifact.kind is ValidationArtifactKind.ZIP_ARCHIVE
        )

    def artifacts_for(
        self,
        role: ValidationArtifactRole,
    ) -> tuple[ValidationArtifactSpec, ...]:
        """Return source artifacts with one semantic role."""

        return tuple(artifact for artifact in self.artifacts if artifact.role is role)


@dataclass(frozen=True, slots=True)
class ValidationImageRecord:
    """One normalized authoring image plane derived from an upstream source."""

    source_relative_path: Path
    canonical_relative_path: Path
    source_set_id: str
    selection_key: str
    partition: ValidationPartition
    well: str
    site: str
    channel: str
    metadata: tuple[tuple[str, str], ...] = ()


@dataclass(frozen=True, slots=True)
class ValidationReferenceRecord:
    """One scoring-only reference associated with a normalized source set."""

    source_relative_path: Path
    canonical_relative_path: Path
    source_set_id: str
    reference_kind: ValidationEvidenceKind
    partition: ValidationPartition
    channel: str | None = None


@dataclass(frozen=True, slots=True)
class FrozenPipelineReceipt:
    """Hash-bound declaration proving the scored pipeline preceded reference access."""

    dataset_id: str
    pipeline_path: Path
    pipeline_sha256: str
    created_at_utc: str


@dataclass(frozen=True, slots=True)
class PreparedValidationCorpus:
    """Filesystem coordinates for separated authoring and trusted scoring surfaces."""

    dataset_id: str
    root: Path
    authoring_root: Path
    held_out_root: Path
    scoring_root: Path
    source_manifest_path: Path
    source_bindings_path: Path
    pipeline_template_path: Path
    provenance_path: Path
