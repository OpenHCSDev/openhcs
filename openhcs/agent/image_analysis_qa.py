"""Typed semantic gates and evidence policy for image-analysis repair."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Self


class ImageQaMeasure(Enum):
    """Measurements used to distinguish admission, continuity, and ownership."""

    OBJECT_COUNT = "admitted-object count"
    SOURCE_TARGET_MATCH_COUNT = "accepted source-to-target match count"
    ADMISSION_DELTA_OBJECTS = (
        "source objects added or removed by an adjacent admission setting"
    )
    REFERENCE_OBJECT_COUNT_DELTA = "detected-versus-reference object-count delta"
    PER_OBJECT_REFERENCE_DELTA = "spatially matched per-object measurement delta"
    ACCEPTED_BODY_PIXELS = "accepted body pixels"
    REJECTED_CANDIDATE_COUNT = "rejected source-candidate count"
    REJECTED_CANDIDATE_SIGNAL_SUPPORT = (
        "nearby signal support for each rejected source candidate"
    )
    REJECTION_REASON_DISTRIBUTION = "rejection-reason distribution"
    RESIDUAL_STRUCTURE_COUNT = "signal-supported residual-structure count"
    RESIDUAL_STRUCTURE_SIGNAL_SUPPORT = (
        "local signal support for unowned or unrooted residual structures"
    )
    RESIDUAL_STRUCTURE_DISPOSITION = "residual-structure disposition distribution"
    SENSITIVITY_DELTA_COMPONENTS = (
        "connected components added by an adjacent sensitivity setting"
    )
    SENSITIVITY_DELTA_ROOTED_YIELD = (
        "root-connected continuity recovered by the sensitivity delta"
    )
    SENSITIVITY_DELTA_BACKGROUND_GROWTH = (
        "unsupported background growth in the sensitivity delta"
    )
    CANDIDATE_TRACE_PIXELS = "current candidate-skeleton pixels"
    ROOTED_CANDIDATE_YIELD = "fraction of candidate-skeleton pixels retained as rooted"
    TOTAL_TRACE_PIXELS = "total trace pixels"
    ROOTED_TRACE_PIXELS = "root-connected trace pixels"
    UNROOTED_TRACE_PIXELS = "unrooted trace pixels"
    OWNERSHIP_CROSSOVER_COMPONENTS = "components touching multiple owners"
    CANDIDATE_COMPONENT_OWNER_CARDINALITY = (
        "number of owner identities touching each candidate component"
    )
    LOCAL_BACKGROUND_SUPPORT = "new-pixel support above local background"
    TOPOLOGY_PLAUSIBILITY = "topology plausibility"


class ImageQaPrecondition(Enum):
    """Evidence required before a reported miss can justify parameter tuning."""

    CURRENT_OUTPUT_CONCORDANCE = (
        "localize the reported view to source coordinates and reproduce it from "
        "the current raw and output artifacts"
    )
    IDENTICAL_COORDINATES = (
        "compare raw, source, candidate, rooted, and owner views at identical "
        "coordinates"
    )
    NESTED_MASK_STAGE_ATTRIBUTION = (
        "attribute the miss with nested masks before changing a semantic gate"
    )
    FIXED_COORDINATE_STAGE_MONTAGE = (
        "render raw signal, candidate skeleton, rooted result, and candidate-only "
        "residual side by side at fixed coordinates"
    )
    DECLARATION_SCOPE = (
        "apply dataset-specific sensitivity through the pipeline declaration, "
        "not by changing the shared engine default"
    )
    SOURCE_LAYOUT_CONTRACT = (
        "verify that the routed source rank and channel-axis semantics satisfy the "
        "declared callable contract; when a color axis is not a biological plane "
        "axis, collapse it explicitly with a registered typed transform before "
        "segmentation"
    )
    VIEWER_FILE_AXIS_PROJECTION = (
        "when streaming an existing image file for QA, derive color-channel semantics "
        "from the physical container before viewer dispatch and refuse undeclared "
        "non-spatial axes; never infer a biological plane axis from array rank"
    )


class ImageQaVisualizationRule(Enum):
    """Rules for trustworthy live and materialized image inspection."""

    ROUTED_PAYLOAD_PERCENTILES = (
        "derive live-view percentile limits from real routed payload values at the "
        "selected semantic coordinates, excluding sparse display padding"
    )
    MULTIPLE_WINDOWS = (
        "inspect the same source coordinates under multiple declared weak and strong "
        "percentile windows"
    )


class ReferenceEvidenceRule(Enum):
    """How external references constrain, but do not replace, spatial QA."""

    COUNT_CONSTRAINS_ADMISSION = (
        "compare detected and reference object counts before changing object admission"
    )
    COUNT_DOES_NOT_PROVE_IDENTITY = (
        "treat count agreement as an admission constraint, not proof that the same "
        "objects were detected"
    )
    IDENTITY_REQUIRES_SPATIAL_CORRESPONDENCE = (
        "require coordinates, labels, or annotations before claiming object identity"
    )
    AGGREGATE_DOES_NOT_PROVE_PER_OBJECT_COMPLETENESS = (
        "treat aggregate measurement agreement as insufficient evidence of per-object "
        "trace completeness"
    )
    VALUE_ONLY_ASSIGNMENT_IS_DIAGNOSTIC = (
        "use value-only object assignment to prioritise review, never to establish "
        "spatial identity"
    )


class SeededSegmentationRule(Enum):
    """Identity evidence for primary-seed to secondary-object segmentation."""

    LABEL_ID_BIJECTION = (
        "require the primary-seed and secondary-object label-ID sets to be identical; "
        "equal object counts alone do not prove seed identity conservation"
    )
    SAME_ID_CONTAINMENT = (
        "verify that every primary-seed pixel lies inside the secondary mask carrying "
        "the same label ID"
    )


class ImageQaMissStage(Enum):
    """Stage attribution derived from nested current-output masks."""

    OBJECT_ADMISSION = "no accepted source object or body"
    CANDIDATE_DETECTION = "present only in the permissive candidate mask"
    ROOTED_CONNECTIVITY = (
        "present in the current candidate mask but not the rooted result"
    )
    OWNERSHIP = "present in the rooted result with an evidenced identity discontinuity"


class ThinStructureContinuationConstraint(Enum):
    """Evidence required before extending a rooted thin structure."""

    TERMINAL_DIRECTION = "aligned with the existing terminal direction"
    BODY_EXCLUSION = "outside the accepted source-object or body neighborhood"
    LOCAL_SIGNAL_SUPPORT = "supported by the declared local-response gate"
    BOUNDED_GAP = "bounded by a declared physical-width-derived gap"
    OWNER_CONSISTENCY = "contained within one owner region without a foreign crossing"


class SignalTransformConstraint(Enum):
    """Evidence required when preprocessing is used to reveal faint signal."""

    TARGET_CHANNEL_ONLY = "transform only the declared target or process channel"
    REFERENCE_CHANNEL_IDENTITY = (
        "prove that source, nuclear, and other reference channels remain unchanged"
    )
    ONE_PARAMETER_PER_ATTEMPT = (
        "change one transform parameter per diagnostic attempt"
    )
    SAME_COORDINATE_DELTA = (
        "compare added and removed rooted paths at identical source coordinates"
    )
    ROOTED_RECOVERY = (
        "require recovered signal-supported rooted continuity rather than aggregate growth"
    )
    FRAGMENTATION_CONTROL = (
        "reject gains accompanied by unsupported background or topology fragmentation"
    )


class SemanticGate(Enum):
    """Independent semantic gates changed by one diagnostic experiment."""

    _description: str
    _measures: tuple[ImageQaMeasure, ...]

    OBJECT_ADMISSION = (
        "object_admission",
        "decides whether a source object enters the analysis",
        (
            ImageQaMeasure.OBJECT_COUNT,
            ImageQaMeasure.SOURCE_TARGET_MATCH_COUNT,
            ImageQaMeasure.ADMISSION_DELTA_OBJECTS,
            ImageQaMeasure.REFERENCE_OBJECT_COUNT_DELTA,
            ImageQaMeasure.ACCEPTED_BODY_PIXELS,
            ImageQaMeasure.REJECTED_CANDIDATE_COUNT,
            ImageQaMeasure.REJECTED_CANDIDATE_SIGNAL_SUPPORT,
            ImageQaMeasure.REJECTION_REASON_DISTRIBUTION,
        ),
    )
    PATH_CONTINUITY = (
        "path_continuity",
        "decides how much signal remains connected to an admitted root",
        (
            ImageQaMeasure.CANDIDATE_TRACE_PIXELS,
            ImageQaMeasure.ROOTED_CANDIDATE_YIELD,
            ImageQaMeasure.TOTAL_TRACE_PIXELS,
            ImageQaMeasure.ROOTED_TRACE_PIXELS,
            ImageQaMeasure.UNROOTED_TRACE_PIXELS,
            ImageQaMeasure.RESIDUAL_STRUCTURE_COUNT,
            ImageQaMeasure.RESIDUAL_STRUCTURE_SIGNAL_SUPPORT,
            ImageQaMeasure.RESIDUAL_STRUCTURE_DISPOSITION,
            ImageQaMeasure.SENSITIVITY_DELTA_COMPONENTS,
            ImageQaMeasure.SENSITIVITY_DELTA_ROOTED_YIELD,
            ImageQaMeasure.SENSITIVITY_DELTA_BACKGROUND_GROWTH,
            ImageQaMeasure.LOCAL_BACKGROUND_SUPPORT,
            ImageQaMeasure.TOPOLOGY_PLAUSIBILITY,
            ImageQaMeasure.PER_OBJECT_REFERENCE_DELTA,
        ),
    )
    OWNERSHIP = (
        "ownership",
        "decides which admitted root owns a path through crossings",
        (
            ImageQaMeasure.OWNERSHIP_CROSSOVER_COMPONENTS,
            ImageQaMeasure.CANDIDATE_COMPONENT_OWNER_CARDINALITY,
            ImageQaMeasure.TOPOLOGY_PLAUSIBILITY,
        ),
    )

    def __new__(
        cls,
        value: str,
        description: str,
        measures: tuple[ImageQaMeasure, ...],
    ) -> Self:
        member = object.__new__(cls)
        member._value_ = value
        member._description = description
        member._measures = measures
        return member

    @property
    def description(self) -> str:
        return self._description

    @property
    def measures(self) -> tuple[ImageQaMeasure, ...]:
        return self._measures


@dataclass(frozen=True, slots=True)
class RootedContinuityObservation:
    """Admission and rooted-path evidence for one candidate."""

    object_count: int
    accepted_body_pixels: int
    total_trace_pixels: int
    rooted_trace_pixels: int
    unrooted_trace_pixels: int
    ownership_crossover_components: int

    def accepts_growth_from(self, previous: RootedContinuityObservation) -> bool:
        """Reject trace growth that adds no root-connected continuity."""

        added_trace = self.total_trace_pixels > previous.total_trace_pixels
        improved_rooted_trace = self.rooted_trace_pixels > previous.rooted_trace_pixels
        return not added_trace or improved_rooted_trace


class CandidateRejectionReason(Enum):
    """Declared biological-candidate gates used during admission review."""

    AREA = "area"
    WIDTH = "width"
    RESPONSE = "response"
    CONNECTIVITY = "connectivity"
    BORDER = "border"
    DEBRIS = "debris"
    ALREADY_OWNED = "already_owned"
    UNCLASSIFIED = "unclassified"


@dataclass(frozen=True, slots=True)
class RejectedCandidateObservation:
    """One source candidate rejected before entering the accepted mask."""

    source_id: int
    coordinate: tuple[int, ...]
    nearby_signal_support: float
    reason: CandidateRejectionReason

    @classmethod
    def rank_by_signal_support(
        cls,
        candidates: tuple[RejectedCandidateObservation, ...],
    ) -> tuple[RejectedCandidateObservation, ...]:
        """Place the strongest locally supported rejected candidates first."""

        return tuple(
            sorted(
                candidates,
                key=lambda candidate: (
                    -candidate.nearby_signal_support,
                    candidate.source_id,
                ),
            )
        )


class ResidualStructureDisposition(Enum):
    """Declared explanations for signal-supported residual structures."""

    UNOWNED = "unowned"
    UNROOTED = "unrooted"
    ALREADY_OWNED = "already_owned"
    BORDER = "border"
    DEBRIS = "debris"


@dataclass(frozen=True, slots=True)
class ResidualStructureObservation:
    """One signal-supported structure outside accepted rooted ownership."""

    structure_id: int
    coordinate: tuple[int, ...]
    local_signal_support: float
    disposition: ResidualStructureDisposition
    topology_plausible: bool

    @classmethod
    def rank_by_signal_support(
        cls,
        structures: tuple[ResidualStructureObservation, ...],
    ) -> tuple[ResidualStructureObservation, ...]:
        """Place the strongest unresolved structures first."""

        return tuple(
            sorted(
                structures,
                key=lambda structure: (
                    -structure.local_signal_support,
                    structure.structure_id,
                ),
            )
        )


class ImageAnalysisQaPolicy:
    """Canonical text projection of typed diagnostic-gate declarations."""

    @classmethod
    def repair_guidance(cls) -> str:
        precondition_text = "; ".join(
            precondition.value for precondition in ImageQaPrecondition
        )
        miss_stage_text = "; ".join(
            f"{stage.name.lower()} means {stage.value}" for stage in ImageQaMissStage
        )
        continuation_constraint_text = ", ".join(
            constraint.value for constraint in ThinStructureContinuationConstraint
        )
        signal_transform_constraint_text = ", ".join(
            constraint.value for constraint in SignalTransformConstraint
        )
        reference_evidence_text = "; ".join(
            rule.value for rule in ReferenceEvidenceRule
        )
        seeded_segmentation_text = "; ".join(
            rule.value for rule in SeededSegmentationRule
        )
        visualization_rule_text = "; ".join(
            rule.value for rule in ImageQaVisualizationRule
        )
        gate_text = "; ".join(
            (
                f"{gate.value} {gate.description}; measure "
                + ", ".join(measure.value for measure in gate.measures)
            )
            for gate in SemanticGate
        )
        rejection_reasons = ", ".join(
            reason.value for reason in CandidateRejectionReason
        )
        residual_dispositions = ", ".join(
            disposition.value for disposition in ResidualStructureDisposition
        )
        return (
            f"Before tuning, require that each precondition holds: {precondition_text}. "
            f"For visual inspection: {visualization_rule_text}. "
            f"When a reference exists: {reference_evidence_text}. "
            f"For seeded secondary segmentation: {seeded_segmentation_text}. "
            "Classify the current-output "
            f"miss by stage: {miss_stage_text}. Then classify each residual miss: "
            f"{gate_text}. Sweep exactly one declaration-owned gate per attempt. "
            "Compare revisions at identical coordinates under declared weak and "
            "strong percentile windows. Inspect missed source objects (including "
            "somata when they are the admitted roots) and faint processes without "
            "reclassifying amplified background as biology. "
            "For every thin-structure miss, preserve a fixed-coordinate four-panel "
            "view of raw signal, candidate skeleton, rooted result, and candidate-only "
            "residual; this separates detection failure from post-detection loss. "
            "For source-assisted admission, enumerate source objects not mapped to "
            "accepted bodies (for example nuclei without a nearby accepted soma) "
            "and rank same-coordinate crops by nearby body-channel response/support. "
            "When a source object or body appears missing, sweep source admission and "
            "target-body response as separate attempts. Compare the source-object, "
            "accepted-body, and source-to-target match counts at identical coordinates; "
            "an added source object is a supported recovery only when it maps to a "
            "plausible target body rather than splitting an already admitted source. "
            "Do not assume an admission threshold is monotone after object partitioning: "
            "a stricter threshold can split a merged object and a permissive threshold "
            "can merge neighbors, so inspect the spatial added/removed mask and source-to-"
            "target matches for every threshold delta. "
            "Inspect the source channel (for example DAPI), target or process channel "
            "(for example FITC), response image, accepted-label overlay, bodies, and "
            "traces under the same multiple percentile windows; record the rejection "
            f"reason ({rejection_reasons}) for every candidate. Rank signal-supported "
            "residual processes that remain unowned or unrooted and classify each as "
            f"{residual_dispositions}. Change only the implicated admission, path, or "
            "ownership criterion. When a miss remains unexplained, make one adjacent "
            "higher-sensitivity diagnostic attempt, subtract the accepted candidate "
            "mask from the permissive mask, split the delta into connected components, "
            "and rank those additions by raw-signal support and connection to a valid "
            "source object. Treat the permissive result as diagnostic evidence rather "
            "than an automatic replacement. Accept a recovery only when local signal "
            "support, "
            "connectivity, and topology evidence agree. "
            "When signal is present in the current candidate skeleton but absent from the "
            "rooted result, report candidate pixels, rooted-candidate yield, and owner "
            "cardinality per connected component. A loss concentrated in components that "
            "touch multiple owners implicates ownership or crossover resolution; lowering "
            "the detection threshold cannot repair it. "
            "If a permissive setting helps the target dataset but fragments a reference "
            "image or adds unsupported structure, keep the conservative shared default "
            "and declare the permissive value only on the dataset or preset that needs it. "
            "For thin-structure endpoint continuation, require every proposed path "
            f"to be {continuation_constraint_text}; distance, ownership, and response "
            "alone are insufficient because they can admit source-object-edge "
            "decorations. "
            "When faint signal motivates monotone, ridge, or contrast preprocessing, "
            f"require the transform to {signal_transform_constraint_text}. Aggregate "
            "length or object-count agreement alone cannot accept a transform. "
            "Reject mask growth that does not increase root-connected continuity, "
            "and preserve rejected parameter changes as well as accepted ones, with "
            "the recovered-candidate evidence for each decision."
        )
