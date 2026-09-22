"""Typed semantic gates and evidence policy for image-analysis repair."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Self


class ImageQaMeasure(Enum):
    """Measurements used to distinguish admission, continuity, and ownership."""

    OBJECT_COUNT = "admitted-object count"
    OBJECT_AREA_DISTRIBUTION = "per-object area distribution"
    FOREGROUND_FRACTION = "accepted foreground fraction"
    SOURCE_TARGET_MATCH_COUNT = "accepted source-to-target match count"
    SOURCE_TARGET_CONTAINMENT_VIOLATION_PIXELS = (
        "source-label pixels outside the same-identity target object"
    )
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
    CANDIDATE_TRACE_PIXELS = "candidate-skeleton pixels"
    ROOTED_CANDIDATE_YIELD = "candidate-skeleton fraction retained as rooted"
    TOTAL_TRACE_PIXELS = "total trace pixels"
    ROOTED_TRACE_PIXELS = "root-connected trace pixels"
    UNROOTED_TRACE_PIXELS = "unrooted trace pixels"
    INITIAL_TOPOLOGY_OWNED_TRACE_PIXELS = (
        "initial-topology owned trace pixels"
    )
    SECONDARY_ADOPTED_TRACE_PIXELS = (
        "trace pixels after secondary-owner adoption"
    )
    SIGNAL_REPAIRED_TRACE_PIXELS = (
        "trace pixels after signal-supported soma repair"
    )
    CROSSING_CORE_TRACE_PIXELS = (
        "shared crossing-core trace pixels"
    )
    FINAL_TOPOLOGY_DROPPED_TRACE_PIXELS = (
        "owned trace pixels dropped by final topology"
    )
    FINAL_TOPOLOGY_DROPPED_CROSSING_SUPPORT_TRACE_PIXELS = (
        "dropped crossing-support trace pixels"
    )
    FINAL_TOPOLOGY_DROPPED_UNROOTED_PATH_TRACE_PIXELS = (
        "dropped graph-path pixels rejected as unrooted"
    )
    FINAL_TOPOLOGY_DROPPED_PHYSICALLY_ROOTED_PATH_TRACE_PIXELS = (
        "physically soma-rooted dropped path pixels"
    )
    FINAL_TOPOLOGY_DROPPED_PHYSICALLY_UNROOTED_PATH_TRACE_PIXELS = (
        "physically soma-detached dropped path pixels"
    )
    FINAL_TOPOLOGY_DROPPED_UNREPRESENTED_TRACE_PIXELS = (
        "dropped trace pixels absent from final path graph"
    )
    FINAL_TOPOLOGY_ADDED_TRACE_PIXELS = (
        "final-topology added shared-core pixels"
    )
    FINAL_TOPOLOGY_OWNED_TRACE_PIXELS = (
        "final-topology owned trace pixels"
    )
    PUBLISHED_OWNED_TRACE_PIXELS = (
        "published single-owner trace pixels"
    )
    OWNERSHIP_SUPPORTED_UNROOTED_TRACE_PIXELS = (
        "unrooted trace pixels inside a declared owner region"
    )
    OWNERSHIP_UNSUPPORTED_UNROOTED_TRACE_PIXELS = (
        "unrooted trace pixels outside every declared owner region"
    )
    OWNERSHIP_SUPPORTED_RESIDUAL_PIXELS = (
        "residual candidate pixels inside a declared owner region"
    )
    OWNERSHIP_UNSUPPORTED_RESIDUAL_PIXELS = (
        "residual candidate pixels outside every declared owner region"
    )
    OWNERSHIP_CROSSOVER_COMPONENTS = "components touching multiple owners"
    CANDIDATE_COMPONENT_OWNER_CARDINALITY = (
        "number of owner identities touching each candidate component"
    )
    LOCAL_BACKGROUND_SUPPORT = "new-pixel support above local background"
    TOPOLOGY_PLAUSIBILITY = "topology plausibility"


class ImageQaPrecondition(Enum):
    """Evidence required before a reported miss can justify parameter tuning."""

    RAW_BIOLOGICAL_CONTRACT = (
        "record stain targets; inspect every raw channel at identical native "
        "coordinates under full, moderate, and dim windows, then the composite; freeze "
        "a raw-only ledger of plausible objects, processes, ambiguities, and debris. "
        "DAPI supports a nuclear anchor, broader colocalised process-channel signal a "
        "soma, and thin continuous signal from that soma a neurite; brightness, labels, "
        "or proximity alone prove none, and nucleus count is not cell count. Before "
        "splitting a lobed nucleus, inspect a less-saturated window and require multiple "
        "independently supported nuclear intensity centres; outline shape alone does not "
        "prove multiple nuclei"
    )
    EARLIEST_FAILED_DEPENDENCY = (
        "review nuclear anchors, somata, candidates, rooted paths, and ownership in "
        "dependency order; stop downstream tuning at the earliest failure. If final "
        "masks cannot distinguish response, threshold, split, or size rejection, expose "
        "typed intermediates before changing parameters. Seed hysteresis can discard a "
        "dim component despite local response; compare pre/post-seed candidates first. "
        "Disabling it is a diagnostic ablation, not acceptance: require rooted recovery "
        "without added background at the same coordinates"
    )
    VALIDATION_EXPOSURE = (
        "record which fields informed pipeline or parameter decisions; a field "
        "used for tuning is development evidence even if its directory says "
        "held-out. Preserve treatment blinding separately from the development "
        "split; select an untouched validation reserve before freezing, or report "
        "that only development validation is available"
    )
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
    SOURCE_LAYOUT_SPLIT_REPRESENTATIVENESS = (
        "before public authoring, derive source carrier, rank, dtype, and channel-axis "
        "contract classes for development and held-out inputs without opening hidden "
        "labels or scoring references; require every held-out layout class to be "
        "represented in development or declared unsupported before pipeline freeze"
    )
    MIXED_COLOR_CARRIER_NORMALIZATION = (
        "when one biological plane may arrive in either grayscale or RGB containers, "
        "declare NamedSourceBinding(load_as_monochrome=True) at the source boundary; "
        "do not apply unconditional color_to_gray downstream"
    )
    EXHAUSTIVE_SOURCE_CARRIER_INVENTORY = (
        "inventory every selected source through its registered image-file header "
        "semantics before authoring or execution; report distinct declared carrier "
        "classes and refuse unknown or unreadable headers rather than sampling files "
        "or inferring layout from array rank"
    )


class ImageQaEvidenceRule(Enum):
    """Auditable evidence rules applied before accepting image-analysis QA."""

    ROUTED_PAYLOAD_PERCENTILES = (
        "derive live-view percentile limits from real routed payload values at the "
        "selected semantic coordinates, excluding sparse display padding"
    )
    MULTIPLE_WINDOWS = (
        "inspect the same source coordinates under multiple declared weak and strong "
        "percentile windows"
    )
    FIXED_COORDINATE_MULTI_WINDOW = (
        "preserve each percentile pair with its applied numeric limits while keeping "
        "raw/result coordinates, crop, scale, and overlay identical"
    )
    ROUTE_LOCAL_VIEWER_IDENTITY = (
        "aggregate viewer indices are not necessarily a route-local semantic "
        "coordinate because routes can have distinct component domains and axis "
        "offsets; derive navigation from the target route's typed component values "
        "and positional indices, then re-read viewer state"
    )
    REJECT_INVALID_CAPTURE = (
        "reject a black, empty, stale, or mismatched capture when its active route, "
        "component values, or routed payload identity do not match the intended evidence"
    )
    SPARSE_DIAGNOSTIC_LOCALIZATION = (
        "for a sparse diagnostic mask, use its viewer-reported exact nonzero bounds "
        "and bounded example coordinates to navigate to evidence before judging a "
        "full-field capture where one-pixel structures may be subpixel"
    )
    DURABLE_ARTIFACT_EXISTENCE = (
        "before freezing, verify every claimed durable label or measurement path exists "
        "and preserves the typed artifact identity rather than inferring persistence "
        "from a streamed viewer payload"
    )
    LABEL_CARDINALITY_AND_CONTAINMENT = (
        "reconcile source and target label cardinality, same-identity containment, "
        "foreground fraction, and per-object area distributions; equal counts alone "
        "do not establish spatial concordance"
    )
    FINAL_TOPOLOGY_REWRITE_ACCOUNTING = (
        "when final topology both removes and introduces trace pixels, compare the "
        "dropped mask, added mask, shared crossing-core mask, and owner identities at "
        "the same raw coordinates; net pixel-count change is not evidence of pruning"
    )
    ROUND_OBJECT_SOURCE_LINEAGE = (
        "for apparent nuclear over-segmentation, compare raw stain with "
        "round_object_prefilter, round_object_accepted, "
        "round_object_weak_core_candidates, "
        "round_object_adjacent_satellite_candidates, and round_object_widths at "
        "fixed coordinates. Use source_component_label and "
        "source_component_output_count to distinguish a separate threshold-stage "
        "component from a watershed split. Never globally reject weak-core objects: "
        "reject only an adjacent weak fragment while preserving isolated faint objects "
        "and multi-centre controls"
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
    ONE_PARAMETER_PER_ATTEMPT = "change one transform parameter per diagnostic attempt"
    SAME_COORDINATE_DELTA = (
        "compare added and removed rooted paths at identical source coordinates"
    )
    ROOTED_RECOVERY = "require recovered signal-supported rooted continuity rather than aggregate growth"
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
            ImageQaMeasure.OBJECT_AREA_DISTRIBUTION,
            ImageQaMeasure.FOREGROUND_FRACTION,
            ImageQaMeasure.SOURCE_TARGET_MATCH_COUNT,
            ImageQaMeasure.SOURCE_TARGET_CONTAINMENT_VIOLATION_PIXELS,
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
            ImageQaMeasure.INITIAL_TOPOLOGY_OWNED_TRACE_PIXELS,
            ImageQaMeasure.SECONDARY_ADOPTED_TRACE_PIXELS,
            ImageQaMeasure.SIGNAL_REPAIRED_TRACE_PIXELS,
            ImageQaMeasure.CROSSING_CORE_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_DROPPED_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_DROPPED_CROSSING_SUPPORT_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_DROPPED_UNROOTED_PATH_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_DROPPED_PHYSICALLY_ROOTED_PATH_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_DROPPED_PHYSICALLY_UNROOTED_PATH_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_DROPPED_UNREPRESENTED_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_ADDED_TRACE_PIXELS,
            ImageQaMeasure.FINAL_TOPOLOGY_OWNED_TRACE_PIXELS,
            ImageQaMeasure.PUBLISHED_OWNED_TRACE_PIXELS,
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
            ImageQaMeasure.OWNERSHIP_SUPPORTED_UNROOTED_TRACE_PIXELS,
            ImageQaMeasure.OWNERSHIP_UNSUPPORTED_UNROOTED_TRACE_PIXELS,
            ImageQaMeasure.OWNERSHIP_SUPPORTED_RESIDUAL_PIXELS,
            ImageQaMeasure.OWNERSHIP_UNSUPPORTED_RESIDUAL_PIXELS,
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
        evidence_rule_text = "; ".join(rule.value for rule in ImageQaEvidenceRule)
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
            f"Preconditions—{precondition_text}. Evidence—{evidence_rule_text}. "
            f"References—{reference_evidence_text}. Seeds—{seeded_segmentation_text}. "
            f"Stages—{miss_stage_text}. Gates/measures—{gate_text}. Reasons—"
            f"{rejection_reasons}. Residuals—{residual_dispositions}. Change one gate "
            "per attempt. Keep a fixed-coordinate four-panel "
            "view: raw, candidate, rooted, and candidate-only residual. Rank nuclei "
            "without a nearby accepted soma by same-coordinate body-channel support; "
            "test source admission and target-body response as separate attempts without "
            "splitting an already admitted source. A stricter threshold can split a "
            "merged object. Inspect source (for example DAPI), target, response, "
            "accepted-label overlay, bodies, and traces. For one higher-sensitivity "
            "diagnostic attempt, subtract the accepted candidate mask and treat gains as "
            "diagnostic evidence rather than an automatic replacement. Report stage "
            "counts and owner cardinality per connected component. Multi-owner loss is "
            "ownership failure; lowering the detection threshold cannot repair it. "
            "If permissiveness harms a reference, declare the permissive value only on "
            "the dataset or preset that needs it. Thin-structure continuation must be "
            f"{continuation_constraint_text}; distance, ownership, and response alone "
            "are insufficient. For monotone, ridge, or contrast preprocessing require "
            f"{signal_transform_constraint_text}. Aggregate length or object-count "
            "agreement alone cannot accept it. Preserve rejected parameter changes."
        )
