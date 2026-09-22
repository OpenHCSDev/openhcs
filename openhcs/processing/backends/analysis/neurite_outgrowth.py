"""MetaXpress-style 2D neurite outgrowth analysis.

The public controls mirror the documented MetaXpress Neurite Outgrowth module.
The opinionated implementation composes the existing CellProfiler-compatible
segmentation leaves and measures the final soma-rooted neurite topology.
"""

import heapq
from collections import Counter, defaultdict
from dataclasses import dataclass
from enum import Enum
from itertools import combinations
from typing import Iterable, Mapping, Sequence

import numpy as np
from scipy import ndimage as ndi
from scipy.spatial import cKDTree
from skan import Skeleton, summarize
from skimage.graph import MCP_Geometric
from skimage.measure import regionprops
from skimage.segmentation import expand_labels

from openhcs.core.artifacts import (
    ArtifactMeasurementSubjectRelation,
    ArtifactSidecarRole,
    ArtifactSpec,
    ArtifactViewerStreaming,
    ImageArtifactType,
    MainFlowPlaneProjectionOutputSpec,
    MeasurementsArtifactType,
    ObjectArtifactMemberSubjectRelation,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
    SpatialGraphArtifactType,
)
from openhcs.core.callable_contract import CallableContract
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.memory import numpy
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.core.projected_image_output import SelectedPlaneImageOutput
from openhcs.core.runtime_image_values import image_payload_data
from openhcs.core.runtime_object_label_building import (
    SourceImageObjectLabelBuildRequest,
)
from openhcs.core.runtime_object_label_domains import (
    PresentObjectLabelIdsDomainDeclaration,
)
from openhcs.core.runtime_object_labels import (
    object_label_dense_array,
    object_label_value_with_dense_labels,
)
from openhcs.core.runtime_spatial_graph import (
    SpatialGraph,
    SpatialGraphEdge,
    SpatialGraphNode,
)
from openhcs.processing.materialization import (
    CsvOptions,
    ImageFileOptions,
    MaterializationSpec,
    MaterializedFilenameIdentity,
    ROIOptions,
    SpatialGraphROIOptions,
    SWCOptions,
)

from ..cellprofiler.feature_enhancement import (
    EnhanceMethod,
    NeuriteMethod,
    OperationMethod,
    enhance_or_suppress_features,
)
from ..cellprofiler.medial_axis import medialaxis
from ..cellprofiler.primary_objects import identify_primary_objects
from ..cellprofiler.secondary import (
    SecondaryMethod,
    identify_secondary_objects,
    secondary_propagation_backend,
)
from ..cellprofiler.thresholding import (
    CellProfilerThresholdMethod,
    CellProfilerThresholdScope,
    threshold,
)
from .count_cells_simple import (
    MetaXpressWavelengthSettings,
    segment_metaxpress_round_objects,
)
from .metaxpress_utils import HiddenPixelSize, local_background_response


class NeuriteIllumination(str, Enum):
    """Documented neurite-image illumination modes."""

    FLUORESCENCE = "fluorescence"
    TRANSMISSION = "transmission"


@dataclass(frozen=True)
class CellProfilerNeuriteEngineProfile:
    """Authoritative CP settings shared by compact and modular workflows."""

    body_min_diameter_px: int = 12
    compact_body_min_diameter_px: int = 10
    body_max_diameter_px: int = 100
    adaptive_window_size_px: int = 64
    tubeness_smoothing_px: float = 1.5
    neurite_candidate_threshold_correction_factor: float = 0.85
    secondary_ownership_threshold_correction_factor: float = 0.85
    threshold_smoothing_px: float = 1.0
    secondary_regularization_factor: float = 0.05

    def body_detection_kwargs(
        self,
        *,
        adaptive_window_size: int | None = None,
        exclude_size: bool = True,
        min_diameter: int | None = None,
    ) -> dict[str, object]:
        return {
            "min_diameter": (
                self.body_min_diameter_px if min_diameter is None else min_diameter
            ),
            "max_diameter": self.body_max_diameter_px,
            "exclude_size": exclude_size,
            "exclude_border_objects": False,
            "threshold_scope": CellProfilerThresholdScope.ADAPTIVE,
            "threshold_method": CellProfilerThresholdMethod.OTSU,
            "adaptive_window_size": (
                self.adaptive_window_size_px
                if adaptive_window_size is None
                else adaptive_window_size
            ),
        }

    def compact_body_detection_kwargs(
        self,
        *,
        adaptive_window_size: int,
    ) -> dict[str, object]:
        """Candidate settings for MetaXpress predicates and CP propagation."""

        return self.body_detection_kwargs(
            adaptive_window_size=adaptive_window_size,
            exclude_size=False,
            min_diameter=self.compact_body_min_diameter_px,
        )

    def enhancement_kwargs(
        self,
        *,
        smoothing_value: float | None = None,
    ) -> dict[str, object]:
        return {
            "method": OperationMethod.ENHANCE,
            "enhance_method": EnhanceMethod.NEURITES,
            "neurite_method": NeuriteMethod.TUBENESS,
            "smoothing_value": (
                self.tubeness_smoothing_px
                if smoothing_value is None
                else smoothing_value
            ),
            "neurite_rescale": True,
        }

    def threshold_kwargs(
        self,
        *,
        window_size: int | None = None,
        smoothing: float | None = None,
        correction_factor: float | None = None,
    ) -> dict[str, object]:
        return {
            "threshold_scope": CellProfilerThresholdScope.ADAPTIVE,
            "threshold_method": CellProfilerThresholdMethod.OTSU,
            "threshold_correction_factor": (
                self.neurite_candidate_threshold_correction_factor
                if correction_factor is None
                else correction_factor
            ),
            "window_size": (
                self.adaptive_window_size_px if window_size is None else window_size
            ),
            "smoothing": (
                self.threshold_smoothing_px if smoothing is None else smoothing
            ),
        }

    def secondary_kwargs(
        self,
        *,
        adaptive_window_size: int | None = None,
    ) -> dict[str, object]:
        return {
            "method": SecondaryMethod.PROPAGATION,
            "threshold_scope": CellProfilerThresholdScope.ADAPTIVE,
            "threshold_method": CellProfilerThresholdMethod.OTSU,
            "threshold_correction_factor": (
                self.secondary_ownership_threshold_correction_factor
            ),
            "adaptive_window_size": (
                self.adaptive_window_size_px
                if adaptive_window_size is None
                else adaptive_window_size
            ),
            "regularization_factor": self.secondary_regularization_factor,
            "fill_holes": True,
            "discard_edge_objects": False,
        }


CELLPROFILER_NEURITE_ENGINE_PROFILE = CellProfilerNeuriteEngineProfile()


@dataclass(frozen=True)
class MetaXpressCellBodySettings:
    """Documented cell-body controls for Neurite Outgrowth."""

    approximate_max_width: float = 30.0
    """Approximate maximum short-axis width in micrometers."""

    minimum_area: float = 50.0
    """Minimum cell-body area in square micrometers."""

    intensity_above_local_background: float = 100.0
    """Minimum absolute intensity difference from local background."""

    channel_index: int | None = None
    """Optional body channel; omitted means the neurite channel."""

    def validate(self) -> None:
        if (
            not np.isfinite(self.approximate_max_width)
            or self.approximate_max_width <= 0
        ):
            raise ValueError("cell_body.approximate_max_width must be > 0")
        if not np.isfinite(self.minimum_area) or self.minimum_area <= 0:
            raise ValueError("cell_body.minimum_area must be > 0")
        if (
            not np.isfinite(self.intensity_above_local_background)
            or self.intensity_above_local_background < 0
        ):
            raise ValueError("cell_body.intensity_above_local_background must be >= 0")
        if self.channel_index is not None and (
            isinstance(self.channel_index, bool)
            or not isinstance(self.channel_index, (int, np.integer))
            or self.channel_index < 0
        ):
            raise ValueError("cell_body.channel_index must be a non-negative integer")


@dataclass(frozen=True)
class MetaXpressOutgrowthSettings:
    """Documented outgrowth controls for Neurite Outgrowth."""

    maximum_width: float = 4.0
    """Maximum outgrowth width in micrometers."""

    intensity_above_local_background: float = 50.0
    """Minimum absolute intensity difference from local background."""

    minimum_cell_growth_to_log_as_significant: float = 10.0
    """Scoring-only total outgrowth threshold in micrometers."""

    candidate_threshold_correction_factor: float = (
        CELLPROFILER_NEURITE_ENGINE_PROFILE.neurite_candidate_threshold_correction_factor
    )
    """Adaptive foreground sensitivity; lower values admit dimmer candidates."""

    candidate_hysteresis_seed_correction_factor: float | None = None
    """Optional stricter seed threshold retaining connected dim candidates."""

    def validate(self) -> None:
        if not np.isfinite(self.maximum_width) or self.maximum_width <= 0:
            raise ValueError("outgrowth.maximum_width must be > 0")
        if (
            not np.isfinite(self.intensity_above_local_background)
            or self.intensity_above_local_background < 0
        ):
            raise ValueError("outgrowth.intensity_above_local_background must be >= 0")
        if (
            not np.isfinite(self.minimum_cell_growth_to_log_as_significant)
            or self.minimum_cell_growth_to_log_as_significant < 0
        ):
            raise ValueError(
                "outgrowth.minimum_cell_growth_to_log_as_significant must be >= 0"
            )
        if (
            not np.isfinite(self.candidate_threshold_correction_factor)
            or self.candidate_threshold_correction_factor <= 0
        ):
            raise ValueError(
                "outgrowth.candidate_threshold_correction_factor must be > 0"
            )
        if self.candidate_hysteresis_seed_correction_factor is not None:
            seed_factor = self.candidate_hysteresis_seed_correction_factor
            if not np.isfinite(seed_factor) or seed_factor <= 0:
                raise ValueError(
                    "outgrowth.candidate_hysteresis_seed_correction_factor must "
                    "be > 0 when set"
                )
            if seed_factor < self.candidate_threshold_correction_factor:
                raise ValueError(
                    "outgrowth.candidate_hysteresis_seed_correction_factor must "
                    "be >= outgrowth.candidate_threshold_correction_factor"
                )


@dataclass(frozen=True)
class MetaXpressNuclearSettings(MetaXpressWavelengthSettings):
    """Optional documented nuclear-stain controls."""

    channel_index: int = 1


@dataclass(frozen=True)
class NeuriteOutgrowthSummary:
    """MetaXpress-style image-level neurite measurements."""

    neurite_channel_index: int
    cell_body_channel_index: int
    nuclear_channel_index: int
    number_of_cells: int
    total_outgrowth_um: float
    mean_outgrowth_per_cell_um: float
    total_processes: int
    mean_processes_per_cell: float
    total_branches: int
    mean_branches_per_cell: float
    total_cell_body_area_um2: float
    mean_cell_body_area_um2: float
    straightness: float
    cells_significant_growth: int
    percent_cells_significant_growth: float
    mean_outgrowth_average_intensity: float
    resolved_crossovers: int
    candidate_trace_pixels: int
    rooted_candidate_trace_pixels: int
    unrooted_candidate_trace_pixels: int
    rooted_candidate_trace_yield: float
    initial_topology_owned_trace_pixels: int
    secondary_adopted_trace_pixels: int
    signal_repaired_trace_pixels: int
    crossing_core_trace_pixels: int
    final_topology_dropped_trace_pixels: int
    final_topology_dropped_crossing_support_trace_pixels: int
    final_topology_dropped_unrooted_path_trace_pixels: int
    final_topology_dropped_physically_rooted_path_trace_pixels: int
    final_topology_dropped_physically_unrooted_path_trace_pixels: int
    final_topology_dropped_unrepresented_trace_pixels: int
    final_topology_added_trace_pixels: int
    final_topology_owned_trace_pixels: int
    published_owned_trace_pixels: int
    secondary_owned_unrooted_trace_pixels: int
    secondary_unowned_unrooted_trace_pixels: int
    candidate_mask_pixels: int
    rooted_candidate_mask_pixels: int
    unrooted_residual_pixels: int
    secondary_owned_residual_pixels: int
    secondary_unowned_residual_pixels: int
    secondary_owned_residual_fraction: float


@dataclass(frozen=True)
class NeuriteOutgrowthCellResult:
    """Cell measurements of the final soma-rooted neurite topology.

    A process is the owned path partition reached from one soma-adjacent root.
    Count, total, mean, median and maximum all describe those same process
    lengths, including their branches. Distances use the supplied pixel size:
    calibrated inputs yield micrometers; an uncalibrated unit pixel size yields
    pixels despite the legacy ``_um`` column names. No independent seed-relative
    skeleton measurement rescales them.
    """

    slice_index: int
    cell: int
    total_outgrowth_um: float
    processes: int
    mean_process_length_um: float
    median_process_length_um: float
    max_process_length_um: float
    branches: int
    straightness: float
    cell_body_area_um2: float
    mean_outgrowth_intensity: float
    significant_growth: bool


@dataclass(frozen=True)
class NeuronalCellBodySummary:
    """Image-level neuronal soma count independent of axon ownership."""

    cell_body_channel_index: int
    nuclear_channel_index: int
    nuclei_detected: int
    neuronal_cell_body_count: int
    total_cell_body_area_um2: float
    mean_cell_body_area_um2: float
    mean_cell_body_intensity: float


@dataclass(frozen=True)
class NeuronalCellBodyResult:
    """Per-soma measurements for an independently detected neuronal body."""

    cell: int
    cell_body_area_um2: float
    mean_cell_body_intensity: float


NEURITE_OBJECT_LABEL_MATERIALIZATION = MaterializationSpec(
    ROIOptions(),
    ImageFileOptions(
        filename_suffix=".labels.tif",
        filename_identity=MaterializedFilenameIdentity.ARTIFACT_NAME,
    ),
)

NEURITE_SUMMARY_OUTPUT = ArtifactSpec.output(
    "neurite_outgrowth_summary",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(ArtifactMeasurementSubjectRelation(),),
)
UNIFIED_NEURONS_OUTPUT = ArtifactSpec.output(
    "neurons",
    ObjectLabelsArtifactType,
    materialization=NEURITE_OBJECT_LABEL_MATERIALIZATION,
    relations=(ObjectArtifactMemberSubjectRelation(),),
)
CELL_BODIES_OUTPUT = ArtifactSpec.output(
    "cell_bodies",
    ObjectLabelsArtifactType,
    materialization=NEURITE_OBJECT_LABEL_MATERIALIZATION,
    viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
    relations=(
        ObjectArtifactMemberSubjectRelation(
            source=UNIFIED_NEURONS_OUTPUT.ref(),
            member_id_field="label",
        ),
    ),
)
NEURITE_CELLS_OUTPUT = ArtifactSpec.output(
    "neurite_outgrowth_cells",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(
        ObjectMeasurementSubjectRelation(
            source=UNIFIED_NEURONS_OUTPUT.ref(),
            id_field="cell",
        ),
    ),
)
NEURITE_LABELS_OUTPUT = ArtifactSpec.output(
    "neurite_outgrowth",
    ObjectLabelsArtifactType,
    materialization=NEURITE_OBJECT_LABEL_MATERIALIZATION,
    viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
    relations=(
        ObjectArtifactMemberSubjectRelation(
            source=UNIFIED_NEURONS_OUTPUT.ref(),
            member_id_field="label",
        ),
    ),
)
NUCLEI_OUTPUT = ArtifactSpec.output(
    "nuclei",
    ObjectLabelsArtifactType,
    materialization=NEURITE_OBJECT_LABEL_MATERIALIZATION,
    viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
)
NEURONAL_CELL_BODY_SUMMARY_OUTPUT = ArtifactSpec.output(
    "neuronal_cell_body_summary",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(ArtifactMeasurementSubjectRelation(),),
)
NEURONAL_CELL_BODIES_OUTPUT = ArtifactSpec.output(
    "neuronal_cell_bodies",
    ObjectLabelsArtifactType,
    materialization=NEURITE_OBJECT_LABEL_MATERIALIZATION,
    viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
)
NEURONAL_CELL_BODY_MEASUREMENTS_OUTPUT = ArtifactSpec.output(
    "neuronal_cell_body_measurements",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(
        ObjectMeasurementSubjectRelation(
            source=NEURONAL_CELL_BODIES_OUTPUT.ref(),
            id_field="cell",
        ),
    ),
)
NEURITE_MORPHOLOGY_OUTPUT = ArtifactSpec.output(
    "neurite_morphology",
    SpatialGraphArtifactType,
    materialization=MaterializationSpec(
        SWCOptions(),
        SpatialGraphROIOptions(),
    ),
    relations=(
        ObjectArtifactMemberSubjectRelation(
            source=UNIFIED_NEURONS_OUTPUT.ref(),
            member_id_field="label",
        ),
    ),
)


def _neurite_qa_checkpoint_output(name: str) -> ArtifactSpec:
    """Declare a source-identifiable plane checkpoint from the assembled stack."""

    return MainFlowPlaneProjectionOutputSpec.output(
        name,
        ImageArtifactType,
        sidecar_role=ArtifactSidecarRole.QA_CHECKPOINT,
        materialization=MaterializationSpec(
            ImageFileOptions(filename_suffix=f"_{name}.checkpoint.tif")
        ),
        viewer_streaming=ArtifactViewerStreaming.ON_DEMAND,
    )


NEURITE_CANDIDATE_MASK_OUTPUT = _neurite_qa_checkpoint_output("neurite_candidate_mask")
NEURITE_UNROOTED_RESIDUAL_OUTPUT = _neurite_qa_checkpoint_output(
    "neurite_unrooted_residual"
)
NEURITE_SECONDARY_OWNERSHIP_OUTPUT = _neurite_qa_checkpoint_output(
    "neurite_secondary_ownership"
)
NEURITE_TOPOLOGY_DROPPED_TRACE_OUTPUT = _neurite_qa_checkpoint_output(
    "neurite_topology_dropped_trace"
)
NEURITE_TOPOLOGY_ADDED_TRACE_OUTPUT = _neurite_qa_checkpoint_output(
    "neurite_topology_added_trace"
)


@dataclass(frozen=True)
class _TopologyResult:
    path_owners: np.ndarray
    path_distances: np.ndarray
    path_lengths: np.ndarray
    path_euclidean_lengths: np.ndarray
    path_coordinates: tuple[np.ndarray, ...]
    path_endpoint_groups: tuple[tuple[int, int], ...]
    path_branch_types: np.ndarray
    endpoint_group_coordinates: Mapping[int, tuple[float, float]]
    transitions: Mapping[int, tuple[int, ...]]
    root_paths_by_cell: Mapping[int, tuple[int, ...]]
    branch_nodes_by_cell: Mapping[int, tuple[int, ...]]
    crossing_nodes: frozenset[int]
    crossing_paths: frozenset[int]
    crossing_core_paths: frozenset[int]


def _raw_processing_leaf(func):
    """Resolve a composed leaf's runtime body through its callable contract."""

    return CallableContract.from_callable(func).resolve_raw_runtime_callable()


@numpy
@artifact_outputs(
    NEURONAL_CELL_BODY_SUMMARY_OUTPUT,
    NEURONAL_CELL_BODY_MEASUREMENTS_OUTPUT,
    NEURONAL_CELL_BODIES_OUTPUT,
    NUCLEI_OUTPUT,
)
@artifact_inputs("pixel_size")
def count_neuronal_cell_bodies_metaxpress(
    image,
    illumination: NeuriteIllumination = NeuriteIllumination.FLUORESCENCE,
    cell_body: MetaXpressCellBodySettings = MetaXpressCellBodySettings(),
    nuclear_stain: MetaXpressNuclearSettings = MetaXpressNuclearSettings(),
    pixel_size: HiddenPixelSize = HiddenPixelSize(1.0),
) -> tuple[
    np.ndarray,
    DataclassMeasurementColumnarRows,
    DataclassMeasurementColumnarRows,
    np.ndarray,
    np.ndarray,
]:
    """Count nuclear-supported neuronal somas without assigning axons.

    The soma channel defines neuronal cytoplasm candidates. The nuclear channel
    confirms those candidates, but does not turn every detected nucleus into a
    neuronal cell. This callable deliberately has no neurite, graph, or unified
    neuron outputs, so its cell identities cannot imply ownership of axons in a
    tissue field.

    Args:
        illumination: Interpret foreground as brighter than background for
            fluorescence or darker than background for transmission images.
        cell_body: Cell-body channel, size, area, and local-background controls
            used to propose neuronal soma candidates.
        nuclear_stain: Nuclear-stain channel and round-object controls used to
            confirm soma candidates.
    """

    image_array = np.asarray(image)
    if image_array.ndim != 3:
        raise ValueError(
            "Expected a 2D channel stack with shape (C, Y, X), got "
            f"shape {image_array.shape}"
        )

    illumination = NeuriteIllumination(illumination)
    cell_body.validate()
    nuclear_stain.validate("nuclear_stain")
    pixel_size_um = float(pixel_size)
    if not np.isfinite(pixel_size_um) or pixel_size_um <= 0:
        raise ValueError("pixel_size must be a finite value > 0")

    body_channel_index = (
        0 if cell_body.channel_index is None else int(cell_body.channel_index)
    )
    nuclear_channel_index = int(nuclear_stain.channel_index)
    for name, channel_index in (
        ("cell_body.channel_index", body_channel_index),
        ("nuclear_stain.channel_index", nuclear_channel_index),
    ):
        if not 0 <= channel_index < image_array.shape[0]:
            raise ValueError(f"{name} is outside the input stack")
    if body_channel_index == nuclear_channel_index:
        raise ValueError(
            "cell_body.channel_index and nuclear_stain.channel_index must differ"
        )

    nuclei_labels = segment_metaxpress_round_objects(
        image_array[nuclear_channel_index],
        nuclear_stain,
        pixel_size_um,
    )
    cell_body_payload = _identify_nuclear_seeded_cell_bodies_cellprofiler(
        image_array[body_channel_index],
        cell_body,
        pixel_size_um,
        bright_objects=illumination == NeuriteIllumination.FLUORESCENCE,
        nuclei_labels=nuclei_labels,
    )
    cell_body_labels = object_label_dense_array(
        cell_body_payload,
        dtype=np.int32,
    )
    body_image = image_array[body_channel_index]
    cell_results = tuple(
        NeuronalCellBodyResult(
            cell=int(region.label),
            cell_body_area_um2=float(region.area) * pixel_size_um**2,
            mean_cell_body_intensity=float(region.mean_intensity),
        )
        for region in regionprops(cell_body_labels, intensity_image=body_image)
    )
    total_area = float(sum(result.cell_body_area_um2 for result in cell_results))
    mean_intensity = (
        float(np.mean([result.mean_cell_body_intensity for result in cell_results]))
        if cell_results
        else 0.0
    )
    summary = NeuronalCellBodySummary(
        cell_body_channel_index=body_channel_index,
        nuclear_channel_index=nuclear_channel_index,
        nuclei_detected=int(nuclei_labels.max()),
        neuronal_cell_body_count=len(cell_results),
        total_cell_body_area_um2=total_area,
        mean_cell_body_area_um2=(
            total_area / len(cell_results) if cell_results else 0.0
        ),
        mean_cell_body_intensity=mean_intensity,
    )

    cell_body_stack = np.zeros(image_array.shape, dtype=np.int32)
    cell_body_stack[body_channel_index] = cell_body_labels
    nuclei_stack = np.zeros(image_array.shape, dtype=np.int32)
    nuclei_stack[nuclear_channel_index] = nuclei_labels
    return (
        image,
        DataclassMeasurementColumnarRows(
            (summary,),
            row_type=NeuronalCellBodySummary,
        ),
        DataclassMeasurementColumnarRows(
            cell_results,
            row_type=NeuronalCellBodyResult,
        ),
        cell_body_stack,
        nuclei_stack,
    )


@numpy
@artifact_outputs(
    NEURITE_SUMMARY_OUTPUT,
    NEURITE_CELLS_OUTPUT,
    CELL_BODIES_OUTPUT,
    NEURITE_LABELS_OUTPUT,
    UNIFIED_NEURONS_OUTPUT,
    NUCLEI_OUTPUT,
    NEURITE_CANDIDATE_MASK_OUTPUT,
    NEURITE_UNROOTED_RESIDUAL_OUTPUT,
    NEURITE_SECONDARY_OWNERSHIP_OUTPUT,
    NEURITE_TOPOLOGY_DROPPED_TRACE_OUTPUT,
    NEURITE_TOPOLOGY_ADDED_TRACE_OUTPUT,
    NEURITE_MORPHOLOGY_OUTPUT,
)
@artifact_inputs("pixel_size")
def neurite_outgrowth_metaxpress(
    image,
    neurite_channel_index: int = 0,
    illumination: NeuriteIllumination = NeuriteIllumination.FLUORESCENCE,
    cell_body: MetaXpressCellBodySettings = MetaXpressCellBodySettings(),
    outgrowth: MetaXpressOutgrowthSettings = MetaXpressOutgrowthSettings(),
    use_nuclear_stain: bool = False,
    nuclear_stain: MetaXpressNuclearSettings = MetaXpressNuclearSettings(),
    pixel_size: HiddenPixelSize = HiddenPixelSize(1.0),
) -> tuple[
    np.ndarray,
    DataclassMeasurementColumnarRows,
    DataclassMeasurementColumnarRows,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    SelectedPlaneImageOutput,
    SelectedPlaneImageOutput,
    SelectedPlaneImageOutput,
    SelectedPlaneImageOutput,
    SelectedPlaneImageOutput,
    SpatialGraph,
]:
    """Measure cell bodies and attached neurites in one 2D channel stack.

    The user-facing controls follow the MetaXpress Neurite Outgrowth module:
    neurite image and illumination; optional cell-body channel, maximum width,
    minimum area, and local-background intensity; outgrowth maximum width,
    local-background intensity, and scoring threshold; plus an optional nuclear
    wavelength with minimum/maximum width and local-background intensity.

    This implementation is deliberately 2D. ``image`` must have shape
    ``(C, Y, X)`` and should be produced by a step whose variable component is
    ``CHANNEL``. Outgrowth detection is independent of the significant-growth
    threshold. CellProfiler-compatible primary-object, tubeness, adaptive Otsu,
    and medial-axis leaves provide the opinionated segmentation engine. Final
    soma-rooted path ownership determines both measurements and rendered masks;
    disconnected traces are omitted from the rendered ownership mask.

    Args:
        neurite_channel_index: Zero-based channel containing neurite outgrowth.
        illumination: Fluorescence or transmission contrast model used for
            foreground detection.
        cell_body: Optional channel plus width, area, and local-background
            thresholds for cell bodies.
        outgrowth: Width, intensity, and significant-growth thresholds for
            attached neurites.
        use_nuclear_stain: Whether to segment a nuclear channel and return nuclei.
        nuclear_stain: Nuclear channel and size/intensity thresholds used when
            nuclear staining is enabled.

    Returns:
        The unchanged image, image- and cell-level measurement rows, and
        channel-aligned cell-body, thin outgrowth, unified-neuron, and nuclear
        masks, followed by a rooted spatial morphology forest. The unified
        layer assigns each body and its owned outgrowth the same integer
        identity, while the graph preserves branch geometry and metrics for
        direct table, ROI-path, and SWC inspection. Object-label artifacts retain
        complete integer masks as lossless TIFFs alongside contour ROI archives;
        ROI area filtering does not remove pixels from those TIFFs.
    """

    image_array = np.asarray(image)
    if image_array.ndim != 3:
        raise ValueError(
            f"Expected a 2D channel stack with shape (C, Y, X), got "
            f"shape {image_array.shape}"
        )
    if not 0 <= neurite_channel_index < image_array.shape[0]:
        raise ValueError("neurite_channel_index is outside the input stack")

    illumination = NeuriteIllumination(illumination)
    cell_body.validate()
    outgrowth.validate()
    pixel_size_um = float(pixel_size)
    if not np.isfinite(pixel_size_um) or pixel_size_um <= 0:
        raise ValueError("pixel_size must be a finite value > 0")

    body_channel_index = (
        neurite_channel_index
        if cell_body.channel_index is None
        else int(cell_body.channel_index)
    )
    if not 0 <= body_channel_index < image_array.shape[0]:
        raise ValueError("cell_body.channel_index is outside the input stack")

    nuclei_labels = np.zeros(image_array.shape[1:], dtype=np.int32)
    if use_nuclear_stain:
        nuclear_stain.validate("nuclear_stain")
        if not 0 <= nuclear_stain.channel_index < image_array.shape[0]:
            raise ValueError("nuclear_stain.channel_index is outside the input stack")
        if nuclear_stain.channel_index == neurite_channel_index:
            raise ValueError(
                "nuclear_stain.channel_index must differ from neurite_channel_index"
            )
        nuclei_labels = segment_metaxpress_round_objects(
            image_array[nuclear_stain.channel_index],
            nuclear_stain,
            pixel_size_um,
        )

    bright_objects = illumination == NeuriteIllumination.FLUORESCENCE
    nuclear_seeded_signal_body_mode = (
        use_nuclear_stain and body_channel_index == neurite_channel_index
    )
    body_detection_channel_index = (
        int(nuclear_stain.channel_index)
        if nuclear_seeded_signal_body_mode
        else body_channel_index
    )
    body_image = image_array[body_detection_channel_index]
    neurite_image = image_array[neurite_channel_index]
    if nuclear_seeded_signal_body_mode:
        signal_cell_bodies = _derive_signal_cell_bodies(
            nuclei_labels,
            neurite_image,
            cell_body,
            pixel_size_um,
            bright_objects=bright_objects,
        )
        keep_signal_body = (
            np.bincount(
                signal_cell_bodies.ravel(),
                minlength=int(nuclei_labels.max()) + 1,
            )
            > 0
        )
        keep_signal_body[0] = False
        cell_body_labels = _relabel(signal_cell_bodies, keep_signal_body)
        cell_body_payload = SourceImageObjectLabelBuildRequest(
            image=neurite_image,
            labels=cell_body_labels,
        ).payload()
    else:
        cell_body_payload = _identify_cell_bodies_cellprofiler(
            body_image,
            cell_body,
            pixel_size_um,
            bright_objects=bright_objects,
            nuclei_labels=nuclei_labels if use_nuclear_stain else None,
        )
        cell_body_labels = object_label_dense_array(
            cell_body_payload,
            dtype=np.int32,
        )

    outgrowth_binary, outgrowth_skeleton, outgrowth_response = (
        _identify_neurites_cellprofiler(
            neurite_image,
            cell_body,
            outgrowth,
            pixel_size_um,
            bright_objects=bright_objects,
        )
    )
    outgrowth_width_px = outgrowth.maximum_width / pixel_size_um
    nuclear_seed_mode = use_nuclear_stain and body_detection_channel_index == int(
        nuclear_stain.channel_index
    )
    if nuclear_seeded_signal_body_mode:
        secondary_owner_regions = _propagate_neurite_owner_regions(
            outgrowth_response,
            cell_body_labels,
            minimum_response=outgrowth.intensity_above_local_background,
        )
    else:
        secondary_owner_regions = _identify_secondary_owner_regions_cellprofiler(
            neurite_image,
            cell_body_payload,
            body_width_px=cell_body.approximate_max_width / pixel_size_um,
            bright_objects=bright_objects,
        )
    if nuclear_seed_mode and not nuclear_seeded_signal_body_mode:
        cell_body_payload = _qualify_nuclear_cell_bodies(
            cell_body_payload,
            cell_body_labels,
            secondary_owner_regions,
        )
        cell_body_labels = object_label_dense_array(
            cell_body_payload,
            dtype=np.int32,
        )
        secondary_owner_regions = _identify_secondary_owner_regions_cellprofiler(
            neurite_image,
            cell_body_payload,
            body_width_px=cell_body.approximate_max_width / pixel_size_um,
            bright_objects=bright_objects,
        )

    topology = _analyze_topology(
        outgrowth_skeleton,
        cell_body_labels,
        pixel_size_um,
        outgrowth_width_px,
    )
    owner_skeleton = _render_owned_skeleton(
        outgrowth_skeleton.shape,
        topology,
    )
    initial_topology_owned_trace_pixels = int(
        np.count_nonzero((owner_skeleton > 0) & (cell_body_labels == 0))
    )
    if nuclear_seed_mode:
        owner_skeleton = _adopt_secondary_owned_path_segments(
            topology,
            owner_skeleton,
            secondary_owner_regions,
        )
    secondary_adopted_trace_pixels = int(
        np.count_nonzero((owner_skeleton > 0) & (cell_body_labels == 0))
    )
    crossing_support = _render_crossing_support(
        outgrowth_skeleton.shape,
        topology,
    )
    crossing_core_mask = _render_crossing_core_mask(
        outgrowth_skeleton.shape,
        topology,
    )
    resolved_crossovers = _count_multi_owner_crossings(
        crossing_core_mask,
        crossing_support,
    )
    crossing_core_support = np.where(
        crossing_core_mask,
        crossing_support,
        0,
    ).astype(np.int32, copy=False)
    owner_skeleton = _repair_signal_supported_skeleton(
        owner_skeleton,
        outgrowth_response,
        secondary_owner_regions,
        cell_body_labels,
        minimum_response=outgrowth.intensity_above_local_background,
    )
    owner_skeleton = np.where(
        crossing_support > 0,
        crossing_support,
        owner_skeleton,
    ).astype(np.int32, copy=False)
    signal_repaired_trace_pixels = int(
        np.count_nonzero((owner_skeleton > 0) & (cell_body_labels == 0))
    )
    pre_topology_owner_skeleton = owner_skeleton.copy()
    pre_topology_owner_skeleton[cell_body_labels > 0] = 0
    topology = _analyze_owned_topology(
        pre_topology_owner_skeleton,
        cell_body_labels,
        pixel_size_um,
        outgrowth_width_px,
        shared_crossing_mask=crossing_core_mask,
    )
    neurite_skeleton = _render_owned_skeleton(
        pre_topology_owner_skeleton.shape,
        topology,
    )
    topology_path_mask = _render_topology_path_mask(
        pre_topology_owner_skeleton.shape,
        topology,
    )
    physically_soma_rooted_trace = _physically_soma_rooted_owner_mask(
        pre_topology_owner_skeleton,
        cell_body_labels,
        maximum_root_distance=max(1, int(np.ceil(outgrowth_width_px)) + 2),
    )
    topology_dropped_trace = (
        (pre_topology_owner_skeleton > 0)
        & (neurite_skeleton == 0)
        & ~crossing_core_mask
    )
    topology_added_trace = (neurite_skeleton > 0) & (pre_topology_owner_skeleton == 0)
    final_topology_owned_trace_pixels = int(np.count_nonzero(neurite_skeleton))
    # A physical crossing core supports two logical paths, but an object-label
    # raster can store only one identity per pixel. The topology above remains
    # authoritative for both neurites; publish the already-resolved nearest
    # owner for each shared physical core pixel so QA and raster expansion do
    # not misclassify valid crossover signal as an unrooted residual.
    neurite_skeleton = np.where(
        crossing_core_support > 0,
        crossing_core_support,
        neurite_skeleton,
    ).astype(np.int32, copy=False)
    owner_outgrowth = _expand_skeleton_ownership(
        neurite_skeleton,
        outgrowth_binary,
        outgrowth_width_px,
    )
    owner_outgrowth[cell_body_labels > 0] = 0
    # Secondary propagation supplies foreground evidence during detection;
    # final neuron ownership comes from the same rooted topology as its traces
    # and measurements. Publishing the earlier propagation would reassign
    # crossing arms independently of that topology.
    unified_neuron_labels = np.where(
        cell_body_labels > 0,
        cell_body_labels,
        owner_outgrowth,
    ).astype(np.int32, copy=False)

    candidate_neurite_mask = outgrowth_binary & (cell_body_labels == 0)
    candidate_trace_mask = outgrowth_skeleton & (cell_body_labels == 0)
    rooted_mask = owner_outgrowth > 0
    rooted_trace_mask = neurite_skeleton > 0
    unrooted_residual = candidate_neurite_mask & ~rooted_mask
    secondary_owned_residual = unrooted_residual & (secondary_owner_regions > 0)
    candidate_trace_pixels = int(np.count_nonzero(candidate_trace_mask))
    rooted_candidate_trace_pixels = int(
        np.count_nonzero(candidate_trace_mask & rooted_trace_mask)
    )
    secondary_owned_unrooted_trace_pixels = int(
        np.count_nonzero(
            candidate_trace_mask & ~rooted_trace_mask & (secondary_owner_regions > 0)
        )
    )
    candidate_mask_pixels = int(np.count_nonzero(candidate_neurite_mask))
    rooted_candidate_mask_pixels = int(
        np.count_nonzero(candidate_neurite_mask & rooted_mask)
    )
    unrooted_residual_pixels = int(np.count_nonzero(unrooted_residual))
    secondary_owned_residual_pixels = int(np.count_nonzero(secondary_owned_residual))

    cell_results = _build_cell_results(
        cell_body_labels,
        owner_outgrowth,
        neurite_image,
        topology,
        outgrowth.minimum_cell_growth_to_log_as_significant,
        pixel_size_um,
        slice_index=body_channel_index,
    )
    summary = _build_summary(
        cell_results,
        neurite_channel_index=neurite_channel_index,
        cell_body_channel_index=body_channel_index,
        nuclear_channel_index=(
            nuclear_stain.channel_index if use_nuclear_stain else -1
        ),
        resolved_crossovers=resolved_crossovers,
        mean_outgrowth_average_intensity=(
            float(np.mean(neurite_image[owner_outgrowth > 0]))
            if np.any(owner_outgrowth > 0)
            else 0.0
        ),
        candidate_trace_pixels=candidate_trace_pixels,
        rooted_candidate_trace_pixels=rooted_candidate_trace_pixels,
        unrooted_candidate_trace_pixels=(
            candidate_trace_pixels - rooted_candidate_trace_pixels
        ),
        rooted_candidate_trace_yield=(
            rooted_candidate_trace_pixels / candidate_trace_pixels
            if candidate_trace_pixels
            else 0.0
        ),
        initial_topology_owned_trace_pixels=initial_topology_owned_trace_pixels,
        secondary_adopted_trace_pixels=secondary_adopted_trace_pixels,
        signal_repaired_trace_pixels=signal_repaired_trace_pixels,
        crossing_core_trace_pixels=int(np.count_nonzero(crossing_core_mask)),
        final_topology_dropped_trace_pixels=int(
            np.count_nonzero(topology_dropped_trace)
        ),
        final_topology_dropped_crossing_support_trace_pixels=int(
            np.count_nonzero(topology_dropped_trace & (crossing_support > 0))
        ),
        final_topology_dropped_unrooted_path_trace_pixels=int(
            np.count_nonzero(topology_dropped_trace & topology_path_mask)
        ),
        final_topology_dropped_physically_rooted_path_trace_pixels=int(
            np.count_nonzero(
                topology_dropped_trace
                & topology_path_mask
                & physically_soma_rooted_trace
            )
        ),
        final_topology_dropped_physically_unrooted_path_trace_pixels=int(
            np.count_nonzero(
                topology_dropped_trace
                & topology_path_mask
                & ~physically_soma_rooted_trace
            )
        ),
        final_topology_dropped_unrepresented_trace_pixels=int(
            np.count_nonzero(topology_dropped_trace & ~topology_path_mask)
        ),
        final_topology_added_trace_pixels=int(np.count_nonzero(topology_added_trace)),
        final_topology_owned_trace_pixels=final_topology_owned_trace_pixels,
        published_owned_trace_pixels=int(np.count_nonzero(rooted_trace_mask)),
        secondary_owned_unrooted_trace_pixels=(secondary_owned_unrooted_trace_pixels),
        secondary_unowned_unrooted_trace_pixels=(
            candidate_trace_pixels
            - rooted_candidate_trace_pixels
            - secondary_owned_unrooted_trace_pixels
        ),
        candidate_mask_pixels=candidate_mask_pixels,
        rooted_candidate_mask_pixels=rooted_candidate_mask_pixels,
        unrooted_residual_pixels=unrooted_residual_pixels,
        secondary_owned_residual_pixels=secondary_owned_residual_pixels,
        secondary_unowned_residual_pixels=(
            unrooted_residual_pixels - secondary_owned_residual_pixels
        ),
        secondary_owned_residual_fraction=(
            secondary_owned_residual_pixels / unrooted_residual_pixels
            if unrooted_residual_pixels
            else 0.0
        ),
    )

    cell_body_stack = np.zeros(image_array.shape, dtype=np.int32)
    cell_body_stack[body_channel_index] = cell_body_labels
    neurite_stack = np.zeros(image_array.shape, dtype=np.int32)
    neurite_stack[neurite_channel_index] = neurite_skeleton
    unified_neuron_stack = np.zeros(image_array.shape, dtype=np.int32)
    unified_neuron_stack[neurite_channel_index] = unified_neuron_labels
    nuclei_stack = np.zeros(image_array.shape, dtype=np.int32)
    if use_nuclear_stain:
        nuclei_stack[nuclear_stain.channel_index] = nuclei_labels
    neurite_morphology = _build_neurite_morphology_graph(
        topology,
        cell_body_labels,
        pixel_size_um=pixel_size_um,
        outgrowth_width_px=outgrowth_width_px,
    )
    neurite_morphology = neurite_morphology.replace_fields(
        source_plane_index=neurite_channel_index
    )
    return (
        image,
        DataclassMeasurementColumnarRows(
            (summary,),
            row_type=NeuriteOutgrowthSummary,
        ),
        DataclassMeasurementColumnarRows(
            tuple(cell_results),
            row_type=NeuriteOutgrowthCellResult,
        ),
        cell_body_stack,
        neurite_stack,
        unified_neuron_stack,
        nuclei_stack,
        SelectedPlaneImageOutput(
            outgrowth_binary.astype(np.uint8, copy=False)[None],
            (neurite_channel_index,),
        ),
        SelectedPlaneImageOutput(
            unrooted_residual.astype(np.uint8, copy=False)[None],
            (neurite_channel_index,),
        ),
        SelectedPlaneImageOutput(
            secondary_owner_regions.astype(np.int32, copy=False)[None],
            (neurite_channel_index,),
        ),
        SelectedPlaneImageOutput(
            topology_dropped_trace.astype(np.uint8, copy=False)[None],
            (neurite_channel_index,),
        ),
        SelectedPlaneImageOutput(
            topology_added_trace.astype(np.uint8, copy=False)[None],
            (neurite_channel_index,),
        ),
        neurite_morphology,
    )


def _cellprofiler_foreground_image(
    image: np.ndarray,
    *,
    bright_objects: bool,
) -> np.ndarray:
    """Present both illumination modes as bright foreground to CP leaves."""

    image_array = np.asarray(image)
    if bright_objects:
        return image_array
    return np.max(image_array) - image_array


def _cellprofiler_adaptive_window(
    reference_width_px: float,
    image_shape: Sequence[int],
) -> int:
    """Choose a stable CP threshold neighborhood from the declared body scale."""

    minimum_window = max(16, int(np.ceil(2.0 * reference_width_px)))
    scale_window = 1 << (minimum_window - 1).bit_length()
    maximum_window = max(1, min(int(size) for size in image_shape[:2]) // 2)
    return min(scale_window, maximum_window)


def _identify_cell_bodies_cellprofiler(
    image: np.ndarray,
    settings: MetaXpressCellBodySettings,
    pixel_size_um: float,
    *,
    bright_objects: bool,
    nuclei_labels: np.ndarray | None = None,
):
    """Detect with CP IPO, then apply the MetaXpress-owned body predicates."""

    maximum_width_px = settings.approximate_max_width / pixel_size_um
    minimum_area_px = settings.minimum_area / pixel_size_um**2
    _, _, detected_payload = _raw_processing_leaf(identify_primary_objects)(
        _cellprofiler_foreground_image(image, bright_objects=bright_objects),
        **CELLPROFILER_NEURITE_ENGINE_PROFILE.compact_body_detection_kwargs(
            adaptive_window_size=_cellprofiler_adaptive_window(
                maximum_width_px,
                image.shape,
            ),
        ),
    )
    detected_labels = object_label_dense_array(detected_payload, dtype=np.int32)
    response = local_background_response(
        image,
        object_width_px=maximum_width_px,
        bright_objects=bright_objects,
    )
    contract_candidates = _cell_body_contract_candidates(
        detected_labels,
        response,
        minimum_area_px=minimum_area_px,
        maximum_width_px=maximum_width_px,
        intensity_threshold=settings.intensity_above_local_background,
    )

    candidate_labels = np.where(
        contract_candidates[detected_labels],
        detected_labels,
        0,
    )
    nuclear_supported = _nuclear_supported_body_candidates(
        candidate_labels,
        response,
        nuclei_labels,
        maximum_width_px=maximum_width_px,
        intensity_threshold=settings.intensity_above_local_background,
    )
    keep = contract_candidates.copy()
    if nuclear_supported is not None:
        for label in np.flatnonzero(contract_candidates):
            keep[label] = label < nuclear_supported.size and nuclear_supported[label]
    filtered_labels = _relabel(detected_labels, keep)
    return object_label_value_with_dense_labels(
        detected_payload,
        filtered_labels,
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )


def _identify_nuclear_seeded_cell_bodies_cellprofiler(
    image: np.ndarray,
    settings: MetaXpressCellBodySettings,
    pixel_size_um: float,
    *,
    bright_objects: bool,
    nuclei_labels: np.ndarray,
):
    """Propagate DAPI seeds through soma signal, then apply the body contract."""

    maximum_width_px = settings.approximate_max_width / pixel_size_um
    seed_payload_template = _identify_cell_bodies_cellprofiler(
        image,
        settings,
        pixel_size_um,
        bright_objects=bright_objects,
    )
    nuclear_seed_payload = object_label_value_with_dense_labels(
        seed_payload_template,
        nuclei_labels,
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )
    *_, propagated_payload = _raw_processing_leaf(identify_secondary_objects)(
        _cellprofiler_foreground_image(image, bright_objects=bright_objects),
        primary_labels=nuclear_seed_payload,
        **CELLPROFILER_NEURITE_ENGINE_PROFILE.secondary_kwargs(
            adaptive_window_size=_cellprofiler_adaptive_window(
                maximum_width_px,
                image.shape,
            ),
        ),
    )
    propagated_labels = object_label_dense_array(
        propagated_payload,
        dtype=np.int32,
    )
    response = local_background_response(
        image,
        object_width_px=maximum_width_px,
        bright_objects=bright_objects,
    )
    keep = _cell_body_contract_candidates(
        propagated_labels,
        response,
        minimum_area_px=settings.minimum_area / pixel_size_um**2,
        maximum_width_px=maximum_width_px,
        intensity_threshold=settings.intensity_above_local_background,
    )
    return object_label_value_with_dense_labels(
        propagated_payload,
        _relabel(propagated_labels, keep),
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )


def _cell_body_contract_candidates(
    labels: np.ndarray,
    response: np.ndarray,
    *,
    minimum_area_px: float,
    maximum_width_px: float,
    intensity_threshold: float,
) -> np.ndarray:
    """Return label-indexed MetaXpress soma-contract qualification."""

    keep = np.zeros(int(labels.max()) + 1, dtype=bool)
    for region in regionprops(labels):
        row_slice, column_slice = region.slice
        region_slice = (
            slice(
                max(0, row_slice.start - 1), min(labels.shape[0], row_slice.stop + 1)
            ),
            slice(
                max(0, column_slice.start - 1),
                min(labels.shape[1], column_slice.stop + 1),
            ),
        )
        region_mask = labels[region_slice] == region.label
        region_response = response[region_slice][region_mask]
        maximum_inscribed_diameter_px = (
            2.0 * float(np.max(ndi.distance_transform_edt(region_mask))) - 1.0
        )
        if (
            region.area >= minimum_area_px
            and maximum_inscribed_diameter_px
            >= CELLPROFILER_NEURITE_ENGINE_PROFILE.compact_body_min_diameter_px
            and region.axis_minor_length <= maximum_width_px
            and region_response.size
            and float(np.mean(region_response)) >= intensity_threshold
        ):
            keep[region.label] = True
    return keep


def _nuclear_supported_body_candidates(
    detected_labels: np.ndarray,
    response: np.ndarray,
    nuclei_labels: np.ndarray | None,
    *,
    maximum_width_px: float,
    intensity_threshold: float,
) -> np.ndarray | None:
    """Map valid nuclear seeds onto contract-qualified CP body candidates."""

    if nuclei_labels is None:
        return None
    supported = np.zeros(int(detected_labels.max()) + 1, dtype=bool)
    if not np.any(detected_labels):
        return supported

    distance, nearest = ndi.distance_transform_edt(
        detected_labels == 0,
        return_indices=True,
    )
    foreground_distance = ndi.distance_transform_edt(
        response >= intensity_threshold,
    )
    maximum_seed_distance = maximum_width_px / 2.0
    for nucleus in regionprops(nuclei_labels):
        centroid = tuple(
            int(np.clip(round(value), 0, detected_labels.shape[axis] - 1))
            for axis, value in enumerate(nucleus.centroid)
        )
        if distance[centroid] > maximum_seed_distance:
            continue
        foreground_radius = float(foreground_distance[centroid])
        if foreground_radius <= 0:
            continue
        local_foreground_width = 2.0 * foreground_radius - 1.0
        if local_foreground_width > maximum_width_px:
            continue
        nearest_position = tuple(indices[centroid] for indices in nearest)
        candidate = int(detected_labels[nearest_position])
        if candidate > 0:
            supported[candidate] = True
    return supported


def _identify_neurites_cellprofiler(
    image: np.ndarray,
    cell_body: MetaXpressCellBodySettings,
    settings: MetaXpressOutgrowthSettings,
    pixel_size_um: float,
    *,
    bright_objects: bool,
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    """Return the public mask, CP medial axis, and local signal evidence."""

    outgrowth_width_px = settings.maximum_width / pixel_size_um
    body_width_px = cell_body.approximate_max_width / pixel_size_um
    cp_image = _cellprofiler_foreground_image(
        image,
        bright_objects=bright_objects,
    )
    enhanced = _raw_processing_leaf(enhance_or_suppress_features)(
        cp_image,
        **CELLPROFILER_NEURITE_ENGINE_PROFILE.enhancement_kwargs(
            smoothing_value=max(0.5, 0.375 * outgrowth_width_px),
        ),
    )
    cp_mask_payload, _ = _raw_processing_leaf(threshold)(
        enhanced,
        **CELLPROFILER_NEURITE_ENGINE_PROFILE.threshold_kwargs(
            window_size=_cellprofiler_adaptive_window(body_width_px, image.shape),
            smoothing=max(0.0, 0.25 * outgrowth_width_px),
            correction_factor=settings.candidate_threshold_correction_factor,
        ),
    )
    cp_mask = np.asarray(image_payload_data(cp_mask_payload)) > 0
    if settings.candidate_hysteresis_seed_correction_factor is not None:
        seed_mask_payload, _ = _raw_processing_leaf(threshold)(
            enhanced,
            **CELLPROFILER_NEURITE_ENGINE_PROFILE.threshold_kwargs(
                window_size=_cellprofiler_adaptive_window(
                    body_width_px,
                    image.shape,
                ),
                smoothing=max(0.0, 0.25 * outgrowth_width_px),
                correction_factor=(
                    settings.candidate_hysteresis_seed_correction_factor
                ),
            ),
        )
        seed_mask = np.asarray(image_payload_data(seed_mask_payload)) > 0
        cp_mask = _seeded_candidate_components(cp_mask, seed_mask)
    response = local_background_response(
        image,
        object_width_px=outgrowth_width_px,
        bright_objects=bright_objects,
    )
    outgrowth_mask = cp_mask & (response >= settings.intensity_above_local_background)
    skeleton_payload = _raw_processing_leaf(medialaxis)(
        outgrowth_mask.astype(np.float32, copy=False)
    )
    skeleton = np.asarray(image_payload_data(skeleton_payload)) > 0
    return outgrowth_mask, skeleton, response


def _seeded_candidate_components(
    candidate_mask: np.ndarray,
    seed_mask: np.ndarray,
) -> np.ndarray:
    """Retain permissive connected components containing stricter seed pixels."""

    candidates = np.asarray(candidate_mask, dtype=bool)
    seeds = np.asarray(seed_mask, dtype=bool)
    if candidates.shape != seeds.shape:
        raise ValueError("candidate_mask and seed_mask must have the same shape")
    candidate_labels, candidate_count = ndi.label(
        candidates,
        structure=np.ones((3, 3), dtype=bool),
    )
    if candidate_count == 0:
        return np.zeros(candidates.shape, dtype=bool)
    seeded_labels = np.unique(candidate_labels[seeds & candidates])
    keep = np.zeros(candidate_count + 1, dtype=bool)
    keep[seeded_labels] = True
    keep[0] = False
    return keep[candidate_labels]


def _identify_secondary_owner_regions_cellprofiler(
    image: np.ndarray,
    cell_body_payload,
    *,
    body_width_px: float,
    bright_objects: bool,
) -> np.ndarray:
    """Return CP seed-propagated regions used as detection evidence."""

    *_, unified_payload = _raw_processing_leaf(identify_secondary_objects)(
        _cellprofiler_foreground_image(image, bright_objects=bright_objects),
        primary_labels=cell_body_payload,
        **CELLPROFILER_NEURITE_ENGINE_PROFILE.secondary_kwargs(
            adaptive_window_size=_cellprofiler_adaptive_window(
                body_width_px,
                image.shape,
            ),
        ),
    )
    return object_label_dense_array(unified_payload, dtype=np.int32)


def _propagate_neurite_owner_regions(
    signal_response: np.ndarray,
    cell_body_labels: np.ndarray,
    *,
    minimum_response: float,
) -> np.ndarray:
    """Propagate soma identities through the declared neurite foreground."""

    response = np.asarray(signal_response, dtype=float)
    bodies = np.asarray(cell_body_labels, dtype=np.int32)
    if response.shape != bodies.shape:
        raise ValueError(
            "signal_response and cell_body_labels must have the same shape"
        )
    if not np.isfinite(minimum_response) or minimum_response < 0:
        raise ValueError("minimum_response must be finite and >= 0")
    if not np.any(bodies):
        return np.zeros_like(bodies)
    support = (response >= minimum_response) | (bodies > 0)
    return secondary_propagation_backend().propagate(
        response,
        bodies,
        support,
        CELLPROFILER_NEURITE_ENGINE_PROFILE.secondary_regularization_factor,
    )


def _adopt_secondary_owned_path_segments(
    topology: _TopologyResult,
    owner_skeleton: np.ndarray,
    secondary_owner_regions: np.ndarray,
) -> np.ndarray:
    """Partition unowned logical paths by secondary soma ownership.

    Raw connected components are not ownership units: a dense component can
    contain multiple branches or resolved crossing arms belonging to different
    neurons. The topology owns the first decomposition, while the propagated
    secondary labels own the finer boundary between soma territories along an
    otherwise uninterrupted path. Rooted paths retain their stronger topology
    assignment. Unowned path pixels adopt their positive secondary owner and
    are subsequently required to reconnect to that owner's soma through
    continuous signal support. Crossing cores remain temporary physical
    support and are never assigned here.
    """

    adopted = np.asarray(owner_skeleton, dtype=np.int32).copy()
    secondary = np.asarray(secondary_owner_regions, dtype=np.int32)
    if adopted.shape != secondary.shape:
        raise ValueError(
            "owner_skeleton and secondary_owner_regions must have the same shape"
        )

    for path_index, coordinates in enumerate(topology.path_coordinates):
        if path_index in topology.crossing_core_paths or not len(coordinates):
            continue
        path_owner = int(topology.path_owners[path_index])
        if path_owner > 0:
            continue
        secondary_path = secondary[tuple(coordinates.T)]
        current = adopted[tuple(coordinates.T)]
        assignable = (current == 0) & (secondary_path > 0)
        adopted[tuple(coordinates[assignable].T)] = secondary_path[assignable]
    return adopted


def _qualify_nuclear_cell_bodies(
    cell_body_payload,
    cell_body_labels: np.ndarray,
    secondary_owner_regions: np.ndarray,
):
    """Keep DAPI candidates that expand into declared neuronal cytoplasm."""

    label_count = int(cell_body_labels.max())
    body_areas = np.bincount(
        cell_body_labels.ravel(),
        minlength=label_count + 1,
    )
    secondary_areas = np.bincount(
        secondary_owner_regions.ravel(),
        minlength=label_count + 1,
    )
    keep = np.zeros(label_count + 1, dtype=bool)
    keep[1:] = secondary_areas[1:] > body_areas[1:]
    return object_label_value_with_dense_labels(
        cell_body_payload,
        _relabel(cell_body_labels, keep),
        domain_declaration=PresentObjectLabelIdsDomainDeclaration(),
    )


def _derive_signal_cell_bodies(
    nuclear_seed_labels: np.ndarray,
    neurite_image: np.ndarray,
    settings: MetaXpressCellBodySettings,
    pixel_size_um: float,
    *,
    bright_objects: bool,
) -> np.ndarray:
    """Fill bounded soma signal assigned to its nearest nuclear seed."""

    seeds = np.asarray(nuclear_seed_labels, dtype=np.int32)
    if seeds.shape != neurite_image.shape:
        raise ValueError("nuclear seeds and neurite image must share a shape")
    maximum_radius_px = settings.approximate_max_width / (2.0 * pixel_size_um)
    minimum_area_px = settings.minimum_area / pixel_size_um**2
    response = local_background_response(
        neurite_image,
        object_width_px=settings.approximate_max_width / pixel_size_um,
        bright_objects=bright_objects,
    )
    body_foreground = response >= settings.intensity_above_local_background
    foreground_distance = ndi.distance_transform_edt(body_foreground)
    bodies = np.zeros(seeds.shape, dtype=np.int32)
    connectivity = np.ones((3, 3), dtype=bool)
    maximum_radius_margin = int(np.ceil(maximum_radius_px))
    for seed_region in regionprops(seeds):
        owner = int(seed_region.label)
        minimum_row, minimum_column, maximum_row, maximum_column = seed_region.bbox
        owner_slice = (
            slice(
                max(0, minimum_row - maximum_radius_margin),
                min(seeds.shape[0], maximum_row + maximum_radius_margin),
            ),
            slice(
                max(0, minimum_column - maximum_radius_margin),
                min(seeds.shape[1], maximum_column + maximum_radius_margin),
            ),
        )
        local_seeds = seeds[owner_slice]
        seed = local_seeds == owner
        seed_coordinates = np.argwhere(seed)
        seed_center = seed_coordinates.mean(axis=0)
        seed_centroid = tuple(
            int(np.clip(round(value), 0, seed.shape[axis] - 1))
            for axis, value in enumerate(seed_center)
        )
        local_foreground_width = (
            2.0 * float(foreground_distance[owner_slice][seed_centroid]) - 1.0
        )
        if local_foreground_width > settings.approximate_max_width / pixel_size_um:
            continue
        distance_to_nearest_seed, nearest_seed_coordinates = ndi.distance_transform_edt(
            local_seeds == 0,
            return_indices=True,
        )
        nearest_seed = local_seeds[tuple(nearest_seed_coordinates)]
        local_body_foreground = body_foreground[owner_slice]
        rows, columns = np.ogrid[: seed.shape[0], : seed.shape[1]]
        distance_from_centroid_squared = (rows - seed_center[0]) ** 2 + (
            columns - seed_center[1]
        ) ** 2
        candidate = (
            (nearest_seed == owner)
            & (distance_from_centroid_squared <= maximum_radius_px**2)
            & (distance_to_nearest_seed <= maximum_radius_px)
            & local_body_foreground
        )
        components, component_count = ndi.label(candidate, structure=connectivity)
        if component_count == 0:
            continue
        overlapping_components = np.unique(components[seed])
        overlapping_components = overlapping_components[overlapping_components > 0]
        if not overlapping_components.size:
            continue
        component = min(
            (int(value) for value in overlapping_components),
            key=lambda value: (
                float(np.min(distance_from_centroid_squared[components == value])),
                value,
            ),
        )
        body = ndi.binary_fill_holes(components == component)
        if np.count_nonzero(body) < minimum_area_px:
            continue
        local_bodies = bodies[owner_slice]
        local_bodies[body] = owner

    # Later seeds can overwrite shared pixels after an earlier body passed the
    # area check. Reapply the public minimum-area contract to the final masks.
    final_areas = np.bincount(
        bodies.ravel(),
        minlength=int(seeds.max()) + 1,
    )
    keep = final_areas >= minimum_area_px
    keep[0] = False
    return np.where(keep[bodies], bodies, 0).astype(np.int32, copy=False)


def _repair_signal_supported_skeleton(
    labels: np.ndarray,
    signal_response: np.ndarray,
    owner_regions: np.ndarray,
    cell_body_labels: np.ndarray,
    *,
    minimum_response: float,
) -> np.ndarray:
    """Connect owned fragments only through continuous same-owner image evidence.

    Each owner starts at a point inside its cell body. A deterministic
    multi-source least-cost search may traverse that body, already accepted
    skeleton pixels, or pixels that both exceed the declared neurite-response
    threshold and belong to the owner's propagated region. Unsupported or
    foreign-owner fragments are removed instead of receiving inferred chords.
    """

    repaired = np.asarray(labels, dtype=np.int32).copy()
    response = np.asarray(signal_response, dtype=float)
    regions = np.asarray(owner_regions, dtype=np.int32)
    bodies = np.asarray(cell_body_labels, dtype=np.int32)
    if not repaired.shape == response.shape == regions.shape == bodies.shape:
        raise ValueError(
            "labels, signal_response, owner_regions, and cell_body_labels must "
            "have the same shape"
        )
    if not np.isfinite(minimum_response) or minimum_response < 0:
        raise ValueError("minimum_response must be finite and >= 0")

    connectivity = np.ones((3, 3), dtype=bool)
    owner_bounds: dict[int, list[tuple[int, int, int, int]]] = defaultdict(list)
    for owner_source in (repaired, regions, bodies):
        for owner_region in regionprops(owner_source):
            owner_bounds[int(owner_region.label)].append(owner_region.bbox)
    owners = sorted(int(region.label) for region in regionprops(repaired))
    for owner in owners:
        bounds = owner_bounds[owner]
        owner_slice = (
            slice(
                min(bound[0] for bound in bounds),
                max(bound[2] for bound in bounds),
            ),
            slice(
                min(bound[1] for bound in bounds),
                max(bound[3] for bound in bounds),
            ),
        )
        local_repaired = repaired[owner_slice].copy()
        local_response = response[owner_slice]
        local_regions = regions[owner_slice]
        local_bodies = bodies[owner_slice]
        body_mask = local_bodies == owner
        original_owner = (local_repaired == owner) & ~body_mask
        local_repaired[(local_repaired == owner) & body_mask] = 0
        if not np.any(original_owner):
            repaired[owner_slice] = local_repaired
            continue
        body_coordinates = np.argwhere(body_mask)
        if not len(body_coordinates):
            raise ValueError(
                f"Neurite topology owner {owner} has no corresponding cell body."
            )
        body_centroid = body_coordinates.mean(axis=0)
        soma_coordinate = tuple(
            int(value)
            for value in body_coordinates[
                np.argmin(np.sum((body_coordinates - body_centroid) ** 2, axis=1))
            ]
        )
        local_repaired[soma_coordinate] = owner
        occupied_by_other_owner = (local_repaired > 0) & (local_repaired != owner)
        signal_support = (local_response >= minimum_response) & (local_regions == owner)
        allowed = (
            signal_support | original_owner | body_mask
        ) & ~occupied_by_other_owner

        while True:
            components, _ = ndi.label(
                local_repaired == owner,
                structure=connectivity,
            )
            root_component = int(components[soma_coordinate])
            connected = components == root_component
            targets = original_owner & ~connected
            if not np.any(targets):
                break
            path = _least_cost_supported_path(
                allowed,
                local_response,
                connected,
                targets,
                preferred=(original_owner | body_mask),
                minimum_response=minimum_response,
            )
            if path is None:
                break
            local_repaired[tuple(path.T)] = owner

        components, _ = ndi.label(
            local_repaired == owner,
            structure=connectivity,
        )
        root_component = int(components[soma_coordinate])
        local_repaired[(local_repaired == owner) & (components != root_component)] = 0
        repaired[owner_slice] = local_repaired
    return repaired


def _least_cost_supported_path(
    allowed: np.ndarray,
    signal_response: np.ndarray,
    starts: np.ndarray,
    targets: np.ndarray,
    *,
    preferred: np.ndarray,
    minimum_response: float,
) -> np.ndarray | None:
    """Return one deterministic 8-connected path over accepted support pixels."""

    pixel_cost = np.full(allowed.shape, np.inf, dtype=float)
    if minimum_response > 0:
        supported_response = np.maximum(signal_response, minimum_response)
        pixel_cost[allowed] = 1.0 + (minimum_response / supported_response[allowed])
    else:
        pixel_cost[allowed] = 1.0
    pixel_cost[preferred & allowed] = 0.5

    start_coordinates = [
        tuple(int(value) for value in coordinate)
        for coordinate in np.argwhere(starts & allowed)
    ]
    target_coordinates = [
        tuple(int(value) for value in coordinate)
        for coordinate in np.argwhere(targets & allowed)
    ]
    if not start_coordinates or not target_coordinates:
        return None
    path_finder = MCP_Geometric(pixel_cost, fully_connected=True)
    cumulative_costs, _ = path_finder.find_costs(
        starts=start_coordinates,
        ends=target_coordinates,
        find_all_ends=False,
    )
    reachable_targets = [
        coordinate
        for coordinate in target_coordinates
        if np.isfinite(cumulative_costs[coordinate])
    ]
    if not reachable_targets:
        return None
    destination = min(
        reachable_targets,
        key=lambda coordinate: (cumulative_costs[coordinate], *coordinate),
    )
    return np.asarray(path_finder.traceback(destination), dtype=np.int32)


def _relabel(labels: np.ndarray, keep: np.ndarray) -> np.ndarray:
    mapping = np.zeros(len(keep), dtype=np.int32)
    kept_labels = np.flatnonzero(keep)
    mapping[kept_labels] = np.arange(1, len(kept_labels) + 1, dtype=np.int32)
    return mapping[labels]


def _remove_three_pixel_cycles(
    skeleton: np.ndarray,
    connectivity: np.ndarray,
) -> np.ndarray:
    """Remove endpoint-free three-pixel components that cannot encode a path."""

    component_labels, component_count = ndi.label(
        skeleton,
        structure=connectivity,
    )
    if component_count == 0:
        return skeleton

    component_sizes = np.bincount(component_labels.ravel())
    candidate_labels = np.flatnonzero(component_sizes == 3)
    candidate_labels = candidate_labels[candidate_labels != 0]
    if len(candidate_labels) == 0:
        return skeleton

    neighborhood = connectivity.copy()
    neighborhood[(1,) * skeleton.ndim] = False
    pixel_degrees = ndi.convolve(
        skeleton.astype(np.uint8, copy=False),
        neighborhood.astype(np.uint8, copy=False),
        mode="constant",
        cval=0,
    )
    cycle_labels = tuple(
        int(component_label)
        for component_label in candidate_labels
        if np.all(pixel_degrees[component_labels == component_label] == 2)
    )
    if not cycle_labels:
        return skeleton
    return skeleton & ~np.isin(component_labels, cycle_labels)


def _analyze_topology(
    skeleton: np.ndarray,
    cell_body_labels: np.ndarray,
    pixel_size_um: float,
    outgrowth_width_px: float,
    *,
    assigned_path_labels: np.ndarray | None = None,
) -> _TopologyResult:
    if (
        assigned_path_labels is not None
        and assigned_path_labels.shape != skeleton.shape
    ):
        raise ValueError(
            "assigned_path_labels must have the same shape as the skeleton"
        )
    # A neurite path requires an edge, not merely a foreground pixel. Skan's
    # full-neighborhood pixel graph has no paths for isolated vertices, and its
    # constructor builds the path CSR before exposing n_paths.
    connectivity = ndi.generate_binary_structure(skeleton.ndim, skeleton.ndim)
    neighborhood = connectivity.copy()
    neighborhood[(1,) * skeleton.ndim] = False
    skeleton = np.asarray(skeleton, dtype=bool) & ndi.binary_dilation(
        skeleton, structure=neighborhood
    )
    # Three mutually adjacent pixels form an endpoint-free cycle. They carry no
    # neurite path, and Skan 0.13 cannot construct a path CSR for that graph.
    skeleton = _remove_three_pixel_cycles(skeleton, connectivity)
    if not skeleton.any():
        return _empty_topology()

    skeleton_graph = Skeleton(skeleton, spacing=pixel_size_um)
    branch_table = summarize(skeleton_graph, separator="_").reset_index(drop=True)
    path_count = skeleton_graph.n_paths
    if path_count == 0:
        return _empty_topology()

    path_coordinates = tuple(
        np.asarray(skeleton_graph.path_coordinates(path_index), dtype=int)
        for path_index in range(path_count)
    )
    path_lengths = branch_table["branch_distance"].to_numpy(dtype=float)
    path_euclidean_lengths = branch_table["euclidean_distance"].to_numpy(dtype=float)
    node_incidence: dict[int, list[int]] = defaultdict(list)
    node_endpoints: dict[int, list[tuple[int, int]]] = defaultdict(list)
    node_coordinates: dict[int, np.ndarray] = {}
    path_endpoint_nodes: list[tuple[int, int]] = []
    for path_index, row in branch_table.iterrows():
        source = int(row["node_id_src"])
        destination = int(row["node_id_dst"])
        path_endpoint_nodes.append((source, destination))
        node_incidence[source].append(path_index)
        node_incidence[destination].append(path_index)
        node_endpoints[source].append((path_index, 0))
        node_endpoints[destination].append((path_index, 1))
        node_coordinates[source] = np.array(
            [row["image_coord_src_0"], row["image_coord_src_1"]], dtype=float
        )
        node_coordinates[destination] = np.array(
            [row["image_coord_dst_0"], row["image_coord_dst_1"]], dtype=float
        )

    transitions: dict[int, set[int]] = {
        path_index: set() for path_index in range(path_count)
    }
    branch_nodes: set[int] = set()
    crossing_nodes: set[int] = set()
    path_endpoint_groups = [[0, 0] for _ in range(path_count)]
    endpoint_group_coordinates: dict[int, tuple[float, float]] = {}
    next_endpoint_group = 1
    lookahead = max(2, int(np.ceil(outgrowth_width_px)))
    junction_nodes = {
        node
        for node, incident_paths in node_incidence.items()
        if len(set(incident_paths)) >= 3
    }
    crossing_clusters: dict[
        int,
        tuple[
            tuple[tuple[tuple[int, int], tuple[int, int]], ...],
            tuple[tuple[int, int], ...],
        ],
    ] = {}
    crossing_cluster_nodes: set[int] = set()
    crossing_core_paths: set[int] = set()
    crossing_paths_by_node: dict[int, tuple[int, ...]] = {}
    crossing_core_paths_by_node: dict[int, tuple[int, ...]] = {}
    for cluster in _junction_node_clusters(
        junction_nodes,
        path_endpoint_nodes,
        path_lengths,
        maximum_internal_length=(
            max(1.0, np.sqrt(2.0) * outgrowth_width_px) * pixel_size_um
        ),
    ):
        external_endpoints = tuple(
            sorted(
                endpoint
                for node in cluster
                for endpoint in node_endpoints[node]
                if path_endpoint_nodes[endpoint[0]][1 - endpoint[1]] not in cluster
            )
        )
        crossing_pairs = _crossing_pairs(
            external_endpoints,
            path_coordinates,
            lookahead,
        )
        if crossing_pairs is None:
            continue
        internal_paths = tuple(
            sorted(
                path_index
                for path_index, (source, destination) in enumerate(path_endpoint_nodes)
                if source in cluster and destination in cluster
            )
        )
        internal_endpoints = tuple(
            (path_index, endpoint_index)
            for path_index in internal_paths
            for endpoint_index in (0, 1)
        )
        anchor = min(cluster)
        crossing_clusters[anchor] = (crossing_pairs, internal_endpoints)
        crossing_cluster_nodes.update(cluster)
        crossing_core_paths.update(internal_paths)
        crossing_paths_by_node[anchor] = tuple(
            sorted({path_index for path_index, _ in external_endpoints})
        )
        crossing_core_paths_by_node[anchor] = internal_paths

    for node in sorted(node_incidence):
        if node in crossing_clusters:
            crossing_nodes.add(node)
            crossing_pairs, internal_endpoints = crossing_clusters[node]
            endpoint_groups = crossing_pairs + tuple(
                (endpoint,) for endpoint in internal_endpoints
            )
        elif node in crossing_cluster_nodes:
            continue
        else:
            incident_paths = node_incidence[node]
            unique_paths = sorted(set(incident_paths))
            if len(unique_paths) >= 3:
                branch_nodes.add(node)
            endpoint_groups = (tuple(node_endpoints[node]),)

        for endpoint_group in endpoint_groups:
            group_id = next_endpoint_group
            next_endpoint_group += 1
            group_paths = sorted({path_index for path_index, _ in endpoint_group})
            for path_index, endpoint_index in endpoint_group:
                path_endpoint_groups[path_index][endpoint_index] = group_id
            endpoint_coordinates = np.asarray(
                [
                    path_coordinates[path_index][0 if endpoint_index == 0 else -1]
                    for path_index, endpoint_index in endpoint_group
                ],
                dtype=float,
            )
            coordinate = endpoint_coordinates.mean(axis=0)
            endpoint_group_coordinates[group_id] = tuple(
                float(value) for value in coordinate
            )
            for first, second in combinations(group_paths, 2):
                transitions[first].add(second)
                transitions[second].add(first)

    expanded_bodies = expand_labels(
        cell_body_labels,
        distance=max(1, int(np.ceil(outgrowth_width_px)) + 2),
    )
    root_labels_by_path: dict[int, tuple[int, ...]] = {}
    for path_index, coordinates in enumerate(path_coordinates):
        labels = expanded_bodies[tuple(coordinates.T)]
        labels = labels[labels > 0]
        if labels.size:
            counts = Counter(int(label) for label in labels)
            root_labels_by_path[path_index] = tuple(
                label for label, _ in counts.most_common()
            )

    path_owners, path_distances = _propagate_path_owners(
        path_lengths,
        transitions,
        root_labels_by_path,
    )
    if crossing_core_paths:
        path_owners[list(crossing_core_paths)] = 0
        path_distances[list(crossing_core_paths)] = np.inf
    if assigned_path_labels is not None:
        for path_index, coordinates in enumerate(path_coordinates):
            if path_index in crossing_core_paths:
                continue
            labels = assigned_path_labels[tuple(coordinates.T)]
            labels = labels[labels > 0]
            if labels.size:
                path_owners[path_index] = Counter(
                    int(label) for label in labels
                ).most_common(1)[0][0]

    # Geometric pairing is only provisional until nominal ownership is known.
    # When same-owner arms were placed in different geometric pairs, connect
    # those arms and give their endpoints one owner-qualified node identity.
    # Two arms remain a crossover path; three or more arms are a branch for
    # that owner. This prevents an apparent crossing from silently severing a
    # soma-rooted neurite that the preceding ownership stage already proved.
    crossing_branch_owners: dict[int, set[int]] = defaultdict(set)
    for node, (crossing_pairs, _) in crossing_clusters.items():
        endpoints_by_owner: dict[int, list[tuple[int, int]]] = defaultdict(list)
        for endpoint in (endpoint for pair in crossing_pairs for endpoint in pair):
            owner = int(path_owners[endpoint[0]])
            if owner > 0:
                endpoints_by_owner[owner].append(endpoint)
        for owner, endpoints in endpoints_by_owner.items():
            endpoint_groups = {
                path_endpoint_groups[path_index][endpoint_index]
                for path_index, endpoint_index in endpoints
            }
            if len(endpoint_groups) <= 1:
                continue
            owner_paths = sorted({path_index for path_index, _ in endpoints})
            for first, second in combinations(owner_paths, 2):
                transitions[first].add(second)
                transitions[second].add(first)
            merged_group = min(endpoint_groups)
            for path_index, endpoint_index in endpoints:
                path_endpoint_groups[path_index][endpoint_index] = merged_group
            if len(owner_paths) >= 3:
                branch_nodes.add(node)
                crossing_branch_owners[node].add(owner)
    roots_by_cell: dict[int, list[int]] = defaultdict(list)
    for path_index, labels in root_labels_by_path.items():
        owner = int(path_owners[path_index])
        if owner > 0 and owner in labels:
            roots_by_cell[owner].append(path_index)
    _retain_soma_rooted_path_owners(
        path_owners,
        path_distances,
        transitions,
        roots_by_cell,
    )
    path_branch_types = _owner_qualified_path_branch_types(
        path_owners,
        path_endpoint_groups,
        crossing_core_paths,
    )

    branch_nodes_by_cell: dict[int, list[int]] = defaultdict(list)
    for node in branch_nodes:
        owned_degrees = Counter(
            int(path_owners[path_index])
            for path_index in set(node_incidence[node])
            if path_owners[path_index] > 0
        )
        for owner, degree in owned_degrees.items():
            if degree >= 3:
                branch_nodes_by_cell[owner].append(node)

    active_crossing_paths_by_node: dict[int, tuple[int, ...]] = {}
    for node in crossing_nodes:
        owner_counts = Counter(
            int(path_owners[path_index])
            for path_index in crossing_paths_by_node[node]
            if path_owners[path_index] > 0
        )
        active_owners = {
            owner
            for owner, path_count in owner_counts.items()
            if path_count == 2 and owner not in crossing_branch_owners[node]
        }
        active_crossing_paths_by_node[node] = tuple(
            path_index
            for path_index in crossing_paths_by_node[node]
            if path_owners[path_index] in active_owners
        )
    used_crossings = {
        node for node, paths in active_crossing_paths_by_node.items() if paths
    }
    return _TopologyResult(
        path_owners=path_owners,
        path_distances=path_distances,
        path_lengths=path_lengths,
        path_euclidean_lengths=path_euclidean_lengths,
        path_coordinates=path_coordinates,
        path_endpoint_groups=tuple(
            tuple(endpoint_groups) for endpoint_groups in path_endpoint_groups
        ),
        path_branch_types=path_branch_types,
        endpoint_group_coordinates=endpoint_group_coordinates,
        transitions={key: tuple(sorted(value)) for key, value in transitions.items()},
        root_paths_by_cell={
            cell: tuple(sorted(set(paths))) for cell, paths in roots_by_cell.items()
        },
        branch_nodes_by_cell={
            owner: _merge_nearby_nodes(
                nodes,
                node_coordinates,
                radius=max(1.0, outgrowth_width_px),
            )
            for owner, nodes in branch_nodes_by_cell.items()
        },
        crossing_nodes=frozenset(used_crossings),
        crossing_paths=frozenset(
            path_index
            for node in used_crossings
            for path_index in active_crossing_paths_by_node[node]
        ),
        crossing_core_paths=frozenset(
            path_index
            for node in used_crossings
            for path_index in crossing_core_paths_by_node[node]
        ),
    )


def _analyze_owned_topology(
    owner_skeleton: np.ndarray,
    cell_body_labels: np.ndarray,
    pixel_size_um: float,
    outgrowth_width_px: float,
    *,
    shared_crossing_mask: np.ndarray | None = None,
) -> _TopologyResult:
    """Analyze each nominal owner without erasing ownership at shared borders.

    A binary union of all owned skeletons reconnects adjacent pixels belonging
    to different neurons. Assigning that union back to one owner per Skan path
    then discards valid segments by majority vote. Each owner is therefore
    analyzed within its own bounded spatial crop and the resulting topologies
    are combined only after their nominal identity has been preserved.
    """

    owned = np.asarray(owner_skeleton, dtype=np.int32)
    bodies = np.asarray(cell_body_labels, dtype=np.int32)
    if owned.shape != bodies.shape:
        raise ValueError("owner_skeleton and cell_body_labels must have the same shape")
    crossing_mask = (
        np.zeros(owned.shape, dtype=bool)
        if shared_crossing_mask is None
        else np.asarray(shared_crossing_mask, dtype=bool)
    )
    if crossing_mask.shape != owned.shape:
        raise ValueError(
            "shared_crossing_mask and owner_skeleton must have the same shape"
        )
    if not np.any(owned > 0):
        return _empty_topology()

    body_regions = {int(region.label): region for region in regionprops(bodies)}
    owned_regions = {int(region.label): region for region in regionprops(owned)}
    margin = max(1, int(np.ceil(outgrowth_width_px)) + 2)
    connectivity = np.ones((3, 3), dtype=bool)
    crossing_components, crossing_component_count = ndi.label(
        crossing_mask,
        structure=connectivity,
    )
    shared_crossings_by_owner: dict[int, set[int]] = defaultdict(set)
    for component in range(1, crossing_component_count + 1):
        component_mask = crossing_components == component
        adjacent = (
            ndi.binary_dilation(
                component_mask,
                structure=connectivity,
            )
            & ~component_mask
        )
        for owner in np.unique(owned[adjacent]):
            if owner > 0:
                shared_crossings_by_owner[int(owner)].add(component)

    path_owners: list[np.ndarray] = []
    path_distances: list[np.ndarray] = []
    path_lengths: list[np.ndarray] = []
    path_euclidean_lengths: list[np.ndarray] = []
    path_coordinates: list[np.ndarray] = []
    path_endpoint_groups: list[tuple[int, int]] = []
    path_branch_types: list[np.ndarray] = []
    endpoint_group_coordinates: dict[int, tuple[float, float]] = {}
    transitions: dict[int, tuple[int, ...]] = {}
    root_paths_by_cell: dict[int, tuple[int, ...]] = {}
    branch_nodes_by_cell: dict[int, tuple[int, ...]] = {}
    crossing_nodes: set[int] = set()
    crossing_paths: set[int] = set()
    crossing_core_paths: set[int] = set()
    path_offset = 0
    endpoint_group_offset = 0
    node_offset = 0

    for owner in sorted(owned_regions):
        owned_region = owned_regions[owner]
        bounds = [owned_region.bbox]
        body_region = body_regions.get(owner)
        if body_region is not None:
            bounds.append(body_region.bbox)
        owner_slice = (
            slice(
                max(0, min(bound[0] for bound in bounds) - margin),
                min(owned.shape[0], max(bound[2] for bound in bounds) + margin),
            ),
            slice(
                max(0, min(bound[1] for bound in bounds) - margin),
                min(owned.shape[1], max(bound[3] for bound in bounds) + margin),
            ),
        )
        local_owner_mask = owned[owner_slice] == owner
        owner_crossings = shared_crossings_by_owner.get(owner, set())
        if owner_crossings:
            local_owner_mask |= np.isin(
                crossing_components[owner_slice],
                tuple(sorted(owner_crossings)),
            )
        local_owned = np.where(local_owner_mask, owner, 0).astype(
            np.int32,
            copy=False,
        )
        local = _analyze_topology(
            local_owned > 0,
            bodies[owner_slice],
            pixel_size_um,
            outgrowth_width_px,
            assigned_path_labels=local_owned,
        )
        local_path_count = len(local.path_owners)
        if local_path_count == 0:
            continue

        spatial_offset = np.array(
            [owner_slice[0].start, owner_slice[1].start],
            dtype=int,
        )
        path_owners.append(local.path_owners)
        path_distances.append(local.path_distances)
        path_lengths.append(local.path_lengths)
        path_euclidean_lengths.append(local.path_euclidean_lengths)
        path_coordinates.extend(
            coordinates + spatial_offset for coordinates in local.path_coordinates
        )
        path_branch_types.append(local.path_branch_types)

        local_group_ids = set(local.endpoint_group_coordinates)
        group_mapping = {
            group_id: group_id + endpoint_group_offset for group_id in local_group_ids
        }
        path_endpoint_groups.extend(
            tuple(group_mapping[group_id] for group_id in groups)
            for groups in local.path_endpoint_groups
        )
        endpoint_group_coordinates.update(
            {
                group_mapping[group_id]: tuple(
                    coordinate + spatial_offset[axis]
                    for axis, coordinate in enumerate(coordinates)
                )
                for group_id, coordinates in local.endpoint_group_coordinates.items()
            }
        )
        transitions.update(
            {
                path_index
                + path_offset: tuple(neighbor + path_offset for neighbor in neighbors)
                for path_index, neighbors in local.transitions.items()
            }
        )
        for cell, roots in local.root_paths_by_cell.items():
            root_paths_by_cell[int(cell)] = tuple(root + path_offset for root in roots)

        local_node_ids = set(local.crossing_nodes)
        local_node_ids.update(
            node for nodes in local.branch_nodes_by_cell.values() for node in nodes
        )
        branch_nodes_by_cell.update(
            {
                int(cell): tuple(node + node_offset for node in nodes)
                for cell, nodes in local.branch_nodes_by_cell.items()
            }
        )
        crossing_nodes.update(node + node_offset for node in local.crossing_nodes)
        crossing_paths.update(
            path_index + path_offset for path_index in local.crossing_paths
        )
        crossing_core_paths.update(
            path_index + path_offset for path_index in local.crossing_core_paths
        )

        path_offset += local_path_count
        if local_group_ids:
            endpoint_group_offset += max(local_group_ids)
        if local_node_ids:
            node_offset += max(local_node_ids) + 1

    if not path_owners:
        return _empty_topology()
    return _TopologyResult(
        path_owners=np.concatenate(path_owners),
        path_distances=np.concatenate(path_distances),
        path_lengths=np.concatenate(path_lengths),
        path_euclidean_lengths=np.concatenate(path_euclidean_lengths),
        path_coordinates=tuple(path_coordinates),
        path_endpoint_groups=tuple(path_endpoint_groups),
        path_branch_types=np.concatenate(path_branch_types),
        endpoint_group_coordinates=endpoint_group_coordinates,
        transitions=transitions,
        root_paths_by_cell=root_paths_by_cell,
        branch_nodes_by_cell=branch_nodes_by_cell,
        crossing_nodes=frozenset(crossing_nodes),
        crossing_paths=frozenset(crossing_paths),
        crossing_core_paths=frozenset(crossing_core_paths),
    )


def _merge_nearby_nodes(
    nodes: Sequence[int],
    node_coordinates: Mapping[int, np.ndarray],
    *,
    radius: float,
) -> tuple[int, ...]:
    """Collapse multi-pixel junction neighborhoods into one branch event."""

    remaining = set(nodes)
    merged: list[int] = []
    while remaining:
        seed = min(remaining)
        cluster = {seed}
        frontier = [seed]
        remaining.remove(seed)
        while frontier:
            current = frontier.pop()
            nearby = {
                candidate
                for candidate in remaining
                if np.linalg.norm(
                    node_coordinates[current] - node_coordinates[candidate]
                )
                <= radius
            }
            remaining.difference_update(nearby)
            cluster.update(nearby)
            frontier.extend(nearby)
        merged.append(min(cluster))
    return tuple(merged)


def _empty_topology() -> _TopologyResult:
    return _TopologyResult(
        path_owners=np.zeros(0, dtype=np.int32),
        path_distances=np.zeros(0, dtype=float),
        path_lengths=np.zeros(0, dtype=float),
        path_euclidean_lengths=np.zeros(0, dtype=float),
        path_coordinates=(),
        path_endpoint_groups=(),
        path_branch_types=np.zeros(0, dtype=np.int32),
        endpoint_group_coordinates={},
        transitions={},
        root_paths_by_cell={},
        branch_nodes_by_cell={},
        crossing_nodes=frozenset(),
        crossing_paths=frozenset(),
        crossing_core_paths=frozenset(),
    )


def _crossing_pairs(
    incident_endpoints: Sequence[tuple[int, int]],
    path_coordinates: Sequence[np.ndarray],
    lookahead: int,
) -> (
    tuple[
        tuple[tuple[int, int], tuple[int, int]],
        tuple[tuple[int, int], tuple[int, int]],
    ]
    | None
):
    if len(incident_endpoints) != 4:
        return None

    directions = []
    for path_index, endpoint_index in incident_endpoints:
        coordinates = path_coordinates[path_index]
        if len(coordinates) < 2:
            return None
        source_side = endpoint_index == 0
        node_coordinate = coordinates[0] if source_side else coordinates[-1]
        sample_index = min(lookahead, len(coordinates) - 1)
        sample_coordinate = (
            coordinates[sample_index] if source_side else coordinates[-sample_index - 1]
        )
        vector = sample_coordinate.astype(float) - node_coordinate.astype(float)
        norm = np.linalg.norm(vector)
        if norm == 0:
            return None
        directions.append(vector / norm)

    pairings = (
        ((0, 1), (2, 3)),
        ((0, 2), (1, 3)),
        ((0, 3), (1, 2)),
    )
    scored_pairings = []
    for pairing in pairings:
        opposite_scores = tuple(
            -float(np.dot(directions[first], directions[second]))
            for first, second in pairing
        )
        scored_pairings.append((min(opposite_scores), sum(opposite_scores), pairing))

    minimum_score, _, best_pairing = max(scored_pairings)
    if minimum_score < np.cos(np.deg2rad(30.0)):
        return None
    return tuple(
        (incident_endpoints[first], incident_endpoints[second])
        for first, second in best_pairing
    )  # type: ignore[return-value]


def _junction_node_clusters(
    junction_nodes: set[int],
    path_endpoint_nodes: Sequence[tuple[int, int]],
    path_lengths: np.ndarray,
    *,
    maximum_internal_length: float,
) -> tuple[frozenset[int], ...]:
    """Group junction pixels joined within one declared neurite width."""

    neighbors: dict[int, set[int]] = {node: set() for node in junction_nodes}
    for path_index, (source, destination) in enumerate(path_endpoint_nodes):
        if (
            source != destination
            and source in junction_nodes
            and destination in junction_nodes
            and path_lengths[path_index] <= maximum_internal_length
        ):
            neighbors[source].add(destination)
            neighbors[destination].add(source)

    remaining = set(junction_nodes)
    clusters = []
    while remaining:
        seed = min(remaining)
        cluster = {seed}
        frontier = [seed]
        remaining.remove(seed)
        while frontier:
            current = frontier.pop()
            adjacent = neighbors[current] & remaining
            remaining.difference_update(adjacent)
            cluster.update(adjacent)
            frontier.extend(sorted(adjacent, reverse=True))
        clusters.append(frozenset(cluster))
    return tuple(clusters)


def _retain_soma_rooted_path_owners(
    path_owners: np.ndarray,
    path_distances: np.ndarray,
    transitions: Mapping[int, Iterable[int]],
    roots_by_cell: Mapping[int, Sequence[int]],
) -> None:
    """Discard assigned path labels outside their logical soma component."""

    rooted_paths: set[int] = set()
    for owner, roots in roots_by_cell.items():
        frontier = list(roots)
        while frontier:
            path_index = frontier.pop()
            if path_index in rooted_paths or path_owners[path_index] != owner:
                continue
            rooted_paths.add(path_index)
            frontier.extend(transitions[path_index])
    detached_paths = [
        path_index
        for path_index, owner in enumerate(path_owners)
        if owner > 0 and path_index not in rooted_paths
    ]
    if detached_paths:
        path_owners[detached_paths] = 0
        path_distances[detached_paths] = np.inf


def _owner_qualified_path_branch_types(
    path_owners: np.ndarray,
    path_endpoint_groups: Sequence[Sequence[int]],
    crossing_core_paths: set[int],
) -> np.ndarray:
    """Classify paths from final owner-specific logical endpoint degrees."""

    endpoint_degrees = Counter(
        (int(path_owners[path_index]), group_id)
        for path_index, endpoint_groups in enumerate(path_endpoint_groups)
        if path_owners[path_index] > 0 and path_index not in crossing_core_paths
        for group_id in endpoint_groups
    )
    branch_types = np.zeros(len(path_owners), dtype=np.int32)
    for path_index, endpoint_groups in enumerate(path_endpoint_groups):
        owner = int(path_owners[path_index])
        if owner <= 0 or path_index in crossing_core_paths:
            continue
        source_group, destination_group = endpoint_groups
        if source_group == destination_group:
            branch_types[path_index] = 3
            continue
        branch_types[path_index] = sum(
            endpoint_degrees[owner, group_id] >= 3 for group_id in endpoint_groups
        )
    return branch_types


def _propagate_path_owners(
    path_lengths: np.ndarray,
    transitions: Mapping[int, Iterable[int]],
    root_labels_by_path: Mapping[int, Sequence[int]],
) -> tuple[np.ndarray, np.ndarray]:
    path_owners = np.zeros(len(path_lengths), dtype=np.int32)
    distances = np.full(len(path_lengths), np.inf, dtype=float)
    queue: list[tuple[float, int, int]] = []
    for path_index, labels in root_labels_by_path.items():
        for label in labels:
            heapq.heappush(queue, (0.0, int(label), path_index))

    while queue:
        distance, owner, path_index = heapq.heappop(queue)
        if distance > distances[path_index]:
            continue
        if distance == distances[path_index] and path_owners[path_index] <= owner:
            continue
        distances[path_index] = distance
        path_owners[path_index] = owner
        for neighbor in transitions[path_index]:
            neighbor_distance = distance + 0.5 * (
                path_lengths[path_index] + path_lengths[neighbor]
            )
            if neighbor_distance <= distances[neighbor]:
                heapq.heappush(queue, (neighbor_distance, owner, neighbor))
    return path_owners, distances


def _build_neurite_morphology_graph(
    topology: _TopologyResult,
    cell_body_labels: np.ndarray,
    *,
    pixel_size_um: float,
    outgrowth_width_px: float,
) -> SpatialGraph:
    """Project owned Skan paths into deterministic soma-rooted forests."""

    paths_by_owner: dict[int, list[int]] = defaultdict(list)
    for path_index, owner in enumerate(topology.path_owners):
        if path_index in topology.crossing_core_paths:
            continue
        if owner > 0:
            paths_by_owner[int(owner)].append(path_index)

    graph_nodes: list[SpatialGraphNode] = []
    graph_edges: list[SpatialGraphEdge] = []
    next_node_id = 1
    next_edge_id = 1
    process_radius_um = max(
        pixel_size_um / 2.0,
        outgrowth_width_px * pixel_size_um / 2.0,
    )
    body_regions = {
        int(region.label): region for region in regionprops(cell_body_labels)
    }

    for owner in sorted(paths_by_owner):
        owner_paths = tuple(sorted(paths_by_owner[owner]))
        adjacency: dict[int, list[tuple[int, int]]] = defaultdict(list)
        for path_index in owner_paths:
            first_group, second_group = topology.path_endpoint_groups[path_index]
            adjacency[first_group].append((path_index, second_group))
            adjacency[second_group].append((path_index, first_group))
        for incident_paths in adjacency.values():
            incident_paths.sort()

        try:
            body_region = body_regions[owner]
        except KeyError as error:
            raise ValueError(
                f"Neurite topology owner {owner} has no corresponding cell body."
            ) from error
        body_coordinates = body_region.coords
        body_centroid = body_coordinates.mean(axis=0)
        soma_coordinate = tuple(
            float(value)
            for value in body_coordinates[
                np.argmin(np.sum((body_coordinates - body_centroid) ** 2, axis=1))
            ]
        )
        body_area_um2 = float(body_region.area) * pixel_size_um**2
        soma_tree = cKDTree(body_coordinates)
        soma_radius_um = max(
            process_radius_um,
            float(np.sqrt(body_area_um2 / np.pi)),
        )
        primary_root_group = min(
            adjacency,
            key=lambda group_id: (
                sum(
                    (
                        topology.endpoint_group_coordinates[group_id][axis]
                        - soma_coordinate[axis]
                    )
                    ** 2
                    for axis in range(2)
                ),
                group_id,
            ),
        )
        remaining_groups = set(adjacency)

        while remaining_groups:
            component_seed = min(remaining_groups)
            component_groups: set[int] = set()
            component_paths: set[int] = set()
            frontier = [component_seed]
            while frontier:
                group_id = frontier.pop()
                if group_id in component_groups:
                    continue
                component_groups.add(group_id)
                for path_index, neighbor_group in adjacency[group_id]:
                    component_paths.add(path_index)
                    if neighbor_group not in component_groups:
                        frontier.append(neighbor_group)
            remaining_groups.difference_update(component_groups)

            root_group = min(
                component_groups,
                key=lambda group_id: (
                    sum(
                        (
                            topology.endpoint_group_coordinates[group_id][axis]
                            - soma_coordinate[axis]
                        )
                        ** 2
                        for axis in range(2)
                    ),
                    group_id,
                ),
            )
            is_soma_component = root_group == primary_root_group
            root_coordinate = topology.endpoint_group_coordinates[root_group]
            root_index = tuple(
                int(np.clip(round(value), 0, cell_body_labels.shape[axis] - 1))
                for axis, value in enumerate(root_coordinate)
            )
            root_inside_soma = cell_body_labels[root_index] == owner
            soma_attachment_distance = max(
                1.0,
                outgrowth_width_px / 2.0 + 0.5,
            )
            root_touches_soma = any(
                np.any(
                    soma_tree.query(
                        topology.path_coordinates[path_index],
                        distance_upper_bound=soma_attachment_distance,
                    )[0]
                    <= soma_attachment_distance
                )
                for path_index in component_paths
            )
            soma_connected = root_inside_soma or root_touches_soma
            if root_inside_soma and is_soma_component:
                root_role = "soma_root"
            elif root_touches_soma:
                root_role = "soma_attachment_root"
            else:
                root_role = "disconnected_root"
            root_node = SpatialGraphNode.from_features(
                node_id=next_node_id,
                coordinates=root_coordinate,
                radius=(
                    soma_radius_um if root_role == "soma_root" else process_radius_um
                ),
                features={
                    "label": owner,
                    "neuron_label": owner,
                    "node_role": root_role,
                },
            )
            next_node_id += 1
            graph_nodes.append(root_node)
            nodes_by_group: dict[int, SpatialGraphNode] = {root_group: root_node}
            for group_id in sorted(component_groups):
                if group_id == root_group:
                    continue
                node = SpatialGraphNode.from_features(
                    node_id=next_node_id,
                    coordinates=topology.endpoint_group_coordinates[group_id],
                    radius=process_radius_um,
                    features={
                        "label": owner,
                        "neuron_label": owner,
                        "node_role": "neurite",
                    },
                )
                next_node_id += 1
                graph_nodes.append(node)
                nodes_by_group[group_id] = node

            node_distances = {root_group: 0.0}
            visited_groups = {root_group}
            emitted_paths: set[int] = set()
            candidate_edges: list[tuple[float, int, int, int]] = []

            def enqueue_from(group_id: int) -> None:
                for path_index, neighbor_group in adjacency[group_id]:
                    if path_index not in component_paths:
                        continue
                    candidate_distance = node_distances[group_id] + float(
                        topology.path_lengths[path_index]
                    )
                    heapq.heappush(
                        candidate_edges,
                        (
                            candidate_distance,
                            path_index,
                            group_id,
                            neighbor_group,
                        ),
                    )

            enqueue_from(root_group)
            while candidate_edges:
                (
                    target_distance,
                    path_index,
                    source_group,
                    target_group,
                ) = heapq.heappop(candidate_edges)
                if path_index in emitted_paths:
                    continue

                endpoint_groups = topology.path_endpoint_groups[path_index]
                coordinates = np.asarray(
                    topology.path_coordinates[path_index],
                    dtype=float,
                ).copy()
                if endpoint_groups != (source_group, target_group):
                    coordinates = coordinates[::-1]
                coordinates[0] = nodes_by_group[source_group].coordinates
                target_is_cycle_break = target_group in visited_groups
                if target_is_cycle_break:
                    target_node = SpatialGraphNode.from_features(
                        node_id=next_node_id,
                        coordinates=coordinates[-1],
                        radius=process_radius_um,
                        features={
                            "label": owner,
                            "neuron_label": owner,
                            "node_role": "cycle_break",
                        },
                    )
                    next_node_id += 1
                    graph_nodes.append(target_node)
                else:
                    visited_groups.add(target_group)
                    node_distances[target_group] = target_distance
                    target_node = nodes_by_group[target_group]
                    coordinates[-1] = target_node.coordinates
                branch_distance_um = float(topology.path_lengths[path_index])
                euclidean_distance_um = float(
                    topology.path_euclidean_lengths[path_index]
                )
                graph_edges.append(
                    SpatialGraphEdge.from_features(
                        edge_id=next_edge_id,
                        source=nodes_by_group[source_group],
                        target=target_node,
                        coordinates=coordinates,
                        features={
                            "label": owner,
                            "neuron_label": owner,
                            "branch_distance_um": branch_distance_um,
                            "euclidean_distance_um": euclidean_distance_um,
                            "tortuosity": (
                                max(
                                    1.0,
                                    branch_distance_um / euclidean_distance_um,
                                )
                                if euclidean_distance_um > 0
                                else 0.0
                            ),
                            "distance_from_soma_um": (
                                node_distances[source_group]
                                if soma_connected
                                else float("nan")
                            ),
                            "branch_type": int(topology.path_branch_types[path_index]),
                        },
                    )
                )
                next_edge_id += 1
                emitted_paths.add(path_index)
                if not target_is_cycle_break:
                    enqueue_from(target_group)

    graph = SpatialGraph(
        name=NEURITE_MORPHOLOGY_OUTPUT.name,
        nodes=tuple(graph_nodes),
        edges=tuple(graph_edges),
        coordinate_spacing=(pixel_size_um, pixel_size_um),
    )
    graph.require_directed_forest()
    return graph


def _in_body_soma_coordinate(
    cell_body_labels: np.ndarray,
    owner: int,
) -> tuple[float, float]:
    owner_coordinates = np.argwhere(cell_body_labels == owner)
    if not len(owner_coordinates):
        raise ValueError(
            f"Neurite topology owner {owner} has no corresponding cell body."
        )
    centroid = owner_coordinates.mean(axis=0)
    soma_index = int(np.argmin(np.sum((owner_coordinates - centroid) ** 2, axis=1)))
    return tuple(float(value) for value in owner_coordinates[soma_index])


def _render_owned_skeleton(
    shape: tuple[int, int],
    topology: _TopologyResult,
) -> np.ndarray:
    owner_skeleton = np.zeros(shape, dtype=np.int32)
    for path_index, coordinates in enumerate(topology.path_coordinates):
        owner = int(topology.path_owners[path_index])
        if owner > 0:
            empty = owner_skeleton[tuple(coordinates.T)] == 0
            owner_skeleton[tuple(coordinates[empty].T)] = owner
    return owner_skeleton


def _render_topology_path_mask(
    shape: tuple[int, int],
    topology: _TopologyResult,
) -> np.ndarray:
    """Render every graph path independently of its final rooted owner."""

    path_mask = np.zeros(shape, dtype=bool)
    for coordinates in topology.path_coordinates:
        path_mask[tuple(coordinates.T)] = True
    return path_mask


def _physically_soma_rooted_owner_mask(
    owner_skeleton: np.ndarray,
    cell_body_labels: np.ndarray,
    *,
    maximum_root_distance: int,
) -> np.ndarray:
    """Mark same-owner pixel components that reach their soma neighborhood."""

    owned = np.asarray(owner_skeleton, dtype=np.int32)
    bodies = np.asarray(cell_body_labels, dtype=np.int32)
    if owned.shape != bodies.shape:
        raise ValueError("owner_skeleton and cell_body_labels must have the same shape")
    if maximum_root_distance < 0:
        raise ValueError("maximum_root_distance must be >= 0")

    expanded_bodies = expand_labels(bodies, distance=maximum_root_distance)
    connectivity = np.ones((3, 3), dtype=bool)
    rooted = np.zeros(owned.shape, dtype=bool)
    body_regions = {int(region.label): region for region in regionprops(bodies)}
    for owner_region in regionprops(owned):
        owner = int(owner_region.label)
        bounds = [owner_region.bbox]
        body_region = body_regions.get(owner)
        if body_region is not None:
            bounds.append(body_region.bbox)
        owner_slice = (
            slice(
                max(0, min(bound[0] for bound in bounds) - maximum_root_distance),
                min(
                    owned.shape[0],
                    max(bound[2] for bound in bounds) + maximum_root_distance,
                ),
            ),
            slice(
                max(0, min(bound[1] for bound in bounds) - maximum_root_distance),
                min(
                    owned.shape[1],
                    max(bound[3] for bound in bounds) + maximum_root_distance,
                ),
            ),
        )
        local_components, _ = ndi.label(
            owned[owner_slice] == owner,
            structure=connectivity,
        )
        root_components = np.unique(
            local_components[expanded_bodies[owner_slice] == owner]
        )
        root_components = root_components[root_components > 0]
        if root_components.size:
            rooted[owner_slice] |= np.isin(local_components, root_components)
    return rooted


def _render_crossing_support(
    shape: tuple[int, int],
    topology: _TopologyResult,
) -> np.ndarray:
    """Render rooted crossover arms plus a temporary physical core."""

    support = np.zeros(shape, dtype=np.int32)
    for path_index in sorted(topology.crossing_paths):
        owner = int(topology.path_owners[path_index])
        if owner <= 0:
            continue
        coordinates = topology.path_coordinates[path_index]
        empty = support[tuple(coordinates.T)] == 0
        support[tuple(coordinates[empty].T)] = owner
    if not np.any(support) or not topology.crossing_core_paths:
        return support

    _, nearest = ndi.distance_transform_edt(
        support == 0,
        return_indices=True,
    )
    nearest_owner = support[tuple(nearest)]
    for path_index in sorted(topology.crossing_core_paths):
        coordinates = topology.path_coordinates[path_index]
        support[tuple(coordinates.T)] = nearest_owner[tuple(coordinates.T)]
    return support


def _render_crossing_core_mask(
    shape: tuple[int, int],
    topology: _TopologyResult,
) -> np.ndarray:
    """Render physical pixels shared by the resolved logical crossing paths."""

    crossing_core = np.zeros(shape, dtype=bool)
    for path_index in topology.crossing_core_paths:
        coordinates = topology.path_coordinates[path_index]
        crossing_core[tuple(coordinates.T)] = True
    return crossing_core


def _count_multi_owner_crossings(
    crossing_core_mask: np.ndarray,
    owner_support: np.ndarray,
) -> int:
    """Count physical crossing cores joining two or more rooted owners."""

    crossing_mask = np.asarray(crossing_core_mask, dtype=bool)
    owners = np.asarray(owner_support, dtype=np.int32)
    if crossing_mask.shape != owners.shape:
        raise ValueError(
            "crossing_core_mask and owner_support must have the same shape"
        )
    connectivity = np.ones((3, 3), dtype=bool)
    components, component_count = ndi.label(
        crossing_mask,
        structure=connectivity,
    )
    resolved = 0
    for component in range(1, component_count + 1):
        component_mask = components == component
        adjacent = (
            ndi.binary_dilation(
                component_mask,
                structure=connectivity,
            )
            & ~component_mask
        )
        adjacent_owners = np.unique(owners[adjacent])
        if np.count_nonzero(adjacent_owners > 0) >= 2:
            resolved += 1
    return resolved


def _expand_skeleton_ownership(
    owner_skeleton: np.ndarray,
    outgrowth_binary: np.ndarray,
    outgrowth_width_px: float,
) -> np.ndarray:
    if not owner_skeleton.any():
        return np.zeros(owner_skeleton.shape, dtype=np.int32)
    distance, nearest = ndi.distance_transform_edt(
        owner_skeleton == 0,
        return_indices=True,
    )
    nearest_owner = owner_skeleton[tuple(nearest)]
    radius = max(1.0, outgrowth_width_px / 2.0 + 0.5)
    return np.where(
        (outgrowth_binary | (owner_skeleton > 0)) & (distance <= radius),
        nearest_owner,
        0,
    ).astype(np.int32, copy=False)


def _build_cell_results(
    cell_body_labels: np.ndarray,
    owner_outgrowth: np.ndarray,
    neurite_image: np.ndarray,
    topology: _TopologyResult,
    significant_growth_threshold_um: float,
    pixel_size_um: float,
    *,
    slice_index: int,
) -> list[NeuriteOutgrowthCellResult]:
    cell_count = int(cell_body_labels.max())
    body_areas = np.bincount(cell_body_labels.ravel(), minlength=cell_count + 1).astype(
        float
    )
    body_areas *= pixel_size_um**2
    outgrowth_labels = owner_outgrowth.ravel()
    outgrowth_pixel_counts = np.bincount(
        outgrowth_labels,
        minlength=cell_count + 1,
    )
    outgrowth_intensity_sums = np.bincount(
        outgrowth_labels,
        weights=np.asarray(neurite_image, dtype=float).ravel(),
        minlength=cell_count + 1,
    )
    results = []

    for cell in range(1, cell_count + 1):
        path_indexes = np.flatnonzero(topology.path_owners == cell)
        roots = topology.root_paths_by_cell.get(cell, ())
        process_lengths = _measure_process_lengths(cell, roots, topology)
        total_outgrowth = float(np.sum(process_lengths))
        process_count = len(process_lengths)
        curve_length = float(np.sum(topology.path_lengths[path_indexes]))
        euclidean_length = float(np.sum(topology.path_euclidean_lengths[path_indexes]))
        straightness = euclidean_length / curve_length if curve_length else 0.0
        mean_intensity = (
            float(outgrowth_intensity_sums[cell] / outgrowth_pixel_counts[cell])
            if outgrowth_pixel_counts[cell]
            else 0.0
        )
        results.append(
            NeuriteOutgrowthCellResult(
                slice_index=slice_index,
                cell=cell,
                total_outgrowth_um=total_outgrowth,
                processes=process_count,
                mean_process_length_um=(
                    total_outgrowth / process_count if process_count else 0.0
                ),
                median_process_length_um=(
                    float(np.median(process_lengths)) if process_lengths else 0.0
                ),
                max_process_length_um=(
                    float(np.max(process_lengths)) if process_lengths else 0.0
                ),
                branches=len(topology.branch_nodes_by_cell.get(cell, ())),
                straightness=straightness,
                cell_body_area_um2=float(body_areas[cell]),
                mean_outgrowth_intensity=mean_intensity,
                significant_growth=(total_outgrowth > significant_growth_threshold_um),
            )
        )
    return results


def _measure_process_lengths(
    cell: int,
    roots: Sequence[int],
    topology: _TopologyResult,
) -> list[float]:
    if not roots:
        return []
    root_owner = np.full(len(topology.path_lengths), -1, dtype=int)
    distances = np.full(len(topology.path_lengths), np.inf, dtype=float)
    queue: list[tuple[float, int, int]] = []
    for root_number, path_index in enumerate(sorted(set(roots))):
        heapq.heappush(queue, (0.0, root_number, path_index))

    while queue:
        distance, process, path_index = heapq.heappop(queue)
        if topology.path_owners[path_index] != cell:
            continue
        if distance > distances[path_index]:
            continue
        if distance == distances[path_index] and root_owner[path_index] <= process:
            continue
        distances[path_index] = distance
        root_owner[path_index] = process
        for neighbor in topology.transitions[path_index]:
            if topology.path_owners[neighbor] != cell:
                continue
            next_distance = distance + 0.5 * (
                topology.path_lengths[path_index] + topology.path_lengths[neighbor]
            )
            if next_distance <= distances[neighbor]:
                heapq.heappush(queue, (next_distance, process, neighbor))

    process_lengths = np.zeros(len(set(roots)), dtype=float)
    for path_index, process in enumerate(root_owner):
        if process >= 0:
            process_lengths[process] += topology.path_lengths[path_index]
    return [float(length) for length in process_lengths if length > 0]


def _build_summary(
    cell_results: Sequence[NeuriteOutgrowthCellResult],
    *,
    neurite_channel_index: int,
    cell_body_channel_index: int,
    nuclear_channel_index: int,
    resolved_crossovers: int,
    mean_outgrowth_average_intensity: float,
    candidate_trace_pixels: int,
    rooted_candidate_trace_pixels: int,
    unrooted_candidate_trace_pixels: int,
    rooted_candidate_trace_yield: float,
    initial_topology_owned_trace_pixels: int,
    secondary_adopted_trace_pixels: int,
    signal_repaired_trace_pixels: int,
    crossing_core_trace_pixels: int,
    final_topology_dropped_trace_pixels: int,
    final_topology_dropped_crossing_support_trace_pixels: int,
    final_topology_dropped_unrooted_path_trace_pixels: int,
    final_topology_dropped_physically_rooted_path_trace_pixels: int,
    final_topology_dropped_physically_unrooted_path_trace_pixels: int,
    final_topology_dropped_unrepresented_trace_pixels: int,
    final_topology_added_trace_pixels: int,
    final_topology_owned_trace_pixels: int,
    published_owned_trace_pixels: int,
    secondary_owned_unrooted_trace_pixels: int,
    secondary_unowned_unrooted_trace_pixels: int,
    candidate_mask_pixels: int,
    rooted_candidate_mask_pixels: int,
    unrooted_residual_pixels: int,
    secondary_owned_residual_pixels: int,
    secondary_unowned_residual_pixels: int,
    secondary_owned_residual_fraction: float,
) -> NeuriteOutgrowthSummary:
    cell_count = len(cell_results)
    total_outgrowth = float(sum(row.total_outgrowth_um for row in cell_results))
    total_processes = int(sum(row.processes for row in cell_results))
    total_branches = int(sum(row.branches for row in cell_results))
    total_body_area = float(sum(row.cell_body_area_um2 for row in cell_results))
    significant_count = sum(row.significant_growth for row in cell_results)
    return NeuriteOutgrowthSummary(
        neurite_channel_index=neurite_channel_index,
        cell_body_channel_index=cell_body_channel_index,
        nuclear_channel_index=nuclear_channel_index,
        number_of_cells=cell_count,
        total_outgrowth_um=total_outgrowth,
        mean_outgrowth_per_cell_um=(
            total_outgrowth / cell_count if cell_count else 0.0
        ),
        total_processes=total_processes,
        mean_processes_per_cell=(total_processes / cell_count if cell_count else 0.0),
        total_branches=total_branches,
        mean_branches_per_cell=(total_branches / cell_count if cell_count else 0.0),
        total_cell_body_area_um2=total_body_area,
        mean_cell_body_area_um2=(total_body_area / cell_count if cell_count else 0.0),
        straightness=(
            float(np.mean([row.straightness for row in cell_results]))
            if cell_results
            else 0.0
        ),
        cells_significant_growth=int(significant_count),
        percent_cells_significant_growth=(
            100.0 * significant_count / cell_count if cell_count else 0.0
        ),
        mean_outgrowth_average_intensity=mean_outgrowth_average_intensity,
        resolved_crossovers=resolved_crossovers,
        candidate_trace_pixels=candidate_trace_pixels,
        rooted_candidate_trace_pixels=rooted_candidate_trace_pixels,
        unrooted_candidate_trace_pixels=unrooted_candidate_trace_pixels,
        rooted_candidate_trace_yield=rooted_candidate_trace_yield,
        initial_topology_owned_trace_pixels=initial_topology_owned_trace_pixels,
        secondary_adopted_trace_pixels=secondary_adopted_trace_pixels,
        signal_repaired_trace_pixels=signal_repaired_trace_pixels,
        crossing_core_trace_pixels=crossing_core_trace_pixels,
        final_topology_dropped_trace_pixels=final_topology_dropped_trace_pixels,
        final_topology_dropped_crossing_support_trace_pixels=(
            final_topology_dropped_crossing_support_trace_pixels
        ),
        final_topology_dropped_unrooted_path_trace_pixels=(
            final_topology_dropped_unrooted_path_trace_pixels
        ),
        final_topology_dropped_physically_rooted_path_trace_pixels=(
            final_topology_dropped_physically_rooted_path_trace_pixels
        ),
        final_topology_dropped_physically_unrooted_path_trace_pixels=(
            final_topology_dropped_physically_unrooted_path_trace_pixels
        ),
        final_topology_dropped_unrepresented_trace_pixels=(
            final_topology_dropped_unrepresented_trace_pixels
        ),
        final_topology_added_trace_pixels=final_topology_added_trace_pixels,
        final_topology_owned_trace_pixels=final_topology_owned_trace_pixels,
        published_owned_trace_pixels=published_owned_trace_pixels,
        secondary_owned_unrooted_trace_pixels=(secondary_owned_unrooted_trace_pixels),
        secondary_unowned_unrooted_trace_pixels=(
            secondary_unowned_unrooted_trace_pixels
        ),
        candidate_mask_pixels=candidate_mask_pixels,
        rooted_candidate_mask_pixels=rooted_candidate_mask_pixels,
        unrooted_residual_pixels=unrooted_residual_pixels,
        secondary_owned_residual_pixels=secondary_owned_residual_pixels,
        secondary_unowned_residual_pixels=secondary_unowned_residual_pixels,
        secondary_owned_residual_fraction=secondary_owned_residual_fraction,
    )
