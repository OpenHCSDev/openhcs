"""
Simple cell counting using thresholding and connected component labeling.

This module provides a compact NumPy/scikit-image cell counter intended for
basic bright- or dark-object workflows, plus MetaXpress-style W1 cell counting
and W2 stained-area scoring. The implementations share connected-component and
watershed infrastructure while exposing controls appropriate to each workflow.
"""

from openhcs.core.memory import numpy
from openhcs.core.artifacts import (
    ArtifactMeasurementSubjectRelation,
    ArtifactSpec,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
)
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
from openhcs.processing.materialization import (
    CsvOptions,
    MaterializationSpec,
    ROIOptions,
)

from dataclasses import dataclass
from enum import Enum
import sys
from typing import Optional

import numpy as np
from scipy import ndimage as ndi
from skimage.feature import peak_local_max
from skimage.filters import threshold_otsu, threshold_li, threshold_yen
from skimage.measure import regionprops
from skimage.morphology import h_maxima
from skimage.segmentation import expand_labels, watershed

from .metaxpress_utils import HiddenPixelSize, local_background_response, odd_size


class ThresholdMethod(str, Enum):
    """Thresholding methods for cell detection."""

    OTSU = "otsu"
    LI = "li"
    YEN = "yen"
    PERCENTILE = "percentile"
    MANUAL = "manual"


class Foreground(str, Enum):
    """Foreground type for thresholding."""

    BRIGHT = "bright"
    DARK = "dark"


@dataclass(frozen=True)
class SimpleCellSegmentationConfig:
    """Canonical settings for one channel of simple cell segmentation."""

    threshold_method: ThresholdMethod = ThresholdMethod.OTSU
    """Thresholding strategy used to create the foreground mask."""

    threshold: float = 0.5
    """Manual threshold used when ``threshold_method`` is ``MANUAL``."""

    threshold_percentile: float = 99.0
    """Percentile used when ``threshold_method`` is ``PERCENTILE``."""

    foreground: Foreground = Foreground.BRIGHT
    """Whether objects are brighter or darker than the background."""

    min_size: int = 20
    """Minimum accepted object area in pixels."""

    max_size: int = 100000
    """Maximum accepted object area in pixels."""

    max_eccentricity: float = 1.0
    """Maximum accepted object eccentricity; ``1.0`` disables this filter."""

    watershed_large_objects: bool = False
    """Whether to split oversized connected components before filtering."""

    watershed_min_size: Optional[int] = None
    """Optional lower area threshold for watershed attempts."""

    watershed_max_size: Optional[int] = None
    """Optional upper area threshold for watershed attempts."""

    watershed_min_distance: int = 5
    """Minimum spacing between watershed seed points."""

    watershed_footprint_size: int = 3
    """Square footprint side length used to find watershed seeds."""

    def validate(self) -> None:
        """Validate the complete settings block for one channel."""

        if self.min_size < 0:
            raise ValueError("min_size must be >= 0")
        if self.max_size < self.min_size:
            raise ValueError("max_size must be >= min_size")
        if not 0.0 <= self.max_eccentricity <= 1.0:
            raise ValueError("max_eccentricity must be in [0.0, 1.0]")
        if not 0.0 <= self.threshold_percentile <= 100.0:
            raise ValueError("threshold_percentile must be in [0.0, 100.0]")
        if self.watershed_min_size is not None and self.watershed_min_size < 1:
            raise ValueError("watershed_min_size must be >= 1 when set")

        split_size = (
            self.max_size
            if self.watershed_min_size is None
            else self.watershed_min_size
        )
        if (
            self.watershed_max_size is not None
            and self.watershed_max_size <= split_size
        ):
            raise ValueError(
                "watershed_max_size must be greater than the watershed split "
                "threshold when set"
            )
        if self.watershed_min_distance < 1:
            raise ValueError("watershed_min_distance must be >= 1")
        if self.watershed_footprint_size < 1:
            raise ValueError("watershed_footprint_size must be >= 1")


class StainedArea(str, Enum):
    """MetaXpress-style cellular compartment used to score W2 staining."""

    NUCLEUS = "nucleus"
    NUCLEUS_AND_CYTOPLASM = "nucleus and cytoplasm"


@dataclass(frozen=True)
class MetaXpressWavelengthSettings:
    """User-facing MetaXpress-style detection settings for one wavelength."""

    channel_index: int = 0
    """Zero-based index of this wavelength in the channel stack."""

    approx_min_width: float = 5.0
    """Approximate minimum short-axis width in micrometers."""

    approx_max_width: float = 30.0
    """Approximate maximum short-axis width in micrometers."""

    intensity_above_local_background: float = 100.0
    """Minimum raw-intensity difference above adaptive local background."""

    def validate(self, name: str) -> None:
        """Validate one wavelength's complete public settings block."""

        if self.channel_index < 0:
            raise ValueError(f"{name}.channel_index must be >= 0")
        if not np.isfinite(self.approx_min_width) or self.approx_min_width <= 0:
            raise ValueError(f"{name}.approx_min_width must be > 0")
        if (
            not np.isfinite(self.approx_max_width)
            or self.approx_max_width < self.approx_min_width
        ):
            raise ValueError(
                f"{name}.approx_max_width must be >= {name}.approx_min_width"
            )
        if (
            not np.isfinite(self.intensity_above_local_background)
            or self.intensity_above_local_background < 0
        ):
            raise ValueError(f"{name}.intensity_above_local_background must be >= 0")


@dataclass(frozen=True)
class MetaXpressW2Settings(MetaXpressWavelengthSettings):
    """MetaXpress-style W2 settings, including the scored cellular area."""

    channel_index: int = 1
    stained_area: StainedArea = StainedArea.NUCLEUS
    """Score W2 staining in nuclei or in expanded nucleus-plus-cytoplasm areas."""

    def validate(self, name: str = "w2") -> None:
        super().validate(name)
        StainedArea(self.stained_area)


@dataclass(frozen=True)
class SimpleCellCountResult:
    """Canonical result schema for simple single-channel counting."""

    slice_index: int
    cell_count: int


@dataclass(frozen=True)
class DualChannelCountResult:
    """MetaXpress-style W1 cell count and W2 positive/negative scoring summary."""

    w1_channel_index: int
    w2_channel_index: int
    total_cell_count: int
    w2_positive_cell_count: int
    w2_negative_cell_count: int
    w2_positive_percent: float
    w2_stained_area: str
    minimum_stained_area: float
    all_w2_mean_stained_area: float
    positive_w2_mean_stained_area: float


@dataclass(frozen=True)
class DualChannelCellResult:
    """W2 scoring measurements keyed by the W1 nucleus label."""

    object_label: int
    w2_positive: bool
    w2_stained_area_um2: float


# Make the Enums importable/stable for multiprocessing/ZMQ pickling
_count_cells_simple = sys.modules[__name__]

ThresholdMethod.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "ThresholdMethod", ThresholdMethod)

Foreground.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "Foreground", Foreground)

SimpleCellSegmentationConfig.__module__ = _count_cells_simple.__name__
setattr(
    _count_cells_simple,
    "SimpleCellSegmentationConfig",
    SimpleCellSegmentationConfig,
)

StainedArea.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "StainedArea", StainedArea)

MetaXpressWavelengthSettings.__module__ = _count_cells_simple.__name__
setattr(
    _count_cells_simple,
    "MetaXpressWavelengthSettings",
    MetaXpressWavelengthSettings,
)

MetaXpressW2Settings.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "MetaXpressW2Settings", MetaXpressW2Settings)

SimpleCellCountResult.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "SimpleCellCountResult", SimpleCellCountResult)

DualChannelCountResult.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "DualChannelCountResult", DualChannelCountResult)

DualChannelCellResult.__module__ = _count_cells_simple.__name__
setattr(_count_cells_simple, "DualChannelCellResult", DualChannelCellResult)


DUAL_CHANNEL_COUNTS_OUTPUT = ArtifactSpec.output(
    "dual_channel_counts",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(ArtifactMeasurementSubjectRelation(),),
)
W1_NUCLEI_OUTPUT = ArtifactSpec.output(
    "w1_nuclei",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions()),
)
W2_STAIN_OUTPUT = ArtifactSpec.output(
    "w2_stain",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions()),
)
DUAL_CHANNEL_CELLS_OUTPUT = ArtifactSpec.output(
    "dual_channel_cells",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions(filename_suffix="_cells.csv")),
    relations=(
        ObjectMeasurementSubjectRelation(
            source=W1_NUCLEI_OUTPUT.ref(),
            id_field="object_label",
        ),
    ),
)


@numpy
@artifact_outputs(
    ArtifactSpec(
        "cell_counts",
        MeasurementsArtifactType,
        materialization=MaterializationSpec(CsvOptions()),
        relations=(ArtifactMeasurementSubjectRelation(),),
    ),
    ArtifactSpec(
        "segmentation_masks",
        ObjectLabelsArtifactType,
        materialization=MaterializationSpec(ROIOptions()),
    ),
)
def count_cells_simple(
    image,
    segmentation_settings: SimpleCellSegmentationConfig = (
        SimpleCellSegmentationConfig()
    ),
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows, np.ndarray]:
    """
    Count thresholded objects in a 3D image stack with optional shape cleanup.

    The function processes each 2D plane of ``image`` independently. For every
    slice it computes a threshold, builds a binary foreground mask, labels
    connected components, optionally applies distance-transform watershed only
    to components larger than ``max_size``, and then applies the final object
    acceptance filters. The reported count and ROI mask therefore describe the
    final accepted connected components after all splitting and filtering.

    Filtering order is intentional:

    1. ``min_size`` is used only in the final acceptance pass.
    2. If ``watershed_large_objects`` is enabled, raw connected components
       whose area is greater than ``watershed_min_size`` are eligible for
       splitting. If ``watershed_min_size`` is ``None``, ``max_size`` is used
       as the split trigger for backward compatibility. When
       ``watershed_max_size`` is set, only components with
       ``watershed_min_size < area <= watershed_max_size`` are split.
    3. ``min_size``, ``max_size``, and ``max_eccentricity`` are then applied to
       the resulting candidate regions.

    This means a large merged component can be split into multiple accepted
    cells, as long as each watershed fragment lands within the size and shape
    limits. If watershed cannot find at least two seeds for a large object, that
    object remains a single candidate and is usually rejected by ``max_size``.

    Args:
        image: Input 3D image stack with shape ``(Z, Y, X)``. OpenHCS also uses
            this shape for logical single-plane data, so a single 2D image
            should be supplied as ``image[None, :, :]``. The input image is
            returned unchanged as the primary output.
        segmentation_settings: Complete threshold, foreground, size, shape, and
            watershed settings for every independently processed image plane.

    Returns:
        Tuple:
          - ``image`` unchanged, preserving OpenHCS primary-output semantics.
          - A list of per-slice dictionaries with ``slice_index`` and
            ``cell_count`` fields. The count is the number of accepted labels
            after optional splitting and all filters.
          - A list of labeled ``int32`` segmentation masks, one per input
            slice. Background is ``0``. Accepted objects are relabeled
            sequentially from ``1`` within each slice.

    Raises:
        ValueError: If size limits, eccentricity limits, or watershed seed
            parameters are outside their supported ranges.
    """
    segmentation_settings.validate()

    results = []
    masks = []

    for i, slice_data in enumerate(image):
        labeled_filtered = _segment_simple_slice(
            slice_data,
            segmentation_settings,
        )
        final_count = int(labeled_filtered.max())

        results.append(SimpleCellCountResult(slice_index=i, cell_count=final_count))

        masks.append(labeled_filtered.astype(np.int32, copy=False))

    return (
        image,
        DataclassMeasurementColumnarRows(
            tuple(results),
            row_type=SimpleCellCountResult,
        ),
        np.stack(masks),
    )


@numpy
@artifact_outputs(
    DUAL_CHANNEL_COUNTS_OUTPUT,
    DUAL_CHANNEL_CELLS_OUTPUT,
    W1_NUCLEI_OUTPUT,
    W2_STAIN_OUTPUT,
)
@artifact_inputs("pixel_size")
def count_cells_simple_dual_channel(
    image,
    w1: MetaXpressWavelengthSettings = MetaXpressWavelengthSettings(
        channel_index=0,
    ),
    w2: MetaXpressW2Settings = MetaXpressW2Settings(
        channel_index=1,
    ),
    minimum_stained_area: float = 10.0,
    pixel_size: HiddenPixelSize = HiddenPixelSize(1.0),
) -> tuple[
    np.ndarray,
    DataclassMeasurementColumnarRows,
    DataclassMeasurementColumnarRows,
    np.ndarray,
    np.ndarray,
]:
    """Count W1 nuclei and score W2-positive cells like MetaXpress MWCS.

    W1 is the required all-nuclei wavelength and therefore defines total cell
    count. W2 is an additional stain scored within each W1 cell's selected
    compartment. A cell is W2-positive when its detected stained area is at
    least ``minimum_stained_area``.

    Widths and stained areas are expressed in micrometers and square
    micrometers. OpenHCS injects the plate pixel size at compilation; direct
    calls use the 1.0 micrometer-per-pixel default. Detection uses adaptive
    local-background subtraction. Object-size filters, background window,
    watershed trigger, seed spacing, and seed footprint are all derived from
    the W1/W2 width settings rather than exposed as separate controls.

    Args:
        image: Input stack with shape ``(C, Y, X)``. The input is returned
            unchanged as the primary output.
        w1: W1 nucleus channel, approximate short-axis width range, and minimum
            intensity above local background.
        w2: W2 stain channel with the same detection controls plus the cellular
            compartment to score: nucleus or nucleus and cytoplasm.
        minimum_stained_area: Minimum W2 stained area in square micrometers for
            a W1 cell to be scored W2-positive.
        pixel_size: Plate pixel size in micrometers per pixel. This is injected
            from microscope metadata and hidden from the function editor.

    Returns:
        Tuple:
          - ``image`` unchanged.
          - A one-element list containing MetaXpress-style positive/negative W2
            scoring and stained-area summary fields.
          - Independently aligned W1 nucleus and W2 stain-object ROI masks. W1
            ROI metadata includes each cell's W2-positive classification and
            stained area.

    Raises:
        ValueError: If the stack, wavelength settings, pixel size, or minimum
            stained area is invalid.
    """
    if image.ndim != 3:
        raise ValueError(f"Expected 3D channel stack, got {image.ndim}D")
    w1.validate("w1")
    w2.validate("w2")
    if w1.channel_index == w2.channel_index:
        raise ValueError("w1.channel_index and w2.channel_index must be different")
    if not 0 <= w1.channel_index < image.shape[0]:
        raise ValueError("w1.channel_index is outside the input stack")
    if not 0 <= w2.channel_index < image.shape[0]:
        raise ValueError("w2.channel_index is outside the input stack")
    if minimum_stained_area < 0:
        raise ValueError("minimum_stained_area must be >= 0")

    pixel_size_um = float(pixel_size)
    if not np.isfinite(pixel_size_um) or pixel_size_um <= 0:
        raise ValueError("pixel_size must be a finite value > 0")

    w1_labels = segment_metaxpress_round_objects(
        image[w1.channel_index],
        w1,
        pixel_size_um,
    )
    w2_labels = segment_metaxpress_round_objects(
        image[w2.channel_index],
        w2,
        pixel_size_um,
    )
    compartments = _build_w2_compartments(
        w1_labels,
        w1,
        w2,
        pixel_size_um,
    )
    stained_areas = _measure_stained_area_by_cell(
        compartments,
        w2_labels > 0,
        int(w1_labels.max()),
        pixel_size_um,
    )
    positive_cells = stained_areas >= float(minimum_stained_area)
    if positive_cells.size:
        positive_cells[0] = False

    total_cell_count = int(w1_labels.max())
    positive_count = int(np.count_nonzero(positive_cells))
    negative_count = total_cell_count - positive_count
    cell_areas = stained_areas[1:]
    positive_areas = stained_areas[positive_cells]

    result = DualChannelCountResult(
        w1_channel_index=int(w1.channel_index),
        w2_channel_index=int(w2.channel_index),
        total_cell_count=total_cell_count,
        w2_positive_cell_count=positive_count,
        w2_negative_cell_count=negative_count,
        w2_positive_percent=(
            100.0 * positive_count / total_cell_count if total_cell_count else 0.0
        ),
        w2_stained_area=StainedArea(w2.stained_area).value,
        minimum_stained_area=float(minimum_stained_area),
        all_w2_mean_stained_area=(
            float(np.mean(cell_areas)) if cell_areas.size else 0.0
        ),
        positive_w2_mean_stained_area=(
            float(np.mean(positive_areas)) if positive_areas.size else 0.0
        ),
    )

    cell_results = tuple(
        DualChannelCellResult(
            object_label=label,
            w2_positive=bool(positive_cells[label]),
            w2_stained_area_um2=float(stained_areas[label]),
        )
        for label in range(1, total_cell_count + 1)
    )
    w1_label_stack = np.zeros(image.shape, dtype=np.int32)
    w1_label_stack[w1.channel_index] = w1_labels
    w2_label_stack = np.zeros(image.shape, dtype=np.int32)
    w2_label_stack[w2.channel_index] = w2_labels

    return (
        image,
        DataclassMeasurementColumnarRows(
            (result,),
            row_type=DualChannelCountResult,
        ),
        DataclassMeasurementColumnarRows(
            cell_results,
            row_type=DualChannelCellResult,
        ),
        w1_label_stack,
        w2_label_stack,
    )


@dataclass(frozen=True)
class LabelShapeStatistics:
    """Vectorized per-label geometry indexed by the label value."""

    counts: np.ndarray
    centroid_rows_px: np.ndarray
    centroid_columns_px: np.ndarray
    major_axis_lengths_px: np.ndarray
    minor_axis_lengths_px: np.ndarray


@dataclass(frozen=True)
class RoundObjectSegmentationStages:
    """Exact pre-filter labels and acceptance evidence for round objects."""

    prefilter_labels: np.ndarray
    source_component_by_label: np.ndarray
    shape_statistics: LabelShapeStatistics
    peak_response_by_label: np.ndarray
    mean_response_by_label: np.ndarray
    width_keep_mask: np.ndarray
    adjacent_satellite_mask: np.ndarray

    @property
    def keep_mask(self) -> np.ndarray:
        return self.width_keep_mask & ~self.adjacent_satellite_mask

    @property
    def accepted_labels(self) -> np.ndarray:
        return _relabel_by_keep_mask(self.prefilter_labels, self.keep_mask)


def segment_metaxpress_round_objects(
    slice_data: np.ndarray,
    settings: MetaXpressWavelengthSettings,
    pixel_size_um: float,
) -> np.ndarray:
    """Segment bright round objects using shared MetaXpress-style controls."""
    return round_object_segmentation_stages(
        slice_data, settings, pixel_size_um
    ).accepted_labels


def round_object_segmentation_stages(
    slice_data: np.ndarray,
    settings: MetaXpressWavelengthSettings,
    pixel_size_um: float,
) -> RoundObjectSegmentationStages:
    """Run the shared detector once and retain its exact acceptance evidence."""

    min_width_px = settings.approx_min_width / pixel_size_um
    max_width_px = settings.approx_max_width / pixel_size_um
    intensity_above_background = local_background_response(
        slice_data,
        object_width_px=max_width_px,
        bright_objects=True,
    )
    binary = intensity_above_background >= settings.intensity_above_local_background

    minimum_pair_area = max(
        1,
        int(np.ceil(2.0 * np.pi * (min_width_px / 2.0) ** 2)),
    )
    seed_spacing = max(1, int(round(min_width_px / 2.0)))
    seed_footprint = odd_size(max(1.0, min_width_px / 2.0))
    seed_prominence = max(1.0, min_width_px / 4.0)
    intensity_smoothing_sigma = max(0.5, min_width_px / 4.0)
    component_stages = _label_binary_component_stages(
        binary,
        watershed_large_objects=True,
        watershed_split_size=minimum_pair_area,
        watershed_max_size=None,
        watershed_min_distance=seed_spacing,
        watershed_footprint_size=seed_footprint,
        watershed_peak_prominence=seed_prominence,
        watershed_marker_image=intensity_above_background,
        watershed_marker_smoothing_sigma=intensity_smoothing_sigma,
        watershed_marker_peak_prominence=(
            settings.intensity_above_local_background / 4.0
        ),
    )
    labeled = component_stages.output_labels

    shape_statistics = _shape_statistics_by_label(labeled)
    peak_response, mean_response = _response_statistics_by_label(
        labeled,
        intensity_above_background,
    )
    width_keep_mask = (
        shape_statistics.minor_axis_lengths_px >= min_width_px
    ) & (
        shape_statistics.minor_axis_lengths_px <= max_width_px
    )
    if width_keep_mask.size:
        width_keep_mask[0] = False
    adjacent_satellite_mask = _adjacent_satellite_mask(
        labeled,
        shape_statistics.counts,
        peak_response,
        width_keep_mask,
        maximum_candidate_area=minimum_pair_area,
        minimum_core_response=(
            2.0 * settings.intensity_above_local_background
        ),
        maximum_gap_px=seed_spacing,
    )
    return RoundObjectSegmentationStages(
        labeled,
        component_stages.source_component_by_output,
        shape_statistics,
        peak_response,
        mean_response,
        width_keep_mask,
        adjacent_satellite_mask,
    )


@dataclass(frozen=True)
class RoundObjectWidthResult:
    """Width-gate evidence keyed to an object before final label filtering."""

    object_label: int
    accepted_label: int
    source_component_label: int
    source_component_output_count: int
    split_from_source_component: bool
    area_pixels: int
    centroid_row_px: float
    centroid_column_px: float
    peak_intensity_above_local_background: float
    mean_intensity_above_local_background: float
    core_support_threshold: float
    weak_core_candidate: bool
    rejected_as_adjacent_satellite: bool
    major_axis_um: float
    minor_axis_um: float
    minimum_width_um: float
    maximum_width_um: float


ROUND_OBJECT_PREFILTER_OUTPUT = ArtifactSpec.output(
    "round_object_prefilter",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions()),
)
ROUND_OBJECT_ACCEPTED_OUTPUT = ArtifactSpec.output(
    "round_object_accepted",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions()),
)
ROUND_OBJECT_WEAK_CORE_OUTPUT = ArtifactSpec.output(
    "round_object_weak_core_candidates",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions()),
)
ROUND_OBJECT_ADJACENT_SATELLITE_OUTPUT = ArtifactSpec.output(
    "round_object_adjacent_satellite_candidates",
    ObjectLabelsArtifactType,
    materialization=MaterializationSpec(ROIOptions()),
)
ROUND_OBJECT_WIDTHS_OUTPUT = ArtifactSpec.output(
    "round_object_widths",
    MeasurementsArtifactType,
    materialization=MaterializationSpec(CsvOptions()),
    relations=(
        ObjectMeasurementSubjectRelation(
            source=ROUND_OBJECT_PREFILTER_OUTPUT.ref(),
            id_field="object_label",
        ),
    ),
)


@numpy
@artifact_inputs("pixel_size")
@artifact_outputs(
    ROUND_OBJECT_WIDTHS_OUTPUT,
    ROUND_OBJECT_PREFILTER_OUTPUT,
    ROUND_OBJECT_ACCEPTED_OUTPUT,
    ROUND_OBJECT_WEAK_CORE_OUTPUT,
    ROUND_OBJECT_ADJACENT_SATELLITE_OUTPUT,
)
def inspect_metaxpress_round_objects(
    image: np.ndarray,
    settings: MetaXpressWavelengthSettings = MetaXpressWavelengthSettings(),
    pixel_size: HiddenPixelSize = HiddenPixelSize(1.0),
) -> tuple[
    np.ndarray,
    DataclassMeasurementColumnarRows,
    np.ndarray,
    np.ndarray,
    np.ndarray,
    np.ndarray,
]:
    """Diagnose round-object admission stages without changing the detector.

    Input is a CHANNEL,Y,X stack. Only the selected channel is analysed; the
    main image is returned unchanged. Prefilter and accepted object labels share
    the input channel axis, with other channels empty. The typed outputs are the
    per-object ``round_object_widths`` measurements plus
    ``round_object_prefilter``, ``round_object_accepted``,
    ``round_object_weak_core_candidates``, and
    ``round_object_adjacent_satellite_candidates`` labels. Source-component
    lineage distinguishes separate threshold-stage components from watershed
    splits. Inspect every diagnostic beside raw stain morphology; acceptance is
    not proof that an object is a biological nucleus or cell.
    """
    settings.validate("settings")
    if image.ndim != 3 or not 0 <= settings.channel_index < image.shape[0]:
        raise ValueError("Expected CHANNEL,Y,X with the selected channel present")
    pixel_size_um = float(pixel_size)
    if not np.isfinite(pixel_size_um) or pixel_size_um <= 0:
        raise ValueError("Pixel size must be finite and positive")
    stages = round_object_segmentation_stages(
        image[settings.channel_index], settings, pixel_size_um
    )
    prefilter = np.zeros(image.shape, dtype=np.int32)
    prefilter[settings.channel_index] = stages.prefilter_labels
    accepted = np.zeros(image.shape, dtype=np.int32)
    accepted[settings.channel_index] = stages.accepted_labels
    core_support_threshold = 2.0 * settings.intensity_above_local_background
    weak_core_mask = stages.width_keep_mask & (
        stages.peak_response_by_label < core_support_threshold
    )
    weak_core = np.zeros(image.shape, dtype=np.int32)
    weak_core[settings.channel_index] = _relabel_by_keep_mask(
        stages.prefilter_labels,
        weak_core_mask,
    )
    adjacent_satellites = np.zeros(image.shape, dtype=np.int32)
    adjacent_satellites[settings.channel_index] = _relabel_by_keep_mask(
        stages.prefilter_labels,
        stages.adjacent_satellite_mask,
    )
    accepted_ids = np.cumsum(stages.keep_mask) * stages.keep_mask
    source_output_counts = np.bincount(stages.source_component_by_label[1:])
    rows = tuple(
        RoundObjectWidthResult(
            object_label=int(label),
            accepted_label=int(accepted_ids[label]),
            source_component_label=int(stages.source_component_by_label[label]),
            source_component_output_count=int(
                source_output_counts[stages.source_component_by_label[label]]
            ),
            split_from_source_component=bool(
                source_output_counts[stages.source_component_by_label[label]] > 1
            ),
            area_pixels=int(stages.shape_statistics.counts[label]),
            centroid_row_px=float(stages.shape_statistics.centroid_rows_px[label]),
            centroid_column_px=float(
                stages.shape_statistics.centroid_columns_px[label]
            ),
            peak_intensity_above_local_background=float(
                stages.peak_response_by_label[label]
            ),
            mean_intensity_above_local_background=float(
                stages.mean_response_by_label[label]
            ),
            core_support_threshold=float(core_support_threshold),
            weak_core_candidate=bool(weak_core_mask[label]),
            rejected_as_adjacent_satellite=bool(
                stages.adjacent_satellite_mask[label]
            ),
            major_axis_um=float(
                stages.shape_statistics.major_axis_lengths_px[label] * pixel_size_um
            ),
            minor_axis_um=float(
                stages.shape_statistics.minor_axis_lengths_px[label] * pixel_size_um
            ),
            minimum_width_um=settings.approx_min_width,
            maximum_width_um=settings.approx_max_width,
        )
        for label in np.flatnonzero(stages.shape_statistics.counts[1:]) + 1
    )
    return (
        image,
        DataclassMeasurementColumnarRows(rows, row_type=RoundObjectWidthResult),
        prefilter,
        accepted,
        weak_core,
        adjacent_satellites,
    )


def _adjacent_satellite_mask(
    labeled: np.ndarray,
    counts: np.ndarray,
    peak_response: np.ndarray,
    width_keep_mask: np.ndarray,
    *,
    maximum_candidate_area: int,
    minimum_core_response: float,
    maximum_gap_px: int,
) -> np.ndarray:
    """Identify small weak fragments adjacent to a supported round object.

    The rule is deliberately conjunctive: an object must already pass the
    declared width gate, lack a supported intensity core, be smaller than the
    area needed for two minimum-width nuclei, and sit within the existing
    watershed seed spacing of a larger width-accepted object with a supported
    core. Isolated faint objects are retained for downstream QA rather than
    being rejected by intensity alone.
    """

    if labeled.ndim != 2:
        raise ValueError("Adjacent-satellite detection requires a 2D label plane")
    if not (
        counts.shape == peak_response.shape == width_keep_mask.shape
        and counts.shape[0] == int(labeled.max()) + 1
    ):
        raise ValueError("Adjacent-satellite evidence must share label indexing")
    if maximum_gap_px < 1:
        raise ValueError("maximum_gap_px must be >= 1")

    weak_small = (
        width_keep_mask
        & (counts < maximum_candidate_area)
        & (peak_response < minimum_core_response)
    )
    if weak_small.size:
        weak_small[0] = False
    candidates = np.flatnonzero(weak_small)
    rejected = np.zeros_like(width_keep_mask, dtype=bool)
    if not len(candidates):
        return rejected

    offsets = np.arange(-maximum_gap_px, maximum_gap_px + 1)
    offset_rows, offset_columns = np.meshgrid(offsets, offsets, indexing="ij")
    neighborhood = (
        np.square(offset_rows) + np.square(offset_columns)
        <= maximum_gap_px**2
    )
    object_slices = ndi.find_objects(labeled)
    for candidate in candidates:
        object_slice = object_slices[candidate - 1]
        if object_slice is None:
            continue
        expanded_slice = tuple(
            slice(
                max(0, axis_slice.start - maximum_gap_px),
                min(axis_size, axis_slice.stop + maximum_gap_px),
            )
            for axis_slice, axis_size in zip(
                object_slice,
                labeled.shape,
                strict=True,
            )
        )
        local_labels = labeled[expanded_slice]
        nearby = ndi.binary_dilation(
            local_labels == candidate,
            structure=neighborhood,
        )
        neighbor_labels = np.unique(
            local_labels[
                nearby
                & (local_labels != 0)
                & (local_labels != candidate)
            ]
        )
        if np.any(
            width_keep_mask[neighbor_labels]
            & (counts[neighbor_labels] >= maximum_candidate_area)
            & (peak_response[neighbor_labels] >= minimum_core_response)
        ):
            rejected[candidate] = True
    return rejected


def _shape_statistics_by_label(labeled: np.ndarray) -> LabelShapeStatistics:
    """Return vectorized geometry indexed by 2D object label."""

    labels = np.asarray(labeled)
    if labels.ndim != 2:
        raise ValueError(
            f"Object axis lengths require a 2D label image, got shape {labels.shape}."
        )
    label_count = int(labels.max())
    output_size = label_count + 1
    flat_labels = labels.ravel()
    foreground_indices = np.flatnonzero(flat_labels)
    if not len(foreground_indices):
        empty = np.zeros(output_size, dtype=float)
        return LabelShapeStatistics(
            empty,
            empty.copy(),
            empty.copy(),
            empty.copy(),
            empty.copy(),
        )

    object_labels = flat_labels[foreground_indices]
    rows = (foreground_indices // labels.shape[1]).astype(float, copy=False)
    columns = (foreground_indices % labels.shape[1]).astype(float, copy=False)
    counts = np.bincount(object_labels, minlength=output_size).astype(float)
    row_sums = np.bincount(object_labels, weights=rows, minlength=output_size)
    column_sums = np.bincount(
        object_labels,
        weights=columns,
        minlength=output_size,
    )
    mean_rows = np.divide(
        row_sums,
        counts,
        out=np.zeros(output_size, dtype=float),
        where=counts > 0,
    )
    mean_columns = np.divide(
        column_sums,
        counts,
        out=np.zeros(output_size, dtype=float),
        where=counts > 0,
    )
    row_variances = np.divide(
        np.bincount(
            object_labels,
            weights=rows * rows,
            minlength=output_size,
        ),
        counts,
        out=np.zeros(output_size, dtype=float),
        where=counts > 0,
    ) - np.square(mean_rows)
    column_variances = np.divide(
        np.bincount(
            object_labels,
            weights=columns * columns,
            minlength=output_size,
        ),
        counts,
        out=np.zeros(output_size, dtype=float),
        where=counts > 0,
    ) - np.square(mean_columns)
    covariance = np.divide(
        np.bincount(
            object_labels,
            weights=rows * columns,
            minlength=output_size,
        ),
        counts,
        out=np.zeros(output_size, dtype=float),
        where=counts > 0,
    ) - (mean_rows * mean_columns)
    discriminant = np.sqrt(
        np.maximum(
            0.0,
            np.square(row_variances - column_variances) + 4.0 * np.square(covariance),
        )
    )
    major_variances = np.maximum(
        0.0,
        0.5 * (row_variances + column_variances + discriminant),
    )
    minor_variances = np.maximum(
        0.0,
        0.5 * (row_variances + column_variances - discriminant),
    )
    return LabelShapeStatistics(
        counts,
        mean_rows,
        mean_columns,
        4.0 * np.sqrt(major_variances),
        4.0 * np.sqrt(minor_variances),
    )


def _response_statistics_by_label(
    labeled: np.ndarray,
    response: np.ndarray,
) -> tuple[np.ndarray, np.ndarray]:
    """Return peak and mean response values indexed by object label."""

    if response.shape != labeled.shape:
        raise ValueError("Response image must match the object-label plane")
    output_size = int(labeled.max()) + 1
    foreground = labeled > 0
    if not np.any(foreground):
        empty = np.zeros(output_size, dtype=float)
        return empty, empty.copy()

    object_labels = labeled[foreground]
    object_responses = np.asarray(response, dtype=float)[foreground]
    counts = np.bincount(object_labels, minlength=output_size)
    response_sums = np.bincount(
        object_labels,
        weights=object_responses,
        minlength=output_size,
    )
    mean_response = np.divide(
        response_sums,
        counts,
        out=np.zeros(output_size, dtype=float),
        where=counts > 0,
    )
    peak_response = np.full(output_size, -np.inf, dtype=float)
    np.maximum.at(peak_response, object_labels, object_responses)
    peak_response[~np.isfinite(peak_response)] = 0.0
    return peak_response, mean_response


def _build_w2_compartments(
    w1_labels: np.ndarray,
    w1: MetaXpressWavelengthSettings,
    w2: MetaXpressW2Settings,
    pixel_size_um: float,
) -> np.ndarray:
    """Build non-overlapping W1-cell compartments used for W2 scoring."""

    stained_area = StainedArea(w2.stained_area)
    if stained_area == StainedArea.NUCLEUS:
        return w1_labels.astype(np.int32, copy=False)

    expansion_um = max(
        0.0,
        (w2.approx_max_width - w1.approx_max_width) / 2.0,
    )
    expansion_px = expansion_um / pixel_size_um
    return expand_labels(w1_labels, distance=expansion_px).astype(
        np.int32,
        copy=False,
    )


def _measure_stained_area_by_cell(
    compartments: np.ndarray,
    stained_mask: np.ndarray,
    cell_count: int,
    pixel_size_um: float,
) -> np.ndarray:
    """Measure W2 stained area in square micrometers for every W1 cell."""

    stained_cell_labels = compartments[stained_mask & (compartments > 0)]
    stained_pixels = np.bincount(
        stained_cell_labels,
        minlength=cell_count + 1,
    ).astype(float, copy=False)
    return stained_pixels * pixel_size_um**2


def _segment_simple_slice(
    slice_data: np.ndarray,
    settings: SimpleCellSegmentationConfig,
) -> np.ndarray:
    """Segment one 2D plane with the simple counter's canonical logic."""
    foreground = Foreground(settings.foreground)
    threshold_value = _compute_threshold(
        slice_data,
        settings,
    )

    if foreground == Foreground.BRIGHT:
        binary = slice_data > threshold_value
    elif foreground == Foreground.DARK:
        binary = slice_data < threshold_value
    else:
        raise ValueError(
            f"Unknown foreground: {foreground!r} (expected 'bright' or 'dark')"
        )

    labeled = _label_binary_components(
        binary,
        watershed_large_objects=settings.watershed_large_objects,
        watershed_split_size=(
            settings.max_size
            if settings.watershed_min_size is None
            else settings.watershed_min_size
        ),
        watershed_max_size=settings.watershed_max_size,
        watershed_min_distance=settings.watershed_min_distance,
        watershed_footprint_size=settings.watershed_footprint_size,
    )

    if labeled.max() == 0:
        return np.zeros_like(labeled, dtype=np.int32)

    if settings.max_eccentricity == 1.0:
        return _filter_labels_by_area(
            labeled,
            min_size=settings.min_size,
            max_size=settings.max_size,
        )

    keep_mask = np.zeros(int(labeled.max()) + 1, dtype=bool)
    for region in regionprops(labeled):
        if (
            settings.min_size <= region.area <= settings.max_size
            and region.eccentricity <= settings.max_eccentricity
        ):
            keep_mask[region.label] = True

    return _relabel_by_keep_mask(labeled, keep_mask)


def _label_binary_components(
    binary: np.ndarray,
    *,
    watershed_large_objects: bool,
    watershed_split_size: int,
    watershed_max_size: Optional[int],
    watershed_min_distance: int,
    watershed_footprint_size: int,
    watershed_peak_prominence: float = 0.0,
    watershed_marker_image: Optional[np.ndarray] = None,
    watershed_marker_smoothing_sigma: float = 0.0,
    watershed_marker_peak_prominence: float = 0.0,
) -> np.ndarray:
    """Label a binary mask and optionally split large connected components."""

    return _label_binary_component_stages(
        binary,
        watershed_large_objects=watershed_large_objects,
        watershed_split_size=watershed_split_size,
        watershed_max_size=watershed_max_size,
        watershed_min_distance=watershed_min_distance,
        watershed_footprint_size=watershed_footprint_size,
        watershed_peak_prominence=watershed_peak_prominence,
        watershed_marker_image=watershed_marker_image,
        watershed_marker_smoothing_sigma=watershed_marker_smoothing_sigma,
        watershed_marker_peak_prominence=watershed_marker_peak_prominence,
    ).output_labels


@dataclass(frozen=True)
class BinaryComponentStages:
    """Connected-component identities before and after optional splitting."""

    source_labels: np.ndarray
    output_labels: np.ndarray
    source_component_by_output: np.ndarray


def _label_binary_component_stages(
    binary: np.ndarray,
    *,
    watershed_large_objects: bool,
    watershed_split_size: int,
    watershed_max_size: Optional[int],
    watershed_min_distance: int,
    watershed_footprint_size: int,
    watershed_peak_prominence: float = 0.0,
    watershed_marker_image: Optional[np.ndarray] = None,
    watershed_marker_smoothing_sigma: float = 0.0,
    watershed_marker_peak_prominence: float = 0.0,
) -> BinaryComponentStages:
    """Retain source-component lineage across optional watershed splitting."""

    source_labels, num_objects = ndi.label(binary)
    output_labels = source_labels
    if watershed_large_objects and num_objects > 0:
        output_labels = _watershed_large_objects(
            source_labels,
            split_size=watershed_split_size,
            watershed_max_size=watershed_max_size,
            min_distance=watershed_min_distance,
            footprint_size=watershed_footprint_size,
            peak_prominence=watershed_peak_prominence,
            marker_image=watershed_marker_image,
            marker_smoothing_sigma=watershed_marker_smoothing_sigma,
            marker_peak_prominence=watershed_marker_peak_prominence,
        )
    source_labels = source_labels.astype(np.int32, copy=False)
    output_labels = output_labels.astype(np.int32, copy=False)
    source_component_by_output = np.zeros(
        int(output_labels.max()) + 1,
        dtype=np.int32,
    )
    foreground = output_labels > 0
    np.maximum.at(
        source_component_by_output,
        output_labels[foreground],
        source_labels[foreground],
    )
    return BinaryComponentStages(
        source_labels,
        output_labels,
        source_component_by_output,
    )


def _filter_labels_by_area(
    labeled: np.ndarray,
    *,
    min_size: int,
    max_size: int,
) -> np.ndarray:
    """Filter labels by pixel area and relabel accepted objects densely."""
    counts = np.bincount(labeled.ravel())
    keep_mask = (counts >= min_size) & (counts <= max_size)
    return _relabel_by_keep_mask(labeled, keep_mask)


def _relabel_by_keep_mask(labeled: np.ndarray, keep_mask: np.ndarray) -> np.ndarray:
    """Apply a boolean label keep mask and produce dense int32 labels."""
    if keep_mask.size:
        keep_mask[0] = False

    kept_count = int(np.count_nonzero(keep_mask))
    if kept_count == 0:
        return np.zeros_like(labeled, dtype=np.int32)

    remap = np.zeros(keep_mask.shape[0], dtype=np.int32)
    remap[keep_mask] = np.arange(1, kept_count + 1, dtype=np.int32)
    return remap[labeled]


def _compute_threshold(
    slice_data: np.ndarray,
    settings: SimpleCellSegmentationConfig,
) -> float:
    """Compute one threshold in the native intensity scale of a 2D plane."""
    threshold_method = ThresholdMethod(settings.threshold_method)
    if threshold_method == ThresholdMethod.OTSU:
        return float(threshold_otsu(slice_data))
    if threshold_method == ThresholdMethod.LI:
        return float(threshold_li(slice_data))
    if threshold_method == ThresholdMethod.YEN:
        return float(threshold_yen(slice_data))
    if threshold_method == ThresholdMethod.PERCENTILE:
        return float(np.percentile(slice_data, settings.threshold_percentile))
    if threshold_method == ThresholdMethod.MANUAL:
        threshold_value = float(settings.threshold)
        if 0.0 <= threshold_value <= 1.0:
            max_val = float(np.max(slice_data))
            if max_val > 1.0:
                threshold_value *= max_val
        return threshold_value
    raise ValueError(f"Unknown threshold_method: {threshold_method!r}")


def _watershed_large_objects(
    labeled: np.ndarray,
    split_size: int,
    watershed_max_size: Optional[int],
    min_distance: int,
    footprint_size: int,
    peak_prominence: float = 0.0,
    marker_image: Optional[np.ndarray] = None,
    marker_smoothing_sigma: float = 0.0,
    marker_peak_prominence: float = 0.0,
) -> np.ndarray:
    """Split components above split_size and at or below watershed_max_size."""
    counts = np.bincount(labeled.ravel())
    split_mask = counts > split_size
    if watershed_max_size is not None:
        split_mask &= counts <= watershed_max_size
    if split_mask.size:
        split_mask[0] = False

    split_labels = np.flatnonzero(split_mask)
    if split_labels.size == 0:
        return labeled.astype(np.int32, copy=False)

    footprint = np.ones((footprint_size, footprint_size), dtype=bool)

    def peak_coordinates(
        surface: np.ndarray,
        component: np.ndarray,
        prominence: float,
    ) -> np.ndarray:
        peak_support = h_maxima(surface, prominence) if prominence > 0.0 else component
        peak_components, _ = ndi.label(peak_support & component)
        return peak_local_max(
            surface,
            min_distance=min_distance,
            footprint=footprint,
            labels=peak_components,
            num_peaks_per_label=1 if prominence > 0.0 else np.inf,
            exclude_border=False,
        )

    marker_array = None
    if marker_image is not None:
        marker_array = np.asarray(marker_image, dtype=float)
        if marker_array.shape != labeled.shape:
            raise ValueError("watershed marker image must match the label plane")

    output = labeled.astype(np.int32, copy=True)
    object_slices = ndi.find_objects(labeled)
    next_label = int(labeled.max()) + 1
    minimum_fragment_area = max(1, int(np.floor(split_size / 2.0)))

    for label_id in split_labels:
        component_slice = object_slices[label_id - 1]
        if component_slice is None:
            continue

        component = labeled[component_slice] == label_id
        filled_component = ndi.binary_fill_holes(component)
        distance = ndi.distance_transform_edt(np.pad(filled_component, 1))[1:-1, 1:-1]
        shape_seeds = peak_coordinates(distance, component, peak_prominence)
        substantial_hole = (
            np.count_nonzero(filled_component) - np.count_nonzero(component)
            >= minimum_fragment_area
        )

        marker_surface = None
        intensity_seeds = np.empty((0, 2), dtype=np.intp)
        if marker_array is not None and not substantial_hole:
            marker_component = marker_array[component_slice]
            if marker_smoothing_sigma > 0.0:
                weights = ndi.gaussian_filter(
                    component.astype(float), marker_smoothing_sigma
                )
                weighted = ndi.gaussian_filter(
                    np.where(component, marker_component, 0.0),
                    marker_smoothing_sigma,
                )
                marker_surface = np.divide(
                    weighted,
                    weights,
                    out=np.zeros_like(weighted),
                    where=weights > np.finfo(float).eps,
                )
            else:
                marker_surface = marker_component
            intensity_seeds = peak_coordinates(
                marker_surface,
                component,
                marker_peak_prominence,
            )

        use_intensity = marker_surface is not None
        seeds = intensity_seeds if use_intensity else shape_seeds
        if len(seeds) <= 1:
            continue

        markers = np.zeros_like(component, dtype=np.int32)
        markers[seeds[:, 0], seeds[:, 1]] = np.arange(1, len(seeds) + 1)
        split_surface = marker_surface if use_intensity else distance
        component_splits = watershed(-split_surface, markers, mask=component)
        if use_intensity:
            fragment_areas = np.bincount(component_splits.ravel())[1:]
            if np.any(fragment_areas < minimum_fragment_area):
                continue

        output_view = output[component_slice]
        output_view[component] = 0
        for split_label in range(1, int(component_splits.max()) + 1):
            output_view[component_splits == split_label] = next_label
            next_label += 1

    return output
