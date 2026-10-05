"""Object-label image rendering for CellProfiler-compatible processing."""

from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass
from enum import Enum
from functools import lru_cache
from typing import Annotated, ClassVar

from metaclass_registry import AutoRegisterMeta
import numpy as np
from numba import njit

from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.core.artifacts import ImageArtifactType, ObjectLabelsArtifactType
from openhcs.core.memory import numpy as numpy_decorator
from openhcs.core.measurement_row_materialization import (
    DataclassMeasurementColumnarRows,
)
from openhcs.core.pipeline.function_contracts import (
    ObjectLabelInputExecutionMode,
    object_label_input_execution_mode,
    special_inputs,
)
from openhcs.core.public_api import public_names_from_objects
from openhcs.core.processing_preparation import PersistentNumbaKernelPreparation
from openhcs.core.registry_strategies import EnumKeyedStrategyMixin
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_metadata,
    with_image_payload_data,
)
from openhcs.core.runtime_measurements import MeasurementRowAxisField
from openhcs.core.runtime_object_label_building import (
    SourceImageObjectLabelBuildRequest,
)
from openhcs.core.runtime_object_labels import (
    ObjectLabelValue,
    object_label_dense_array,
)
from openhcs.interop.cellprofiler.module_artifact_declarations import (
    MeasurementArtifactOutputModule,
    ObjectArtifactInputModule,
    ObjectArtifactOutputModule,
)
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.runtime.measurement_recording import (
    MeasurementFeatureRecord,
)
from openhcs.interop.cellprofiler.setting_names import SettingNameFamily
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    cellprofiler_enum_setting_parser,
    coerce_cellprofiler_enum,
    parse_cellprofiler_bool,
    parse_cellprofiler_int,
)
from openhcs.processing.backends.analysis.region_properties import (
    LabelRegionPropertiesBackendStrategy,
)
from openhcs.processing.backends.lib_registry.unified_registry import (
    ProcessingContract,
)


class ImageMode(Enum):
    """Object-label rendering modes exposed by ConvertObjectsToImage."""

    BINARY = "binary"
    GRAYSCALE = "grayscale"
    COLOR = "color"
    UINT16 = "uint16"


class ConvertObjectsToImageModule(
    ObjectArtifactInputModule,
    CellProfilerModule,
):
    module_name = "ConvertObjectsToImage"
    function_name = "convert_objects_to_image"
    validated = True
    confidence = 1.0
    input_objects_setting = SettingNameFamily("Select the input objects")
    output_image_setting = SettingNameFamily("Name the output image")
    setting_bindings = (
        SettingToKeywordBinding.input(
            input_objects_setting,
            ObjectLabelsArtifactType,
            runtime_parameter_name="labels",
        ),
        SettingToKeywordBinding.output(output_image_setting, ImageArtifactType),
        SettingToKeywordBinding(
            "Select the color format",
            "image_mode",
            cellprofiler_enum_setting_parser(ImageMode),
        ),
        SettingToKeywordBinding("Select the colormap", "colormap_value"),
    )


@dataclass(frozen=True, slots=True)
class ObjectConversionStats(MeasurementFeatureRecord):
    """ConvertImageToObjects summary row."""

    slice_index: Annotated[int, MeasurementRowAxisField.SLICE_INDEX]
    object_count: int
    mean_area: float
    total_area: int


class ImageModeRenderer(
    EnumKeyedStrategyMixin[ImageMode],
    PersistentNumbaKernelPreparation,
    ABC,
    metaclass=AutoRegisterMeta,
):
    """Render object labels for one closed ImageMode case."""

    __enum_member_attr__ = "image_mode"
    image_mode: ClassVar[ImageMode | None] = None

    @classmethod
    def prepare_registered_family(cls) -> None:
        for renderer in cls.registered_strategy_types():
            renderer.prepare_rendering()

    @classmethod
    def prepare_rendering(cls) -> None:
        """Prepare computational kernels required by this rendering mode."""

    @abstractmethod
    def render(self, labels: np.ndarray, *, colormap_value: str) -> np.ndarray:
        """Return one rendered image payload for the requested ImageMode."""


class BinaryImageModeRenderer(ImageModeRenderer):
    image_mode = ImageMode.BINARY

    def render(self, labels: np.ndarray, *, colormap_value: str) -> np.ndarray:
        del colormap_value
        return (labels > 0).astype(np.float32)


class GrayscaleImageModeRenderer(ImageModeRenderer):
    image_mode = ImageMode.GRAYSCALE

    def render(self, labels: np.ndarray, *, colormap_value: str) -> np.ndarray:
        del colormap_value
        max_label = labels.max()
        if max_label > 0:
            return labels.astype(np.float32) / max_label
        return np.zeros(labels.shape, dtype=np.float32)


class ColorImageModeRenderer(ImageModeRenderer):
    image_mode = ImageMode.COLOR

    def render(self, labels: np.ndarray, *, colormap_value: str) -> np.ndarray:
        max_label = labels.max()
        colors = self.palette(colormap_value, max_label)
        pixel_data = colors[labels]
        return (
            np.float32(0.299) * pixel_data[..., 0]
            + np.float32(0.587) * pixel_data[..., 1]
            + np.float32(0.114) * pixel_data[..., 2]
        ).astype(np.float32, copy=False)

    @staticmethod
    def palette(colormap_name: str, num_labels: int) -> np.ndarray:
        """Return label-indexed colors with an explicit black background row."""
        from matplotlib import colormaps

        cmap = colormaps.get_cmap(colormap_name)
        colors = np.zeros((num_labels + 1, 3), dtype=np.float32)
        for index in range(1, num_labels + 1):
            colors[index] = cmap(index / max(num_labels, 1))[:3]
        return colors

    @classmethod
    @lru_cache(maxsize=256)
    def blend_palette(cls, colormap_name: str, num_labels: int) -> np.ndarray:
        """Retain the positive-label palette for repeated indexed blending."""
        return cls.palette(colormap_name, max(num_labels, 0))[1:]

    @classmethod
    def blend_image(
        cls,
        grayscale: np.ndarray,
        labels: np.ndarray,
        *,
        opacity: float,
        max_label: int | None,
        seed: int | None,
        colormap_value: str,
    ) -> np.ndarray:
        """Blend indexed label colors into one grayscale plane or volume."""
        if grayscale.shape != labels.shape:
            raise ValueError(
                "Indexed label colors and grayscale pixels must exactly match; "
                f"got {grayscale.shape!r} and {labels.shape!r}."
            )
        if labels.ndim not in (2, 3):
            raise ValueError(
                "Indexed color blending requires 2-D or 3-D object labels, got "
                f"shape {labels.shape!r}."
            )
        is_plane = labels.ndim == 2
        if is_plane:
            grayscale = grayscale[None, ...]
            labels = labels[None, ...]
        normalized = np.empty(grayscale.shape, dtype=np.float32)
        for index, plane in enumerate(grayscale):
            maximum = plane.max()
            normalized[index] = plane / maximum if maximum > 1.0 else plane
        label_count = int(labels.max()) if max_label is None else int(max_label)
        if seed is not None:
            np.random.seed(seed)
        colors = cls.blend_palette(colormap_value, label_count)
        if seed is not None and len(grayscale) > 1:
            # Each later plane historically reset the seed before its palette hit.
            np.random.seed(seed)
        weight_dtype = np.result_type(np.empty((0,), dtype=np.float32), opacity)
        output = _blend_label_colors(
            normalized,
            np.ascontiguousarray(labels, dtype=np.int32),
            colors,
            weight_dtype.type(1.0 - opacity),
            weight_dtype.type(opacity),
        )
        return output[0] if is_plane else output

    @classmethod
    def prepare_rendering(cls) -> None:
        image = np.zeros((1, 2, 2), dtype=np.float32)
        labels = np.ones(image.shape, dtype=np.int32)
        for readonly in (False, True):
            labels.setflags(write=not readonly)
            for opacity in (0.3, np.float64(0.3)):
                cls.blend_image(
                    image,
                    labels,
                    opacity=opacity,
                    max_label=1,
                    seed=None,
                    colormap_value="jet",
                )


@njit(cache=True)
def _blend_label_colors(grayscale, labels, colors, background_weight, color_weight):
    """Write final RGB pixels without foreground gathers or blend temporaries."""
    output = np.empty((*grayscale.shape, 3), dtype=np.float32)
    for z in range(grayscale.shape[0]):
        for y in range(grayscale.shape[1]):
            for x in range(grayscale.shape[2]):
                gray = grayscale[z, y, x]
                label = labels[z, y, x]
                for channel in range(3):
                    value = gray
                    if label > 0 and colors.shape[0] > 0:
                        color_index = (label - 1) % colors.shape[0]
                        value = (
                            background_weight * gray
                            + color_weight * colors[color_index, channel]
                        )
                    if value < 0.0:
                        value = 0.0
                    if value > 1.0:
                        value = 1.0
                    output[z, y, x, channel] = value
    return output


class Uint16ImageModeRenderer(ImageModeRenderer):
    image_mode = ImageMode.UINT16

    def render(self, labels: np.ndarray, *, colormap_value: str) -> np.ndarray:
        del colormap_value
        minimum = int(labels.min(initial=0))
        maximum = int(labels.max(initial=0))
        if minimum < 0 or maximum > np.iinfo(np.uint16).max:
            raise ValueError(
                "ConvertObjectsToImage uint16 labels must be in the inclusive "
                f"range 0..65535, got {minimum}..{maximum}."
            )
        return labels.astype(np.uint16, copy=False)


@numpy_decorator(contract=ProcessingContract.PURE_2D)
def convert_image_to_objects(
    image: RuntimeArrayData,
    cast_to_bool: bool = False,
    preserve_label: bool = False,
    background: int = 0,
    connectivity: int = 1,
) -> tuple[np.ndarray, DataclassMeasurementColumnarRows, ObjectLabelValue]:
    """Convert an image plane into CellProfiler-compatible object labels.

    Args:
        cast_to_bool: Treat every pixel unequal to ``background`` as foreground
            before labeling.
        preserve_label: Keep non-background pixel values as object IDs instead of
            relabeling connected foreground regions.
        background: Pixel value treated as background and mapped to object label 0.
        connectivity: Neighborhood connectivity used for connected-component
            labeling when ``preserve_label`` is false.
    """
    from skimage.measure import label

    working_image = np.asarray(image).copy()
    if cast_to_bool:
        working_image = (working_image != background).astype(np.uint8)
    if preserve_label:
        labels = working_image.astype(np.int32)
        labels[labels == background] = 0
    else:
        labels = label(working_image != background, connectivity=connectivity).astype(
            np.int32
        )
    props = LabelRegionPropertiesBackendStrategy.for_memory_type().measure_2d(labels)
    object_count = int(props.label.size)
    if object_count > 0:
        mean_area = float(np.mean(props.area))
        total_area = int(np.sum(props.area))
    else:
        mean_area = 0.0
        total_area = 0
    return (
        image,
        DataclassMeasurementColumnarRows(
            (
                ObjectConversionStats(
                    slice_index=0,
                    object_count=object_count,
                    mean_area=mean_area,
                    total_area=total_area,
                ),
            ),
            row_type=ObjectConversionStats,
        ),
        SourceImageObjectLabelBuildRequest(
            image=image,
            labels=labels,
            declared_object_count=object_count,
            declared_object_ids=tuple(int(value) for value in props.label),
        ).payload(),
    )


@numpy_decorator(contract=ProcessingContract.PURE_3D)
@object_label_input_execution_mode(ObjectLabelInputExecutionMode.FULL_STACK)
@special_inputs("labels")
def convert_objects_to_image(
    image: np.ndarray,
    labels: ObjectLabelValue,
    image_mode: ImageMode = ImageMode.COLOR,
    colormap_value: str = "jet",
) -> np.ndarray:
    """Render object labels into the requested CellProfiler image mode.

    Args:
        labels: Object-label image or volume to render in the selected image mode.
    """
    del image
    label_array = object_label_dense_array(labels, dtype=np.int32)
    rendered = ImageModeRenderer.for_enum_member(image_mode).render(
        label_array, colormap_value=colormap_value
    )
    label_metadata = image_payload_metadata(labels)
    output_metadata = (
        ImagePayloadMetadata(intensity_scale=1.0).with_source_context_from(
            label_metadata
        )
        if image_mode is ImageMode.UINT16
        else label_metadata
    )
    return with_image_payload_data(
        labels,
        rendered,
        metadata=output_metadata,
    )


class ConvertImageToObjectsModule(
    MeasurementArtifactOutputModule,
    ObjectArtifactOutputModule,
    CellProfilerModule,
):
    module_name = "ConvertImageToObjects"
    function_name = "convert_image_to_objects"
    validated = True
    confidence = 1.0
    input_image_setting = SettingNameFamily("Select the input image")
    output_objects_setting = SettingNameFamily("Name the output objects")
    setting_bindings = (
        SettingToKeywordBinding.input(input_image_setting, ImageArtifactType),
        SettingToKeywordBinding.output(
            output_objects_setting,
            ObjectLabelsArtifactType,
        ),
        SettingToKeywordBinding(
            "Convert to boolean image",
            "cast_to_bool",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "Preserve original labels",
            "preserve_label",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "Background label",
            "background",
            parse_cellprofiler_int,
        ),
        SettingToKeywordBinding(
            "Connectivity",
            "connectivity",
            parse_cellprofiler_int,
        ),
    )


__all__ = public_names_from_objects(
    BinaryImageModeRenderer,
    ColorImageModeRenderer,
    GrayscaleImageModeRenderer,
    ImageMode,
    ImageModeRenderer,
    ObjectConversionStats,
    Uint16ImageModeRenderer,
    convert_image_to_objects,
    convert_objects_to_image,
)
