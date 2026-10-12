"""CellProfiler plugin DistanceTransform.

Upstream: CellProfiler-plugins ``active_plugins/distancetransform.py``.
"""

from typing import ClassVar

import numpy as np

from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.callable_contract import runtime_image_execution_mode
from openhcs.core.image_payload_execution_mode import FullStackExecution
from openhcs.core.image_shapes import apply_over_trailing_spatial_axes
from openhcs.core.memory.decorators import numpy
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
)


class DistanceTransformModule(CellProfilerModule):
    module_name = "DistanceTransform"
    function_name = "distance_transform"
    validated = True
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select the input image", ImageArtifactType),
        SettingToKeywordBinding.output("Name the output image", ImageArtifactType),
        SettingToKeywordBinding(
            "Rescale values from 0 to 1?", "rescale", parse_cellprofiler_bool
        ),
    )


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
def distance_transform(image: ImagePayload, rescale: bool = True) -> ImagePayload:
    """Distance of every non-zero pixel to the nearest zero pixel.

    Distances are Euclidean and in units of the Y pixel size: the voxel spacing
    is divided by its second entry, as CellProfiler does, so a volume with
    thicker planes measures further across planes than within one. Each image
    of a stack (2D plane or 3D volume, as its metadata declares) is transformed
    on its own.

    The plugin's quirks are kept. Its documentation says it respects masks, but
    the image mask does not take part: masked pixels count as image content,
    and the output carries the input's mask. An image with no non-zero pixel
    divides zero by zero when rescaling and becomes all NaN.

    Args:
        rescale: Divide by the image's largest distance, giving values from 0 to
            1. Leave off to keep distances in pixel units.
    """
    from scipy.ndimage import distance_transform_edt

    pixels = np.asarray(image.data)
    spatial_rank = image.metadata.source_spatial_domain.spatial_rank
    spacing = image.metadata.source_voxel_spacing.spacing_for_ndim(spatial_rank)
    relative_spacing = tuple(np.divide(spacing, spacing[1]))

    def distances_of_one_image(one_image: np.ndarray) -> np.ndarray:
        distances = distance_transform_edt(one_image, sampling=relative_spacing)
        return distances / np.max(distances) if rescale else distances

    return image.with_pixels(
        apply_over_trailing_spatial_axes(
            pixels, spatial_rank, distances_of_one_image, dtype=np.float32
        ).astype(np.float32, copy=False)
    )
