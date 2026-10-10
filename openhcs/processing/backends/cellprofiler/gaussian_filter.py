"""
Converted from CellProfiler: GaussianFilter
Original: gaussianfilter
"""

from typing import ClassVar

from openhcs.core.callable_contract import runtime_image_execution_mode
from openhcs.core.runtime_array_values import RuntimeArrayData
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_float,
)
from openhcs.interop.cellprofiler.module_declarations import (
    CellProfilerModule,
)
from openhcs.core.artifacts import ImageArtifactType
from openhcs.core.image_payload_execution_mode import (
    FullStackExecution,
)


class GaussianFilterModule(CellProfilerModule):
    module_name = "GaussianFilter"
    function_name = "gaussian_filter"
    validated = True
    confidence = 1.0
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select the input image", ImageArtifactType),
        SettingToKeywordBinding.output("Name the output image", ImageArtifactType),
        SettingToKeywordBinding("Sigma", "sigma", parse_cellprofiler_float),
    )


import numpy as np
from openhcs.core.memory.decorators import numpy
from openhcs.core.processing_contracts import (
    FlexibleContract,
)
from openhcs.core.runtime_image_values import ImagePayload


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
def gaussian_filter(image: ImagePayload, sigma: float = 1.0) -> np.ndarray:
    """
    Apply CellProfiler-compatible Gaussian smoothing to an image.

    CellProfiler divides the user sigma by physical voxel spacing before
    invoking the library filter. Assembled source cohorts and channels are
    independent images, not additional physical dimensions.
    """
    from skimage.filters import gaussian as skimage_gaussian

    pixel_data = np.asarray(image.data)
    metadata = image.metadata
    spatial_axes = metadata.spatial_axes(pixel_data)
    spacing = metadata.source_voxel_spacing.spacing_for_ndim(len(spatial_axes))
    effective_sigma = np.zeros(pixel_data.ndim, dtype=np.float64)
    effective_sigma[list(spatial_axes)] = np.divide(
        float(sigma), np.asarray(spacing, dtype=np.float64)
    )
    filtered = skimage_gaussian(pixel_data, sigma=effective_sigma)
    return image.with_pixels(filtered)
