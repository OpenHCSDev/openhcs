"""CellProfiler plugin HistogramEqualization.

Upstream: CellProfiler-plugins ``active_plugins/histogramequalization.py``.
"""

from typing import ClassVar

import numpy as np

from openhcs.core.artifacts.kinds import ImageArtifactType
from openhcs.core.callable_contract import runtime_image_execution_mode
from openhcs.core.image_payload_execution_mode import FullStackExecution
from openhcs.core.memory.decorators import numpy
from openhcs.core.pipeline.function_contracts import special_inputs
from openhcs.core.processing_contracts import FlexibleContract
from openhcs.core.runtime_image_values import ImagePayload
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.setting_names import SettingNameFamily
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
    parse_cellprofiler_float,
    parse_cellprofiler_int,
)


class HistogramEqualizationModule(CellProfilerModule):
    module_name = "HistogramEqualization"
    function_name = "histogram_equalization"
    validated = True
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select the input image", ImageArtifactType),
        SettingToKeywordBinding.output("Name the output image", ImageArtifactType),
        SettingToKeywordBinding("Bins", "bins", parse_cellprofiler_int),
        SettingToKeywordBinding.input(
            "Mask", ImageArtifactType, runtime_parameter_name="mask_image"
        ),
        SettingToKeywordBinding("Local", "local", parse_cellprofiler_bool),
        SettingToKeywordBinding("Tile Size", "tile_size", parse_cellprofiler_int),
        SettingToKeywordBinding("Clip limit", "clip_limit", parse_cellprofiler_float),
        SettingToKeywordBinding(
            # Pipelines saved by earlier plugin versions carry the misspelling.
            SettingNameFamily("Is your image 3D?", aliases=("Is you image 3D?",)),
            "planes_form_a_volume",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding(
            "Do framewise calculation?", "framewise", parse_cellprofiler_bool
        ),
        SettingToKeywordBinding(
            "Tile Size (Z)", "tile_size_z", parse_cellprofiler_int
        ),
    )


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
@special_inputs("mask_image")
def histogram_equalization(
    image: ImagePayload,
    mask_image: np.ndarray | None = None,
    bins: int = 256,
    local: bool = False,
    tile_size: int = 50,
    clip_limit: float = 0.01,
    planes_form_a_volume: bool = False,
    framewise: bool = False,
    tile_size_z: int = 5,
) -> ImagePayload:
    """Spread an image's intensities over the full range to raise contrast.

    The global method maps every pixel through the image's cumulative
    histogram (scikit-image ``equalize_hist``). The local method equalizes
    within tiles and limits how much any intensity is amplified
    (``equalize_adapthist``, CLAHE). Each image of a stack (2D plane or 3D
    volume, as its metadata declares) is equalized on its own.

    The plugin's quirks are kept. Whether a volume is treated as one is decided
    by ``planes_form_a_volume``, not by the image: left off, a volume still
    goes to scikit-image whole, with ``tile_size`` on all three axes for the
    local method; turned on for a 2D image, ``framewise`` equalizes row by row.
    The mask is another image's pixels (non-zero means inside), not the image's
    own mask, which is ignored although the plugin's documentation says masks
    are respected. The local method does not use the mask. A mask together with
    ``planes_form_a_volume`` and ``framewise`` fails in the plugin (it offers
    the whole mask to each plane) and is refused here.

    Args:
        mask_image: Image whose non-zero pixels select what the global histogram is
            computed from; the mapping is still applied to every pixel. Same
            shape as the image.
        bins: Number of histogram bins.
        local: Equalize within tiles (CLAHE) instead of over the whole image.
        tile_size: Tile edge in pixels for the local method; pick one that fits
            at least one object of interest.
        clip_limit: Local method only, 0 to 1; higher gives more contrast and
            more amplified background.
        planes_form_a_volume: Apply the 3D options below.
        framewise: With ``planes_form_a_volume``, equalize each plane on its
            own instead of the volume as a whole.
        tile_size_z: Tile depth in planes for the local method on a whole
            volume.
    """
    from skimage.exposure import equalize_adapthist, equalize_hist

    each_plane = planes_form_a_volume and framewise
    if mask_image is not None and not local and each_plane:
        raise ValueError(
            "HistogramEqualization cannot use a mask when equalizing a volume "
            "framewise: the CellProfiler plugin fails on this combination."
        )
    kernel_size = (
        (tile_size_z, tile_size, tile_size)
        if planes_form_a_volume and not framewise
        else tile_size
    )

    def equalize(pixels: np.ndarray, pixels_mask: np.ndarray | None) -> np.ndarray:
        if local:
            return equalize_adapthist(
                pixels, kernel_size=kernel_size, nbins=bins, clip_limit=clip_limit
            )
        # In double precision, as the scikit-image CellProfiler pins computes it.
        return equalize_hist(pixels.astype(np.float64), nbins=bins, mask=pixels_mask)

    pixels = np.asarray(image.data)
    masks = (
        None
        if mask_image is None
        else np.broadcast_to(ImagePayload.of(mask_image).data, pixels.shape)
    )
    spatial_rank = image.metadata.source_spatial_domain.spatial_rank
    equalized = np.empty(pixels.shape, dtype=np.float32)
    for index in np.ndindex(pixels.shape[: pixels.ndim - spatial_rank]):
        one_image = pixels[index]
        one_mask = None if masks is None else masks[index]
        equalized[index] = (
            np.stack([equalize(plane, one_mask) for plane in one_image])
            if each_plane
            else equalize(one_image, one_mask)
        )
    return image.with_pixels(equalized)
