"""CellProfiler plugin HistogramMatching.

Upstream: CellProfiler-plugins ``active_plugins/histogrammatching.py``.
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
from openhcs.core.source_spatial_domain import VolumeSourceSpatialDomain
from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.interop.cellprofiler.setting_names import SettingNameFamily
from openhcs.interop.cellprofiler.settings_binder import (
    SettingToKeywordBinding,
    parse_cellprofiler_bool,
    parse_cellprofiler_int,
)


class HistogramMatchingModule(CellProfilerModule):
    module_name = "HistogramMatching"
    function_name = "histogram_matching"
    validated = True
    ignored_settings = (
        # The plugin only uses this to show or hide other settings; what it
        # computes depends on whether the image itself is a volume. Pipelines
        # saved by earlier plugin versions carry the misspelling.
        SettingNameFamily("Is your image 3D?", aliases=("Is you image 3D?",)),
        # Written by a fork of the plugin (seen in TrynkaLab/tglow-pipeline);
        # the plugin this module reproduces has no such setting.
        "Plane number in 3d",
    )
    setting_bindings: ClassVar[tuple[SettingToKeywordBinding, ...]] = (
        SettingToKeywordBinding.input("Select the input image", ImageArtifactType),
        SettingToKeywordBinding.output("Name the output image", ImageArtifactType),
        SettingToKeywordBinding(
            "Use a frame within image as reference?",
            "frame_is_reference",
            parse_cellprofiler_bool,
        ),
        SettingToKeywordBinding.input(
            "Image to use as reference",
            ImageArtifactType,
            runtime_parameter_name="reference",
        ),
        SettingToKeywordBinding("Frame number", "frame_number", parse_cellprofiler_int),
    )


@runtime_image_execution_mode(FullStackExecution)
@numpy(contract=FlexibleContract)
@special_inputs("reference")
def histogram_matching(
    image: ImagePayload,
    reference: np.ndarray | None = None,
    frame_is_reference: bool = False,
    frame_number: int = 5,
) -> ImagePayload:
    """Remap an image's intensities so its histogram matches a reference's.

    Uses scikit-image ``match_histograms``. A 2D image is matched to the
    reference image, which may have another shape. In a volume every plane is
    matched to one plane of the same volume. Each image of a stack (2D plane or
    3D volume, as its metadata declares) is matched on its own.

    The plugin's quirks are kept. Which branch runs depends on the image, not
    on the plugin's "Is your image 3D?" setting, which is not a parameter here.
    A 2D image always uses the reference image, whatever ``frame_is_reference``
    says. A volume matched to a reference image fails in the plugin and is
    refused here. ``frame_number`` counts from zero although the plugin's
    setting only accepts 1 and above, so the plugin cannot pick the first
    plane; here 0 picks it.

    Args:
        reference: Image whose intensity distribution a 2D image takes on.
        frame_is_reference: For a volume, match every plane to the plane chosen
            by ``frame_number``. A volume requires this.
        frame_number: Zero-based index of the reference plane within a volume.
    """
    from skimage.exposure import match_histograms

    volumetric = isinstance(
        image.metadata.source_spatial_domain, VolumeSourceSpatialDomain
    )
    if volumetric and not frame_is_reference:
        raise ValueError(
            "HistogramMatching cannot match a volume to a reference image: the "
            "CellProfiler plugin fails on this combination. Use a frame within "
            "the image as reference."
        )
    if not volumetric and reference is None:
        raise ValueError("HistogramMatching of a 2D image requires a reference image.")

    pixels = np.asarray(image.data)
    reference_pixels = (
        None if reference is None else np.asarray(ImagePayload.of(reference).data)
    )
    spatial_rank = image.metadata.source_spatial_domain.spatial_rank
    matched = np.empty(pixels.shape, dtype=np.float32)
    for index in np.ndindex(pixels.shape[: pixels.ndim - spatial_rank]):
        one_image = pixels[index]
        if volumetric:
            frame = one_image[frame_number]
            matched[index] = np.stack(
                [match_histograms(plane, frame) for plane in one_image]
            )
        else:
            matched[index] = match_histograms(
                one_image,
                reference_pixels[index]
                if reference_pixels.ndim == pixels.ndim
                else reference_pixels,
            )
    return image.with_pixels(matched)
