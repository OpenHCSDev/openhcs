"""Compiled raw calls preserve metadata required by declared image consumers."""

from dataclasses import replace

import numpy as np
from scipy import ndimage

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.function_patterns import NormalizeFunctionGroupAuthority
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
    normalize_image_payload_intensity,
)
from openhcs.core.runtime_object_label_building import SourceImageObjectLabelBuildRequest
from openhcs.core.runtime_object_labels import object_label_dense_array
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.processing.backends.cellprofiler.color import ColorToGrayMode, color_to_gray
from openhcs.processing.backends.cellprofiler.median_filter import medianfilter
from openhcs.processing.backends.cellprofiler.secondary import (
    SecondaryMethod,
    identify_secondary_objects,
)


def _execute_prepared(func, source, kwargs, mode=ImagePayloadExecutionMode.NATURAL):
    contract = NormalizeFunctionGroupAuthority().normalize("image", func).items[0].contract
    contract = replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )
    assert contract.metadata.canonical_signature is not None
    assert contract.raw_main_flow_call_argument(source) is source
    return CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        source,
        kwargs,
        execution_mode=mode,
    )


def test_prepared_color_to_gray_preserves_channel_mask_and_spatial_domain():
    pixels = np.arange(4 * 5 * 3, dtype=np.float32).reshape(4, 5, 3)
    mask = np.ones(pixels.shape[:2], dtype=bool)
    mask[0] = False
    mask[-1] = False
    domain = SourceSpatialDomain(origin_yx=(2, 3), source_shape_yx=(8, 10))
    source = ImagePayloadMetadata(
        source_channel_axis=-1,
        source_image_names=("RGB",),
        source_path="/input/rgb.tif",
        source_spatial_domain=domain,
    ).payload_with(pixels, mask)

    result = _execute_prepared(
        color_to_gray, source,
        {"mode": ColorToGrayMode.COMBINE,
         "channel_indices": (0, 2), "contributions": (1.0, 3.0)},
    )

    np.testing.assert_array_equal(image_payload_data(result), (pixels[..., 0] + 3 * pixels[..., 2]) / 4)
    np.testing.assert_array_equal(image_payload_mask(result), mask)
    metadata = image_payload_metadata(result)
    assert metadata.source_channel_axis is None
    assert metadata.source_spatial_domain == domain
    assert metadata.source_image_paths == ("/input/rgb.tif",)


def test_prepared_medianfilter_keeps_original_intensity_scale_and_mask():
    pixels = np.arange(25, dtype=np.uint16).reshape(5, 5)
    mask = np.ones(pixels.shape, dtype=bool)
    mask[0] = False
    source = normalize_image_payload_intensity(
        ImagePayloadMetadata.for_array(pixels).payload_with(pixels, mask),
        dtype=np.float32,
    )

    result = _execute_prepared(
        medianfilter, source, {"window_size": 3}, ImagePayloadExecutionMode.FULL_STACK,
    )

    np.testing.assert_array_equal(
        image_payload_data(result),
        ndimage.median_filter(image_payload_data(source), size=3, mode="constant"),
    )
    np.testing.assert_array_equal(image_payload_mask(result), mask)
    assert image_payload_metadata(result).unit_interval_intensity_scale == 65535
    assert image_payload_data(result).dtype == np.float32


def test_prepared_secondary_object_output_keeps_actual_source_spatial_domain():
    pixels = np.zeros((9, 9), dtype=np.float32)
    domain = SourceSpatialDomain(origin_yx=(3, 4), source_shape_yx=(15, 16))
    source = ImagePayloadMetadata(
        source_image_names=("DNA",), source_path="/input/dna.tif",
        source_spatial_domain=domain,
    ).payload_with(pixels, None)
    seed_pixels = np.zeros(pixels.shape, dtype=np.int32)
    seed_pixels[4, 4] = 1
    seeds = SourceImageObjectLabelBuildRequest(
        image=source, labels=seed_pixels, declared_object_ids=(1,),
    ).payload()

    result = _execute_prepared(
        identify_secondary_objects, source,
        {"primary_labels": seeds, "method": SecondaryMethod.DISTANCE_N,
         "distance_to_dilate": 1, "fill_holes": False},
    )

    _image, _rows, relationship, objects = result
    expected = ndimage.distance_transform_edt(seed_pixels == 0) <= 1
    np.testing.assert_array_equal(object_label_dense_array(objects), expected.astype(np.int32))
    assert objects.source_spatial_domain.origin_yx == domain.origin_yx
    assert objects.source_spatial_domain.source_shape_yx == domain.source_shape_yx
    assert objects.source_provenance == image_payload_metadata(source).source_provenance
    assert relationship.source_ids == (1,)
    assert relationship.target_ids == (1,)
