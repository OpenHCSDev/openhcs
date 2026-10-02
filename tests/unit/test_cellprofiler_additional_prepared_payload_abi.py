"""Prepared raw arguments retain context consumed by nominal CP request owners."""
from dataclasses import replace

import numpy as np
import pytest

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
    normalize_image_payload_intensity,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import (
    CellProfilerFunctionContractExecutor,
)
from openhcs.processing.backends.cellprofiler.alignment import AlignModule, align
from openhcs.processing.backends.cellprofiler.area_occupied import measure_image_area_occupied
from openhcs.processing.backends.cellprofiler.crop import CropModule, crop
from openhcs.processing.backends.cellprofiler.image_quality import measure_image_quality
from openhcs.processing.backends.cellprofiler.intensity import measure_object_intensity
from openhcs.processing.backends.cellprofiler.manual_objects import identify_objects_manually
from openhcs.processing.backends.cellprofiler.object_images import convert_image_to_objects
from openhcs.processing.backends.cellprofiler.thresholding import threshold
from openhcs.processing.backends.cellprofiler.worms import (
    identify_dead_worms,
    untangle_worms,
    untangle_worms_both,
    untangle_worms_with_overlap,
)


def _prepared_contract(func):
    contract = CallableContract.from_callable(func).with_prepared_signature()
    return replace(
        contract,
        metadata=replace(
            contract.metadata,
            runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
        ),
    )


@pytest.mark.parametrize(
    "func",
    (
        align,
        crop,
        measure_image_area_occupied,
        measure_object_intensity,
        measure_image_quality,
        identify_objects_manually,
        convert_image_to_objects,
        identify_dead_worms,
        threshold,
        untangle_worms,
        untangle_worms_with_overlap,
        untangle_worms_both,
    ),
)
def test_prepared_primary_context_consumers_keep_nominal_payload_and_bare_pixels(func):
    pixels = np.arange(60, dtype=np.float32).reshape(4, 5, 3)
    mask = np.ones((4, 5), dtype=bool)
    mask[0] = False
    source = ImagePayloadMetadata(
        source_path="/input/rgb.tif",
        source_image_names=("RGB",),
        source_channel_axis=-1,
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(2, 3), source_shape_yx=(8, 10)
        ),
    ).payload_with(pixels, mask)
    contract = _prepared_contract(func)

    projected = contract.raw_main_flow_call_argument(source)

    assert projected is source
    assert image_payload_mask(projected) is mask
    assert image_payload_metadata(projected).source_spatial_domain.origin_yx == (2, 3)
    assert image_payload_metadata(projected).source_image_paths == ("/input/rgb.tif",)
    assert contract.raw_main_flow_call_argument(pixels) is pixels


@pytest.mark.parametrize("color", (False, True))
def test_prepared_align_preserves_named_plane_axis_masks_and_source_identity(color):
    shape = (8, 9, 3) if color else (8, 9)
    image = np.random.default_rng(1).random(shape, dtype=np.float32)
    pixels = np.stack((image, image))
    masks = np.ones((2, 8, 9), dtype=bool)
    masks[:, 0] = False
    metadata = ImagePayloadMetadata(
        source_image_names=("First", "Second"),
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=("/input/first.tif", "/input/second.tif"),
            component_metadata=({"well": "A01", "channel": "1"}, {"well": "A01", "channel": "2"}),
        ),
        plane_axis=RuntimePlaneAxis.SOURCE_BINDING,
        source_channel_axis=3 if color else None,
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(2, 3), source_shape_yx=(14, 17)
        ),
    )
    source = metadata.payload_with(pixels, masks)
    contract = _prepared_contract(align)

    outputs, measurements = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        source,
        {"method": AlignModule.Method.NORMALIZED_CROSS_CORRELATION,
         "crop_mode": AlignModule.CropMode.KEEP_SIZE},
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )

    assert len(outputs.slices) == 2
    assert measurements.row_count() == 2
    for index, output in enumerate(outputs.slices):
        np.testing.assert_array_equal(image_payload_data(output), pixels[index])
        np.testing.assert_array_equal(image_payload_mask(output), masks[index])
        output_metadata = image_payload_metadata(output)
        assert output_metadata.source_image_paths == (("/input/first.tif", "/input/second.tif")[index],)
        assert output_metadata.source_spatial_domain == metadata.source_spatial_domain
        assert output_metadata.source_channel_axis == (2 if color else None)


def test_prepared_crop_preserves_rgb_spatial_mask_and_calibrated_source_domain():
    pixels = np.arange(60, dtype=np.float32).reshape(4, 5, 3)
    parent_mask = np.ones((4, 5), dtype=bool)
    parent_mask[0] = False
    domain = SourceSpatialDomain(origin_yx=(2, 3), source_shape_yx=(8, 10))
    source = ImagePayloadMetadata(
        source_channel_axis=-1,
        source_image_names=("RGB",),
        source_path="/input/rgb.tif",
        source_spatial_domain=domain,
    ).payload_with(pixels, parent_mask)
    contract = _prepared_contract(crop)

    output, cropping, measurements = CellProfilerFunctionContractExecutor().execute(
        contract,
        contract.resolve_canonical_raw_callable(),
        source,
        {"left_right_rectangle_positions": (1, 4),
         "top_bottom_rectangle_positions": (0, 3),
         "removal_method": CropModule.RemovalMethod.NO},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
    )

    expected_crop = np.zeros((4, 5), dtype=bool)
    expected_crop[:3, 1:4] = True
    expected_pixels = pixels.copy()
    expected_pixels[~expected_crop] = 0
    np.testing.assert_array_equal(cropping, expected_crop)
    np.testing.assert_array_equal(image_payload_data(output), expected_pixels)
    np.testing.assert_array_equal(image_payload_mask(output), expected_crop & parent_mask)
    output_metadata = image_payload_metadata(output)
    assert output_metadata.source_channel_axis == -1
    assert output_metadata.source_spatial_domain == domain
    assert output_metadata.source_image_paths == ("/input/rgb.tif",)
    assert measurements.row_count() == 1


def test_prepared_threshold_keeps_owned_unit_interval_proof_and_mask():
    pixels = np.arange(20, dtype=np.uint8).reshape(4, 5)
    mask = np.ones(pixels.shape, dtype=bool)
    mask[0] = False
    source = normalize_image_payload_intensity(
        ImagePayloadMetadata.for_array(pixels).payload_with(pixels, mask),
        dtype=np.float32,
    )
    contract = _prepared_contract(threshold)

    projected = contract.raw_main_flow_call_argument(source)

    assert projected is source
    assert image_payload_metadata(projected).unit_interval_intensity_scale == 255
    assert image_payload_mask(projected) is mask
    np.testing.assert_array_equal(image_payload_data(projected), pixels.astype(np.float32) / 255)
