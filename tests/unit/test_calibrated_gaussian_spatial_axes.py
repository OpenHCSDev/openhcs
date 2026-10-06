"""Gaussian consumes declared physical axes, not assembled payload rank."""

from dataclasses import replace

import numpy as np
import pytest
from skimage.filters import gaussian

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain, VolumeSourceSpatialDomain
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.gaussian_filter import gaussian_filter


def _execute(source):
    contract = CallableContract.from_callable(gaussian_filter).with_prepared_signature()
    contract = replace(contract, metadata=replace(
        contract.metadata, runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
    ))
    return CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), source, {"sigma": 1.5},
        execution_mode=ImagePayloadExecutionMode.FULL_STACK,
    )


def _source(pixels, *, domain=None, spacing=(0.5, 0.75), channel_axis=None, cohort=False):
    metadata = ImagePayloadMetadata(
        source_path="/synthetic/original.tif",
        source_image_names=("Original",),
        source_component_metadata={"well": "A01", "site": 1, "channel": 1},
        source_voxel_spacing=SourceVoxelSpacing(values_zyx=spacing),
        source_spatial_domain=SourceSpatialDomain() if domain is None else domain,
        source_channel_axis=channel_axis,
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE if cohort else None,
    )
    return metadata.payload_with(pixels, np.ones(pixels.shape, dtype=bool))


@pytest.mark.parametrize("count", (1, 3))
def test_calibrated_sites_filter_independently_and_preserve_source(count):
    pixels = np.zeros((count, 9, 11), dtype=np.float32)
    pixels[0, 4, 5] = 1
    source = _source(pixels, cohort=True)
    result = _execute(source)
    expected = np.stack([gaussian(plane, sigma=(3, 2)) for plane in pixels])
    np.testing.assert_allclose(image_payload_data(result), expected)
    np.testing.assert_array_equal(image_payload_data(result)[1:], 0)
    assert image_payload_metadata(result) == image_payload_metadata(source)
    np.testing.assert_array_equal(image_payload_mask(result), image_payload_mask(source))
    np.testing.assert_array_equal(image_payload_data(source), pixels)


@pytest.mark.parametrize("cohort", (False, True))
def test_anisotropic_physical_z_matches_library_without_site_blur(cohort):
    volume = np.zeros((5, 9, 11), dtype=np.float32)
    volume[2, 4, 5] = 1
    pixels = np.stack((volume, np.zeros_like(volume))) if cohort else volume
    source = _source(
        pixels, domain=VolumeSourceSpatialDomain(source_depth=5),
        spacing=(2, 0.5, 0.75), cohort=cohort,
    )
    result = _execute(source)
    expected_volume = gaussian(volume, sigma=(0.75, 3, 2))
    expected = np.stack((expected_volume, np.zeros_like(volume))) if cohort else expected_volume
    np.testing.assert_allclose(image_payload_data(result), expected)
    assert image_payload_metadata(result) == image_payload_metadata(source)
    assert np.any(image_payload_data(result)[0, 1] if cohort else image_payload_data(result)[1])


@pytest.mark.parametrize("channel_axis", (0, 1, -1))
def test_declared_channel_axis_is_not_smoothed(channel_axis):
    channels = np.zeros((2, 9, 11), dtype=np.float32)
    channels[0, 4, 5] = 1
    pixels = np.moveaxis(channels, 0, channel_axis)
    result = _execute(_source(pixels, channel_axis=channel_axis))
    expected = np.moveaxis(np.stack([
        gaussian(plane, sigma=(3, 2)) for plane in channels
    ]), 0, channel_axis)
    np.testing.assert_allclose(image_payload_data(result), expected)


def test_physical_volume_with_channels_and_independent_sites():
    pixels = np.zeros((2, 5, 9, 11, 2), dtype=np.float32)
    pixels[0, 2, 4, 5, 0] = 1
    source = _source(
        pixels, domain=VolumeSourceSpatialDomain(source_depth=5),
        spacing=(2, 0.5, 0.75), channel_axis=-1, cohort=True,
    )
    result = _execute(source)
    expected = np.zeros_like(pixels)
    expected[0, ..., 0] = gaussian(pixels[0, ..., 0], sigma=(0.75, 3, 2))
    np.testing.assert_allclose(image_payload_data(result), expected)
    assert image_payload_metadata(result) == image_payload_metadata(source)


def test_missing_physical_z_spacing_still_rejects():
    source = _source(np.zeros((3, 9, 11)), domain=VolumeSourceSpatialDomain(source_depth=3))
    with pytest.raises(ValueError, match="Cannot project"):
        _execute(source)


def test_invalid_channel_and_spatial_rank_still_reject():
    with pytest.raises(ValueError, match="channel axis"):
        _execute(_source(np.zeros((9, 11)), channel_axis=4))
    with pytest.raises(ValueError, match="spatial rank"):
        _execute(_source(np.zeros((9, 11)), domain=VolumeSourceSpatialDomain(source_depth=3)))


def test_plain_two_dimensional_pixels_preserve_unscaled_gaussian():
    pixels = np.zeros((9, 11), dtype=np.float32)
    pixels[4, 5] = 1
    np.testing.assert_allclose(image_payload_data(_execute(pixels)), gaussian(pixels, sigma=1.5))


@pytest.mark.parametrize("physical_volume", (False, True))
def test_original_cohort_composition_keeps_every_source_plane(physical_volume):
    planes = tuple(
        ImagePayloadMetadata(
            source_path=f"/synthetic/plane{index}.tif",
            source_image_names=("Original",),
            source_component_metadata={
                "well": "A01", "site": 1 if physical_volume else index + 1,
                "z_index": index if physical_volume else 0,
            },
            source_voxel_spacing=SourceVoxelSpacing(
                values_zyx=(2, 0.5, 0.75) if physical_volume else (0.5, 0.75)
            ),
        ).payload_with(np.eye(9, 11, dtype=np.float32) * (index + 1), None)
        for index in range(3)
    )
    metadata = ImagePayloadMetadata.compose(planes).replace_fields(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    )
    if physical_volume:
        metadata = metadata.replace_fields(
            source_spatial_domain=VolumeSourceSpatialDomain().admit_source_cohort(
                metadata.source_spatial_domain, depth=len(planes),
            )
        )
    pixels = np.stack([image_payload_data(plane) for plane in planes])
    result = _execute(metadata.payload_with(pixels, None))
    expected = (
        gaussian(pixels, sigma=(0.75, 3, 2)) if physical_volume
        else np.stack([gaussian(plane, sigma=(3, 2)) for plane in pixels])
    )
    np.testing.assert_allclose(image_payload_data(result), expected)
    assert image_payload_metadata(result) == metadata
    assert image_payload_metadata(result).source_provenance.source_plane_count == 3
