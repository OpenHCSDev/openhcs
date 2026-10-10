"""Gaussian consumes declared physical axes, not assembled payload rank."""

from dataclasses import replace

import numpy as np
import pytest
from skimage.filters import gaussian

from openhcs.core.aligned_image_payload import ImagePayloadExecutionMode
from openhcs.core.callable_contract import CallableContract
from openhcs.core.runtime_image_values import (
    ImagePayloadAxisFields,
    ImagePayloadMetadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.core.source_spatial_domain import SourceSpatialDomain, VolumeSourceSpatialDomain
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.gaussian_filter import gaussian_filter
from openhcs.core.payload_axes import PayloadAxes
from openhcs.core.axes import ColourAxis


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
        axes=PayloadAxes.colour_samples(channel_axis),
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
    np.testing.assert_allclose(result.data, expected)
    np.testing.assert_array_equal(result.data[1:], 0)
    assert result.metadata == source.metadata
    np.testing.assert_array_equal(result.mask, source.mask)
    np.testing.assert_array_equal(source.data, pixels)


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
    np.testing.assert_allclose(result.data, expected)
    assert result.metadata == source.metadata
    assert np.any(result.data[0, 1] if cohort else result.data[1])


@pytest.mark.parametrize("channel_axis", (0, 1, -1))
def test_declared_channel_axis_is_not_smoothed(channel_axis):
    channels = np.zeros((2, 9, 11), dtype=np.float32)
    channels[0, 4, 5] = 1
    pixels = np.moveaxis(channels, 0, channel_axis)
    result = _execute(_source(pixels, channel_axis=channel_axis))
    expected = np.moveaxis(np.stack([
        gaussian(plane, sigma=(3, 2)) for plane in channels
    ]), 0, channel_axis)
    np.testing.assert_allclose(result.data, expected)


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
    np.testing.assert_allclose(result.data, expected)
    assert result.metadata == source.metadata


def test_missing_physical_z_spacing_still_rejects():
    source = _source(np.zeros((3, 9, 11)), domain=VolumeSourceSpatialDomain(source_depth=3))
    with pytest.raises(ValueError, match="Cannot project"):
        _execute(source)


def test_invalid_channel_and_spatial_rank_still_reject():
    with pytest.raises(ValueError, match="channel axis"):
        _execute(_source(np.zeros((9, 11)), channel_axis=4))
    with pytest.raises(ValueError, match="spatial rank"):
        _execute(_source(np.zeros((9, 11)), domain=VolumeSourceSpatialDomain(source_depth=3)))


@pytest.mark.parametrize(
    "shape,channel_axis,non_channel_axes,yx",
    (
        ((7,), None, (0,), None),
        ((7, 9), 0, (1,), None),
        ((7, 9), None, (0, 1), (0, 1)),
        ((2, 7, 9, 3), -1, (0, 1, 2), (1, 2)),
    ),
)
def test_optional_yx_and_strict_intrinsic_share_non_channel_projection(
    shape, channel_axis, non_channel_axes, yx,
):
    metadata = ImagePayloadMetadata(axes=PayloadAxes.colour_samples(channel_axis))
    pixels = np.zeros(shape)
    assert metadata.non_channel_axes(pixels) == non_channel_axes
    assert metadata.spatial_axes_yx(pixels) == yx
    if yx is None:
        with pytest.raises(ValueError, match="spatial rank"):
            metadata.spatial_axes(pixels)
    else:
        assert metadata.spatial_axes(pixels) == yx


def test_yx_does_not_inherit_strict_volume_rank_requirement():
    metadata = ImagePayloadMetadata(source_spatial_domain=VolumeSourceSpatialDomain())
    pixels = np.zeros((7, 9))
    assert metadata.spatial_axes_yx(pixels) == (0, 1)
    with pytest.raises(ValueError, match="spatial rank"):
        metadata.spatial_axes(pixels)


def test_axis_capability_is_inherited_without_metadata_overrides():
    for name in (
        "non_channel_axes", "normalized_source_channel_axis", "spatial_axes_yx",
        "is_declared_source_channel_plane", "is_declared_source_channel_stack",
    ):
        assert name not in ImagePayloadMetadata.__dict__
        assert getattr(ImagePayloadMetadata, name) is getattr(ImagePayloadAxisFields, name)
    metadata = ImagePayloadMetadata()
    assert metadata.axis_position(ColourAxis) is None
    assert metadata.plane_axis is None
    assert metadata.non_channel_axes(np.zeros((3, 7, 9))) == (0, 1, 2)


@pytest.mark.parametrize("projection", ("spatial_axes_yx", "spatial_axes"))
def test_both_spatial_projections_preserve_invalid_channel_rejection(projection):
    metadata = ImagePayloadMetadata(axes=PayloadAxes.colour_samples(4))
    with pytest.raises(ValueError, match="channel axis"):
        getattr(metadata, projection)(np.zeros((7, 9)))


def test_plain_two_dimensional_pixels_preserve_unscaled_gaussian():
    pixels = np.zeros((9, 11), dtype=np.float32)
    pixels[4, 5] = 1
    np.testing.assert_allclose(_execute(pixels).data, gaussian(pixels, sigma=1.5))


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
            source_spatial_domain=VolumeSourceSpatialDomain().with_source_cohort(
                metadata.source_spatial_domain, depth=len(planes),
            )
        )
    pixels = np.stack([plane.data for plane in planes])
    result = _execute(metadata.payload_with(pixels, None))
    expected = (
        gaussian(pixels, sigma=(0.75, 3, 2)) if physical_volume
        else np.stack([gaussian(plane, sigma=(3, 2)) for plane in pixels])
    )
    np.testing.assert_allclose(result.data, expected)
    assert result.metadata == metadata
    assert result.metadata.source_provenance.source_plane_count == 3
