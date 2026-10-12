"""Composed image payloads land at the placement that was asked for.

One family of cases: every way of composing image payloads (a plane stack, a
source-binding bundle, a mixed-channel bundle, a copy) is run for each
destination placement, and data and mask must both be there.
"""

import numpy as np
import pytest
from arraybridge import MemoryType
from arraybridge.devices import HOST, AcceleratorDevice
from arraybridge.libraries import ArrayLibrary

from openhcs.core.aligned_image_payload import (
    ImagePayloadBundleContext,
    ImagePayloadStackContext,
)
from openhcs.core.payload_axes import PayloadAxes
from openhcs.core.runtime_array_values import ArrayPlacement
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImageUnitIntervalIntensityMetadata,
)
from openhcs.core.runtime_plane_projection import RuntimeSlicePlaneAxis, SourceBindingPlaneAxis
from openhcs.core.source_spatial_domain import SourceSpatialDomain

ON_HOST = ArrayPlacement(MemoryType.NUMPY.library, HOST)
ON_ACCELERATOR = ArrayPlacement(MemoryType.CUPY.library, AcceleratorDevice(1))


def _assert_placed(value, placement: ArrayPlacement) -> np.ndarray:
    """``value`` lives at ``placement``; returns its host copy."""
    assert ArrayPlacement.of(value) == placement
    return placement.library.to_numpy(value)


@pytest.mark.parametrize('composition,mode', (
    (ImagePayloadStackContext, RuntimeSlicePlaneAxis),
    (ImagePayloadBundleContext, SourceBindingPlaneAxis),
))
@pytest.mark.parametrize('raw_first', (False, True))
@pytest.mark.parametrize('destination', (None, ON_HOST, ON_ACCELERATOR))
@pytest.mark.parametrize('declared_spatial_extent', (False, True))
def test_mixed_intensity_composition_lands_at_the_requested_placement(
    cupy_arrays_that_record_their_device, composition, mode, raw_first, destination, declared_spatial_extent,
):
    DeviceArray, state = cupy_arrays_that_record_their_device
    spatial_domain = SourceSpatialDomain(
        source_shape_yx=(2, 3) if declared_spatial_extent else None,
    )
    raw = ImagePayloadMetadata(
        intensity_scale=64, source_dtype='uint8', source_spatial_domain=spatial_domain,
    ).payload_with(
        DeviceArray(np.full((2, 3), 32, dtype=np.uint8)),
        DeviceArray(np.array([[True, False, True], [False, True, True]])),
    )
    normalized = ImagePayloadMetadata(
        intensity_scale=64, source_dtype='uint8',
        unit_interval_intensity=ImageUnitIntervalIntensityMetadata(scale=64),
        source_spatial_domain=spatial_domain,
    ).payload_with(DeviceArray(np.full((2, 3), 0.5, dtype=np.float32)),
                   DeviceArray(np.ones((2, 3), dtype=bool)))
    inputs = (raw, normalized) if raw_first else (normalized, raw)
    context = composition(inputs, metadata_mode=mode)
    result = context.compose(destination)
    assert bool(state['downloads']) == (destination == ON_HOST)
    placement = ON_ACCELERATOR if destination is None else destination
    np.testing.assert_array_equal(_assert_placed(result.data, placement), 0.5)
    assert result.metadata.has_normalized_intensity
    mask = result.mask
    expected = raw.mask.values
    if composition is ImagePayloadStackContext or not declared_spatial_extent:
        expected = np.stack(tuple(value.mask.values for value in inputs))
    mask_library = ArrayLibrary.of(mask)
    assert mask_library.device_of(mask) == placement.device
    np.testing.assert_array_equal(mask_library.to_numpy(mask), expected)
    assert state['downloads']
    assert all(device == 1 for device in state['downloads'])
    assert all(device == 1 for device in state['uploads'])
    assert state['device'] == 0
    np.testing.assert_array_equal(raw.data.values, 32)


@pytest.mark.parametrize('mask_kind', ('full', 'channel-free', 'absent'))
@pytest.mark.parametrize('destination', (ON_HOST, ON_ACCELERATOR))
def test_mixed_channel_bundle_promotes_masks_in_the_output_domain(
    cupy_arrays_that_record_their_device, mask_kind, destination,
):
    DeviceArray, state = cupy_arrays_that_record_their_device
    gray = np.arange(6, dtype=np.uint8).reshape(2, 3)
    color = np.repeat(gray[..., None], 3, axis=2)
    spatial = gray % 2 == 0
    color_mask = (
        None if mask_kind == 'absent' else DeviceArray(
            np.repeat(spatial[..., None], 3, axis=2)
            if mask_kind == 'full' else spatial,
        )
    )
    inputs = (
        ImagePayloadMetadata(axes=PayloadAxes.colour_samples(2)).payload_with(
            DeviceArray(color), color_mask,
        ),
        ImagePayloadMetadata().payload_with(DeviceArray(gray), DeviceArray(spatial)),
    )
    result = ImagePayloadBundleContext.from_payloads(inputs).compose(destination)
    if destination == ON_ACCELERATOR:
        assert not state['downloads']
    np.testing.assert_array_equal(
        _assert_placed(result.data, destination), np.stack((color, color))
    )
    expected = np.stack((np.ones_like(spatial) if mask_kind == 'absent' else spatial, spatial))
    if mask_kind == 'full':
        expected = np.repeat(expected[..., None], 3, axis=3)
    np.testing.assert_array_equal(_assert_placed(result.mask, destination), expected)


def test_independent_cohort_copy_retains_nested_named_bundle_domains():
    from openhcs.core.aligned_image_payload import (
        AlignedImageSliceContext, AlignedImageStack, ImageOutputBundle,
    )

    pixels = np.arange(12, dtype=np.float32).reshape(3, 4)
    mask = np.ones((3, 4), dtype=bool)
    payload = ImagePayloadMetadata(source_image_names=("Canonical",)).payload_with(pixels, mask)
    context = AlignedImageSliceContext.main_flow("Canonical")
    named = ImageOutputBundle((payload,), (context,))
    nested = AlignedImageStack((named,))
    copied = nested.copied(ON_HOST)
    assert type(copied) is AlignedImageStack
    assert type(copied.slices[0]) is ImageOutputBundle
    assert copied.slices[0].slice_contexts == (context,)
    member = copied.slices[0].slices[0]
    assert not np.shares_memory(member.data, pixels)
    assert not np.shares_memory(member.mask, mask)
    member.data[:] = -1
    member.mask[:] = False
    np.testing.assert_array_equal(pixels, np.arange(12).reshape(3, 4))
    assert mask.all()
