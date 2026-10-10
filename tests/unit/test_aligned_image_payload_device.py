import numpy as np
import pytest
import sys
from types import SimpleNamespace

from arraybridge import MemoryType

import openhcs.core.aligned_image_payload as aligned_image_payload
from openhcs.core.aligned_image_payload import (
    ImagePayloadBundleContext, ImagePayloadStackContext,
)
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    ImagePayloadMetadataCompositionMode,
    ImageUnitIntervalIntensityMetadata,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.payload_axes import PayloadAxes


@pytest.fixture
def declared_cupy_leaf(monkeypatch):
    """CPU-controlled external leaf; real MemoryType/converters run unchanged."""
    state = {'device': 0, 'downloads': [], 'uploads': []}

    class DeviceScope:
        def __init__(self, device_id):
            self.device_id = device_id

        def __enter__(self):
            self.previous = state['device']
            state['device'] = self.device_id

        def __exit__(self, *exc):
            state['device'] = self.previous

    class DeviceArray:
        __module__ = 'cupy'

        def __init__(self, values, device_id=1):
            self.values = np.asarray(values)
            self.device = SimpleNamespace(id=device_id)

        @property
        def shape(self):
            return self.values.shape

        @property
        def dtype(self):
            return self.values.dtype

        @property
        def ndim(self):
            return self.values.ndim

        def __array__(self, dtype=None, copy=None):
            raise TypeError('Implicit device-to-host conversion is forbidden')

        def get(self):
            state['downloads'].append(self.device.id)
            return self.values

        def __getitem__(self, key):
            return type(self)(self.values[key], self.device.id)

        def astype(self, dtype, copy=False):
            return type(self)(self.values.astype(dtype, copy=copy), self.device.id)

        def __truediv__(self, scalar):
            return type(self)(self.values / scalar, self.device.id)

        def reshape(self, shape):
            return type(self)(self.values.reshape(shape), self.device.id)

    def upload(values):
        state['uploads'].append(state['device'])
        return DeviceArray(values, state['device'])

    monkeypatch.setitem(sys.modules, 'cupy', SimpleNamespace(
        cuda=SimpleNamespace(
            runtime=SimpleNamespace(getDeviceCount=lambda: 2), Device=DeviceScope,
        ),
        array=upload,
        broadcast_to=lambda value, shape: DeviceArray(
            np.broadcast_to(value.values, shape), value.device.id,
        ),
        ones=lambda shape, dtype=bool: DeviceArray(
            np.ones(shape, dtype=dtype), state['device'],
        ),
        stack=lambda values, axis=0: DeviceArray(
            np.stack([value.values for value in values], axis=axis), state['device'],
        ),
        logical_and=lambda left, right: DeviceArray(
            np.logical_and(left.values, right.values), state['device'],
        ),
    ))
    return DeviceArray, state


@pytest.mark.parametrize('composition,mode', (
    (ImagePayloadStackContext, ImagePayloadMetadataCompositionMode.STACK),
    (ImagePayloadBundleContext, ImagePayloadMetadataCompositionMode.BUNDLE),
))
@pytest.mark.parametrize('raw_first', (False, True))
@pytest.mark.parametrize('destination', ('implicit', 'numpy', 'cupy'))
@pytest.mark.parametrize('declared_spatial_extent', (False, True))
def test_mixed_intensity_composition_uses_declared_memory_conversion(
    declared_cupy_leaf, composition, mode, raw_first, destination, declared_spatial_extent,
):
    DeviceArray, state = declared_cupy_leaf
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
    kwargs = {} if destination == 'implicit' else {
        'memory_type': destination, 'device_id': 1 if destination == 'cupy' else None,
    }
    result = context.compose(**kwargs)
    assert bool(state['downloads']) == (destination == 'numpy')
    output = result.data
    requested = 'cupy' if destination == 'implicit' else destination
    owner = MemoryType(requested)
    np.testing.assert_array_equal(owner.to_numpy(output), 0.5)
    assert owner.device_id_of(output) == (1 if requested == 'cupy' else None)
    assert result.metadata.has_normalized_intensity
    mask = result.mask
    mask_owner = MemoryType(aligned_image_payload.detect_memory_type(mask))
    masks = mask_owner.to_numpy(mask)
    expected = raw.mask.values
    if composition is ImagePayloadStackContext or not declared_spatial_extent:
        expected = np.stack(tuple(value.mask.values for value in inputs))
    assert mask_owner.device_id_of(mask) == owner.device_id_of(output)
    np.testing.assert_array_equal(masks, expected)
    assert state['downloads']
    assert all(device == 1 for device in state['downloads'])
    assert all(device == 1 for device in state['uploads'])
    assert state['device'] == 0
    np.testing.assert_array_equal(raw.data.values, 32)


def test_image_bundle_stacks_on_the_payload_framework_device(monkeypatch) -> None:
    payloads = (
        np.zeros((3, 4), dtype=np.float32),
        np.ones((3, 4), dtype=np.float32),
    )
    observed = []
    monkeypatch.setattr(
        aligned_image_payload,
        "detect_memory_type",
        lambda _payload: MemoryType.CUPY.value,
    )
    monkeypatch.setattr(
        MemoryType,
        "device_id_of",
        lambda memory_type, _payload, _module=None: (
            7 if memory_type is MemoryType.CUPY else None
        ),
    )
    monkeypatch.setattr(
        aligned_image_payload,
        "stack_runtime_slices",
        lambda values, memory_type, device_id: observed.append(
            (tuple(values), memory_type, device_id)
        )
        or "stacked",
    )

    context = ImagePayloadBundleContext(payloads)

    assert context.compose_unmasked(payloads) == "stacked"
    assert observed == [(payloads, MemoryType.CUPY.value, 7)]


@pytest.mark.parametrize('mask_kind', ('full', 'channel-free', 'absent'))
@pytest.mark.parametrize('destination', ('numpy', 'cupy'))
def test_mixed_channel_bundle_promotes_masks_in_the_output_domain(
    declared_cupy_leaf, mask_kind, destination,
):
    DeviceArray, state = declared_cupy_leaf
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
    result = ImagePayloadBundleContext.from_payloads(inputs).compose(
        memory_type=destination, device_id=1 if destination == 'cupy' else None,
    )
    if destination == 'cupy':
        assert not state['downloads']
    owner = MemoryType(destination)
    data, mask = result.data, result.mask
    assert owner.device_id_of(mask) == owner.device_id_of(data)
    np.testing.assert_array_equal(owner.to_numpy(data), np.stack((color, color)))
    expected = np.stack((np.ones_like(spatial) if mask_kind == 'absent' else spatial, spatial))
    if mask_kind == 'full':
        expected = np.repeat(expected[..., None], 3, axis=3)
    np.testing.assert_array_equal(owner.to_numpy(mask), expected)


def test_independent_cohort_copy_retains_nested_named_bundle_domains():
    from openhcs.core.aligned_image_payload import (
        AlignedImageSliceContext, AlignedImageStack, ImageOutputBundle,
        ImagePayloadStackComposition,
    )
    from openhcs.core.runtime_image_values import ImagePayloadMetadata

    pixels = np.arange(12, dtype=np.float32).reshape(3, 4)
    mask = np.ones((3, 4), dtype=bool)
    payload = ImagePayloadMetadata(source_image_names=("Canonical",)).payload_with(pixels, mask)
    context = AlignedImageSliceContext.main_flow("Canonical")
    named = ImageOutputBundle((payload,), (context,))
    nested = AlignedImageStack((named,))
    copied = (nested).copied(memory_type="numpy", device_id=None,)
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
