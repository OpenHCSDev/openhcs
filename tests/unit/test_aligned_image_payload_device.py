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
    ImagePayloadMetadata, ImagePayloadMetadataCompositionMode,
    ImageUnitIntervalIntensityMetadata, image_payload_data, image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.source_spatial_domain import SourceSpatialDomain


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

    def upload(values):
        state['uploads'].append(state['device'])
        return DeviceArray(values, state['device'])

    monkeypatch.setitem(sys.modules, 'cupy', SimpleNamespace(
        cuda=SimpleNamespace(
            runtime=SimpleNamespace(getDeviceCount=lambda: 2), Device=DeviceScope,
        ),
        array=upload,
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
    output = image_payload_data(result)
    requested = 'cupy' if destination == 'implicit' else destination
    owner = MemoryType(requested)
    np.testing.assert_array_equal(owner.to_numpy(output), 0.5)
    assert owner.device_id_of(output) == (1 if requested == 'cupy' else None)
    assert image_payload_metadata(result).has_normalized_intensity
    mask = image_payload_mask(result)
    mask_owner = MemoryType(aligned_image_payload.detect_memory_type(mask))
    masks = mask_owner.to_numpy(mask)
    expected = raw.mask.values
    if composition is ImagePayloadStackContext or not declared_spatial_extent:
        expected = np.stack(tuple(value.mask.values for value in inputs))
        # Bundle's non-shared mask preserves its mask owner's device; dense stack
        # masks are returned on the declared output device through the ancestor.
        if composition is ImagePayloadStackContext:
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


def test_independent_cohort_copy_retains_nested_named_bundle_domains():
    from openhcs.core.aligned_image_payload import (
        AlignedImageSliceContext, AlignedImageStack, ImageOutputBundle,
        ImagePayloadStackComposition,
    )
    from openhcs.core.runtime_image_values import (
        ImagePayloadMetadata, image_payload_data, image_payload_mask,
    )

    pixels = np.arange(12, dtype=np.float32).reshape(3, 4)
    mask = np.ones((3, 4), dtype=bool)
    payload = ImagePayloadMetadata(source_image_names=("Canonical",)).payload_with(pixels, mask)
    context = AlignedImageSliceContext.main_flow("Canonical")
    named = ImageOutputBundle((payload,), (context,))
    nested = AlignedImageStack((named,))
    copied = ImagePayloadStackComposition.copy_whole_image(
        nested, memory_type="numpy", device_id=None,
    )
    assert type(copied) is AlignedImageStack
    assert type(copied.slices[0]) is ImageOutputBundle
    assert copied.slices[0].slice_contexts == (context,)
    member = copied.slices[0].slices[0]
    assert not np.shares_memory(image_payload_data(member), pixels)
    assert not np.shares_memory(image_payload_mask(member), mask)
    image_payload_data(member)[:] = -1
    image_payload_mask(member)[:] = False
    np.testing.assert_array_equal(pixels, np.arange(12).reshape(3, 4))
    assert mask.all()
