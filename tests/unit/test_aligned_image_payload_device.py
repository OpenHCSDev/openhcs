import numpy as np

from arraybridge import MemoryType

import openhcs.core.aligned_image_payload as aligned_image_payload
from openhcs.core.aligned_image_payload import ImagePayloadBundleContext


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
