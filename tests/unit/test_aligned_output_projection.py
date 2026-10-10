from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.core import aligned_image_payload
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    AlignedImageStack,
    ImageOutputBundle,
)
from openhcs.core.memory import MemoryType
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest


def test_runtime_projects_mixed_output_planes_once_with_their_contexts(monkeypatch):
    first = np.arange(12, dtype=np.float32).reshape(3, 2, 2)
    second = np.arange(8, dtype=np.float32).reshape(2, 2, 2)
    mask = first > 3
    payloads = (
        ImagePayloadMetadata(
            source_path="first.tif", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
        ).payload_with(first, mask),
        ImagePayloadMetadata(
            source_path="second.tif", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
        ).payload_with(second, None),
    )
    contexts = tuple(AlignedImageSliceContext.main_flow(name) for name in ("A", "B"))
    bundle = ImageOutputBundle(payloads, contexts)
    calls = []
    original = aligned_image_payload.payload_slices_for_alignment

    def counted(payload):
        calls.append(payload)
        return original(payload)

    monkeypatch.setattr(aligned_image_payload, "payload_slices_for_alignment", counted)
    runtime = PatternGroupExecutionRequest(pattern_group_info="generic-output-projection",
            execution_plan=CompiledStepPlan(
                step_index=0, step_name="output-projection",
                axis_id="A01", output_memory_type=MemoryType.NUMPY,
            ),
            context=ProcessingContext(axis_id="A01"),
            compiled_group=compile_function_pattern(lambda image: image, {}, {}).default_group,
            component_index=0,
            component_count=1)
    result = runtime._project_output_slices(bundle, [])

    assert len(calls) == 2
    assert calls[0] is payloads[0] and calls[1] is payloads[1]
    assert tuple(context for _payload, context in result) == (contexts[0],) * 3 + (contexts[1],) * 2
    assert len(result) == 5
    for index, payload in enumerate(payload for payload, _context in result):
        source = first if index < 3 else second
        plane = index if index < 3 else index - 3
        np.testing.assert_array_equal(image_payload_data(payload), source[plane])
        assert np.shares_memory(image_payload_data(payload), source)
        if index < 3:
            np.testing.assert_array_equal(image_payload_mask(payload), mask[plane])
        else:
            assert image_payload_mask(payload) is None
        assert image_payload_metadata(payload).plane_axis is None


def test_shared_projection_retains_nesting_and_fresh_metadata_snapshots():
    array = np.ones((2, 2, 2), dtype=np.float32)
    metadata = ImagePayloadMetadata(
        source_path="first.tif", plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    )
    payload = metadata.payload_with(array, None)
    stack = AlignedImageStack((payload,))
    before = tuple(stack.projected_output_slices())
    metadata.source_path = "updated.tif"
    after = tuple(stack.projected_output_slices())

    assert all(context is None for _payload, context in before)
    assert all(
        image_payload_metadata(item).source_path == "first.tif" for item, _ in before
    )
    assert all(
        image_payload_metadata(item).source_path == "updated.tif" for item, _ in after
    )
    nested = AlignedImageStack((stack,))
    assert tuple(nested.projected_output_slices()) == ((payload, None),)


def test_aligned_projection_preserves_strict_context_cardinality():
    context = AlignedImageSliceContext.main_flow("A")
    value = ImageOutputBundle((np.ones((2, 2)),), (context,))
    value.slice_contexts = (context, context)

    with pytest.raises(ValueError, match="zip"):
        tuple(value.projected_output_slices())

    assert (
        ImageOutputBundle.projected_output_slices
        is AlignedImageStack.projected_output_slices
    )
