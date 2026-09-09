"""Execution-boundary release of image reuse storage."""

import gc
import weakref

import numpy as np
import pytest

from openhcs.core.artifacts import ArtifactOutputPlan, ImageArtifactType
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_stack_cache import RuntimeImageStackCache


@pytest.mark.parametrize("context_owned", [False, True])
def test_release_drops_all_cached_views_and_allows_reuse(context_owned: bool) -> None:
    context = ProcessingContext(axis_id="A01")
    cache = (
        context.runtime_image_stack_cache if context_owned else RuntimeImageStackCache()
    )
    release = context.release_execution_image_cache if context_owned else cache.clear
    allocation = np.ones((3, 8, 8), dtype=np.uint16)
    allocation_ref = weakref.ref(allocation)
    paths = (("/memory/first.tif",), ("/memory/second.tif",))
    for index, entry in enumerate(paths):
        cache.store(entry, memory_type="numpy", stack=allocation[index : index + 1])
    del allocation
    gc.collect()
    assert allocation_ref() is not None

    release()
    release()
    gc.collect()

    assert allocation_ref() is None
    assert all(cache.get(entry, memory_type="numpy") is None for entry in paths)
    replacement = np.zeros((1, 8, 8), dtype=np.uint16)
    cache.store(paths[0], memory_type="numpy", stack=replacement)
    assert cache.get(paths[0], memory_type="numpy").stack is replacement


def test_context_image_cache_release_preserves_runtime_artifacts_and_observations() -> None:
    context = ProcessingContext(axis_id="A01")
    output_plan = ArtifactOutputPlan(
        name="retained_image",
        path="/memory/retained.pkl",
        artifact_type=ImageArtifactType,
    )
    retained_array = np.ones((1, 2, 2), dtype=np.uint16)
    retained_payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    ).payload_with(retained_array, None)
    value = RuntimeValue.normalize(output_plan, retained_payload, axis_id="A01")
    store = context.runtime_value_store
    cursor = store.observation_cursor()
    record = store.record(value, path=output_plan.path, backend="memory")
    revision = store.revision
    cached_array = np.ones((1, 8, 8), dtype=np.uint16)
    cached_ref = weakref.ref(cached_array)
    context.runtime_image_stack_cache.store(
        ("/memory/temporary.tif",), memory_type="numpy", stack=cached_array
    )
    del cached_array

    context.release_execution_image_cache()
    gc.collect()

    assert cached_ref() is None
    assert context.runtime_value_store is store
    assert store.revision == revision
    assert store.values() == (record,)
    assert store.observed_values_after(cursor) == (record,)
