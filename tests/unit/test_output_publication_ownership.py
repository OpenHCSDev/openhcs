"""Real output publication keeps buffer preparation and commit effects ordered."""

from dataclasses import replace
from types import SimpleNamespace

import numpy as np
import pytest
from polystore.filemanager import FileManager
from polystore.memory import MemoryStorageBackend

from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    AlignedImageStack,
    ImageOutputBundle,
    ImagePayloadStackComposition,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data
from openhcs.core.steps.function_output_manifest import step_output_manifest
from openhcs.core.steps.function_runtime import PatternGroupExecutionRequest
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser


SOURCE = "/source/A01_s001_w1_z001_t001.tif"


def _identity(image):
    return image


def _runtime(tmp_path):
    filemanager = FileManager({"memory": MemoryStorageBackend()})
    context = ProcessingContext(axis_id="A01", filemanager=filemanager)
    context.microscope_handler = SimpleNamespace(parser=SourceSchemaFilenameParser())
    plan = CompiledStepPlan(
        step_index=0,
        step_name="OutputOwnership",
        step_scope_id="output-ownership",
        axis_id="A01",
        input_memory_type="numpy",
        output_memory_type="numpy",
        output_dir=tmp_path,
        variable_components=(),
        artifact_inputs={},
        artifact_outputs={},
        execution_group_scope=ComponentGroupScope.ungrouped(),
    )
    runtime = PatternGroupExecutionRequest(context=context,
            execution_plan=plan,
            compiled_group=compile_function_pattern(_identity, {}, {}).default_group,
            component_value=None,
            pattern_group_info="A01_s001_w1_z001_t001.tif",
            component_index=0,
            component_count=1)
    payload = ImagePayloadMetadata(
        source_path=SOURCE,
        source_component_metadata={
            "well": "A01", "site": "1", "channel": "1", "z_index": "1", "timepoint": "1",
        },
    ).payload_with(np.ones((4, 5), dtype=np.float32))
    return runtime, payload


def test_buffer_preparation_failure_precedes_any_vfs_publication(tmp_path, monkeypatch):
    runtime, payload = _runtime(tmp_path)
    files = runtime.context.filemanager
    events = []

    def fail_copy(*args, **kwargs):
        events.append("copy")
        raise ValueError("buffer allocation failed")

    def unexpected_exists(*args, **kwargs):
        pytest.fail("output path access must follow independent buffer preparation")

    monkeypatch.setattr(ImagePayloadStackComposition, "copy_whole_image", staticmethod(fail_copy))
    monkeypatch.setattr(files, "exists", unexpected_exists)
    with pytest.raises(ValueError, match="buffer allocation failed"):
        runtime._save_outputs(payload, [SOURCE])
    assert events == ["copy"]
    assert runtime.context.runtime_image_stack_cache.stacks == {}


def test_saved_metadata_failure_keeps_actual_commit_but_no_cache_or_manifest(tmp_path, monkeypatch):
    runtime, payload = _runtime(tmp_path)
    files = runtime.context.filemanager
    path = str(tmp_path / "A01_s001_w1_z001_t001.tif")

    def fail_attachment(*args, **kwargs):
        assert files.load(path, "memory") is args[1][0]
        assert np.shares_memory(image_payload_data(args[1][0]), payload.data)
        raise ValueError("saved context failed")

    monkeypatch.setattr(ImagePayloadStackComposition, "with_saved_output_context", staticmethod(fail_attachment))
    with pytest.raises(ValueError, match="saved context failed"):
        runtime._save_outputs(payload, [SOURCE])
    assert np.shares_memory(image_payload_data(files.load(path, "memory")), payload.data)
    assert runtime.context.runtime_image_stack_cache.stacks == {}
    assert step_output_manifest(runtime.context).produced_records_for(runtime.execution_plan) == ()


def test_duplicate_output_paths_leave_existing_memory_value_and_cache_intact(tmp_path):
    runtime, payload = _runtime(tmp_path)
    context = runtime.context
    path = str(tmp_path / "A01_s001_w1_z001_t001.tif")
    previous = np.full((4, 5), 9, dtype=np.float32)
    context.filemanager.ensure_directory(str(tmp_path), "memory")
    context.filemanager.save(previous, path, "memory")
    context.runtime_image_stack_cache.store((path,), memory_type="numpy", stack=previous)
    output = AlignedImageStack((payload, replace(payload)))
    with pytest.raises(ValueError, match="duplicate output path"):
        runtime._save_outputs(output, [SOURCE, SOURCE])
    assert context.filemanager.load(path, "memory") is previous
    assert context.runtime_image_stack_cache.get((path,), memory_type="numpy") is previous


def test_original_named_owner_is_consulted_at_saved_metadata_epoch(tmp_path):
    runtime, payload = _runtime(tmp_path)
    files = runtime.context.filemanager
    path = str(tmp_path / "A01_s001_w1_z001_t001_Named.tif")
    calls = []

    class EpochSensitiveBundle(ImageOutputBundle):
        def plane_axis_for_output_context(self, context):
            calls.append(files.exists(path, "memory"))
            if calls[-1]:
                raise ValueError("post-save domain rejected")
            return super().plane_axis_for_output_context(context)

    output = EpochSensitiveBundle((payload,), (AlignedImageSliceContext.main_flow("Named"),))
    with pytest.raises(ValueError, match="post-save domain rejected"):
        runtime._save_outputs(output, [SOURCE])
    assert calls == [False, True]
    np.testing.assert_array_equal(image_payload_data(files.load(path, "memory")), payload.data)
    assert runtime.context.runtime_image_stack_cache.stacks == {}


def test_anonymous_context_is_shared_by_record_and_post_save_axis_hooks(tmp_path):
    runtime, payload = _runtime(tmp_path)
    calls = []

    class AnonymousStack(AlignedImageStack):
        def plane_axis_for_output_context(self, context):
            calls.append(context)
            return super().plane_axis_for_output_context(context)

    output = AnonymousStack((payload,))
    (record,) = runtime._save_outputs(output, [SOURCE])
    assert calls[0] is None
    assert len(calls) == 3
    assert calls[1].is_anonymous_main_flow
    assert calls[2] is calls[1]
    assert record.output_context == calls[1]
