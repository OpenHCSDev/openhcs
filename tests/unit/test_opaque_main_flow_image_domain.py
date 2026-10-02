"""Whole image domains survive the producer/cache/next-load handoff."""

from dataclasses import replace
from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.constants.constants import MEMORY_TYPE_NUMPY
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_image_values import (
    ImagePayloadMetadata,
    image_payload_data,
    image_payload_mask,
    image_payload_metadata,
)
from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
from openhcs.core.runtime_slice_projection import RuntimeSliceProjection
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.function_runtime import PatternGroupData, PatternGroupRuntime
from openhcs.core.aligned_image_payload import AlignedImageStack, ImageOutputBundle, AlignedImageSliceContext
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.steps.function_output_manifest import step_output_manifest, StepOutputManifestStore
from openhcs.core.source_bindings import CompiledSourceBindingPlan, SourceBindingRuntimeContext
from openhcs.core.steps.function_runtime import SourceBindingRuntimeContextRequest
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.microscopes.source_schema import SourceSchemaFilenameParser
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes


def _identity(image):
    return image


def _runtime():
    pattern = compile_function_pattern(_identity, {}, {})
    runtime = object.__new__(PatternGroupRuntime)
    runtime.request = SimpleNamespace(
        compiled_group=pattern.default_group,
        execution_plan=CompiledStepPlan(
            step_index=0,
            step_name="WholeImage",
            step_type="FunctionStep",
            axis_id="A01",
            output_memory_type=MEMORY_TYPE_NUMPY,
            input_memory_type=MEMORY_TYPE_NUMPY,
            variable_components=(),
            artifact_inputs={},
            artifact_outputs={},
            execution_group_scope=ComponentGroupScope.ungrouped(),
        ),
        component_key=None,
    )
    return runtime


@pytest.mark.parametrize(
    ("shape", "channel_axis"),
    [((4, 5), None), ((4, 5, 3), -1), ((3, 4, 5), None), ((1, 4, 5), None)],
    ids=("plane", "rgb", "volume", "one-z-volume"),
)
def test_opaque_whole_image_is_copied_without_a_new_execution_axis(shape, channel_axis):
    pixels = np.arange(np.prod(shape), dtype=np.float32).reshape(shape)
    mask_shape = shape[:2] if channel_axis is not None else shape
    mask = np.ones(mask_shape, dtype=bool)
    metadata = ImagePayloadMetadata(
        source_path="/input/A01_s001_w1_z001_t001.tif",
        source_component_metadata={"well": "A01", "site": "1", "channel": "1"},
        source_image_names=("WholeImage",),
        source_channel_axis=channel_axis,
        source_spatial_domain=SourceSpatialDomain(
            origin_yx=(2, 3), source_shape_yx=(12, 13),
        ),
    )
    payload = metadata.payload_with(pixels, mask)
    output = _runtime()._validate_and_unstack(
        payload,
        PatternGroupData(
            matching_files=["/input/A01_s001_w1_z001_t001.tif", "/input/A01_s001_w1_z002_t001.tif"],
            main_data_stack=np.zeros((2, 4, 5), dtype=np.float32),
        ),
    )
    assert len(output.slices) == 1
    assert output.slices[0] is payload
    cached = output.stack_payload
    assert image_payload_data(cached).shape == shape
    assert image_payload_metadata(cached) == metadata
    np.testing.assert_array_equal(image_payload_data(cached), pixels)
    np.testing.assert_array_equal(image_payload_mask(cached), mask)
    assert not np.shares_memory(image_payload_data(cached), pixels)
    assert not np.shares_memory(image_payload_mask(cached), mask)
    assert image_payload_metadata(cached) is not metadata
    assert RuntimeSliceProjection.full_stack_value(cached) is cached
    image_payload_data(cached).flat[0] = -100
    image_payload_mask(cached).flat[0] = False
    assert pixels.flat[0] == 0
    assert mask.flat[0]
    image_payload_metadata(cached).source_channel_axis = 0
    assert metadata.source_channel_axis == channel_axis


@pytest.mark.parametrize("count", [1, 3])
def test_declared_runtime_axis_retains_its_exact_count(count):
    pixels = np.arange(count * 4 * 5, dtype=np.float32).reshape(count, 4, 5)
    payload = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(pixels)
    output = _runtime()._validate_and_unstack(
        payload,
        PatternGroupData(matching_files=["source-1.tif", "source-2.tif"], main_data_stack=pixels),
    )
    assert len(output.slices) == count
    assert output.stack_payload is payload
    assert image_payload_data(output.stack_payload).shape == (count, 4, 5)
    assert image_payload_metadata(output.stack_payload).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE


@pytest.mark.parametrize("named", [False, True])
@pytest.mark.parametrize("axis", [None, RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING])
def test_nominal_alignment_owner_preserves_single_output_topology(named, axis):
    shape = (3, 4, 5) if axis is None else (1, 4, 5)
    payload = ImagePayloadMetadata(plane_axis=axis).payload_with(np.ones(shape, dtype=np.float32))
    context = AlignedImageSliceContext.main_flow("Image")
    value = (ImageOutputBundle if named else AlignedImageStack)((payload,), (context,))
    output = _runtime()._validate_and_unstack(
        value, PatternGroupData(matching_files=["source.tif"], main_data_stack=payload),
    )
    if named and axis is not RuntimePlaneAxis.RUNTIME_SLICE:
        expected_shape, expected_axis = shape, axis
    else:
        expected_shape = (1, 4, 5) if axis is RuntimePlaneAxis.RUNTIME_SLICE else (1, *shape)
        expected_axis = RuntimePlaneAxis.RUNTIME_SLICE
    assert image_payload_data(output.stack_payload).shape == expected_shape
    assert image_payload_metadata(output.stack_payload).plane_axis is expected_axis


@pytest.mark.parametrize("count", [1, 3])
def test_raw_array_fallback_keeps_explicit_runtime_unstack_contract(count):
    runtime = _runtime()
    runtime.request.context = ProcessingContext(axis_id="A01")
    runtime.request.context.microscope_handler = SimpleNamespace(parser=SourceSchemaFilenameParser())
    pixels = np.arange(count * 4 * 5, dtype=np.float32).reshape(count, 4, 5)
    output = runtime._validate_and_unstack(
        pixels, PatternGroupData(matching_files=[f"source-{i}.tif" for i in range(count)], main_data_stack=pixels),
    )
    cached = output.cache_payload_for_outputs(output.slices, [image_payload_metadata(p) for p in output.slices])
    assert image_payload_data(cached).shape == (count, 4, 5)
    assert image_payload_metadata(cached).plane_axis is RuntimePlaneAxis.RUNTIME_SLICE


class _MemoryFiles:
    def __init__(self):
        self.values = {}

    def exists(self, path, backend):
        return path in self.values or any(value_path.startswith(path.rstrip("/") + "/") for value_path in self.values)

    def ensure_directory(self, path, backend):
        pass

    def save_batch(self, payloads, paths, backend):
        self.values.update(zip(paths, payloads, strict=True))

    def load_batch(self, paths, backend):
        return [self.values[path] for path in paths]

    def delete(self, path, backend):
        del self.values[path]


@pytest.mark.parametrize("cache_hit", [False, True])
@pytest.mark.parametrize("axis", [None, RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING])
@pytest.mark.parametrize("shape", [(4, 5), (4, 5, 3), (3, 4, 5), (1, 4, 5)])
def test_save_and_next_load_preserve_domain_and_independent_cache(tmp_path, monkeypatch, cache_hit, axis, shape, raw_named=False):
    pixels = np.arange(np.prod(shape), dtype=np.float32).reshape(shape)
    channel_axis = -1 if shape == (4, 5, 3) else None
    if axis is not None:
        pixels = pixels[None]
        channel_axis = 3 if channel_axis is not None else None
    mask = np.ones(pixels.shape[:-1] if channel_axis is not None else pixels.shape, dtype=bool)
    path = "/input/A01_s001_w1_z001_t001.tif"
    components = {"well": "A01", "site": "1", "channel": "1", "z_index": "1", "timepoint": "1"}
    metadata = ImagePayloadMetadata(
        source_path=path, source_component_metadata=components, source_image_names=("WholeImage",),
        source_channel_axis=channel_axis, plane_axis=axis,
        source_image_provenance_planes=(
            SourceImageProvenancePlanes.from_components(paths=(path,), component_metadata=(components,))
            if axis is not None else SourceImageProvenancePlanes()
        ),
    )
    payload = pixels if raw_named else metadata.payload_with(pixels, mask)
    if raw_named:
        mask = None
    producer = _runtime()
    pattern = compile_function_pattern(_identity, {}, {})
    plan = replace(producer.request.execution_plan, output_dir=tmp_path, step_scope_id="whole-producer", compiled_function_pattern=pattern)
    producer.request.execution_plan = plan
    files = _MemoryFiles()
    context = ProcessingContext(axis_id="A01", filemanager=files)
    context.microscope_handler = SimpleNamespace(parser=SourceSchemaFilenameParser())
    producer.request.context = context
    producer.pattern_repr = "whole"
    output = producer._validate_and_unstack(
        ImageOutputBundle((payload,), (AlignedImageSliceContext.main_flow("WholeImage"),)) if axis is not None or raw_named else payload,
        PatternGroupData(matching_files=[path, "/input/A01_s001_w1_z002_t001.tif"], main_data_stack=pixels),
    )
    records = producer._save_outputs(output, [path])
    manifest = step_output_manifest(context)
    manifest.record_outputs(plan, records)
    assert records[0].main_flow_plane_axis is axis
    physical = files.values[records[0].output_path]
    assert np.shares_memory(image_payload_data(physical), pixels)
    if not cache_hit:
        context.runtime_image_stack_cache.clear()
    consumer_plan = replace(
        plan, step_index=1, step_scope_id="whole-consumer", input_dir=tmp_path,
        main_input_dependency=StepInputDependency.step_output(source_step_index=0, source_step_scope_id=plan.step_scope_id),
    )
    consumer = PatternGroupRuntime(SimpleNamespace(
        context=context, execution_plan=consumer_plan, compiled_group=pattern.default_group,
        source_binding_plan=CompiledSourceBindingPlan.empty(), component_key=None,
        pattern_group_info="A01_s001_w1_z{iii}_t001.tif",
    ))
    monkeypatch.setattr(consumer, "source_workspace_projection_authority", lambda: SimpleNamespace(projection_if_available=lambda: None))
    monkeypatch.setattr(SourceBindingRuntimeContextRequest, "from_context", classmethod(lambda cls, **kwargs: SimpleNamespace(runtime_context=SourceBindingRuntimeContext.empty)))
    loaded = consumer._load_input_stack().main_data_stack
    assert image_payload_data(loaded).shape == pixels.shape
    assert image_payload_metadata(loaded).plane_axis is axis
    np.testing.assert_array_equal(image_payload_data(loaded), pixels)
    np.testing.assert_array_equal(image_payload_mask(loaded), mask)
    assert not np.shares_memory(image_payload_data(loaded), pixels)
    if mask is not None:
        assert not np.shares_memory(image_payload_mask(loaded), mask)
    assert image_payload_metadata(loaded) is not image_payload_metadata(physical)
    image_payload_metadata(loaded).source_provenance = image_payload_metadata(loaded).source_provenance.with_source_image_names(("Changed",))
    assert image_payload_metadata(physical).source_image_names == ("WholeImage",)
    image_payload_data(loaded).flat[0] = -100
    if mask is not None:
        image_payload_mask(loaded).flat[0] = False
        assert mask.flat[0]
    assert pixels.flat[0] == 0
    consumer._record_main_flow_passthrough([records[0].relative_output_path])
    (passed,) = manifest.produced_records_for(consumer_plan)
    assert passed.main_flow_plane_axis is axis
    assert passed.image_metadata is records[0].image_metadata


@pytest.mark.parametrize("runtime_count", [1, 3])
def test_mixed_named_outputs_retain_each_original_axis_before_projection(runtime_count):
    contexts = (AlignedImageSliceContext.main_flow("Planes"), AlignedImageSliceContext.main_flow("Volume"))
    planes = ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.RUNTIME_SLICE).payload_with(np.ones((runtime_count, 4, 5), dtype=np.float32))
    volume = ImagePayloadMetadata().payload_with(np.ones((4, 5) if runtime_count == 1 else (2, 4, 5), dtype=np.float32))
    bundle = ImageOutputBundle((planes, volume), contexts)
    output = _runtime()._validate_and_unstack(bundle, PatternGroupData(matching_files=[], main_data_stack=planes))
    assert output.stack_payload is None
    assert [output.plane_axis_for_output_context(c) for c in output.slice_contexts] == [RuntimePlaneAxis.RUNTIME_SLICE] * runtime_count + [None]
    assert output.main_flow_source is bundle


def test_passed_through_record_preserves_collapsed_and_filename_coordinates(tmp_path):
    from openhcs.core.steps.function_output_manifest import ProducedOutputSemantics
    from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
    plan = replace(_runtime().request.execution_plan, output_dir=tmp_path)
    record = ProducedOutputSemantics.from_output(
        plan, tmp_path / "A01_s001_w1_z001_t001.tif",
        FunctionOutputIdentity(component_values={"well": "A01"}, filename_component_values={"well": "A01", "z_index": 1}, extension=".tif", source="test"),
        main_flow_plane_axis=None,
    )
    passed = record.passed_through(replace(plan, step_index=1, step_scope_id="next"))
    assert passed.component_values == record.component_values
    assert passed.filename_component_values == record.filename_component_values
    assert passed.main_flow_plane_axis is None


def test_duplicate_physical_path_rejects_contradictory_whole_axis(tmp_path):
    from openhcs.core.steps.function_output_manifest import ProducedOutputSemantics
    from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
    plan = replace(_runtime().request.execution_plan, output_dir=tmp_path)
    opaque = ProducedOutputSemantics.from_output(
        plan, tmp_path / "A01_s001_w1_z001_t001.tif",
        FunctionOutputIdentity(component_values={"well": "A01"}, extension=".tif", source="test"),
        main_flow_plane_axis=None,
    )
    with pytest.raises(ValueError, match="conflicting main-flow image axes"):
        StepOutputManifestStore._unique_output_path_records((opaque, replace(opaque, main_flow_plane_axis=RuntimePlaneAxis.RUNTIME_SLICE)))


@pytest.mark.parametrize("cache_hit", [False, True])
@pytest.mark.parametrize("shape", [(4, 5), (4, 5, 3), (3, 4, 5), (1, 4, 5)])
def test_named_raw_image_actual_save_and_reload_retains_opaque_domain(tmp_path, monkeypatch, cache_hit, shape):
    test_save_and_next_load_preserve_domain_and_independent_cache(
        tmp_path, monkeypatch, cache_hit, None, shape, raw_named=True,
    )


def test_record_axis_survives_replace_and_pickle(tmp_path):
    import pickle
    from openhcs.core.steps.function_output_manifest import ProducedOutputSemantics
    from openhcs.core.steps.function_output_identity import FunctionOutputIdentity
    plan = replace(_runtime().request.execution_plan, output_dir=tmp_path)
    for axis in (None, RuntimePlaneAxis.RUNTIME_SLICE, RuntimePlaneAxis.SOURCE_BINDING):
        record = ProducedOutputSemantics.from_output(
            plan, tmp_path / "A01_s001_w1_z001_t001.tif",
            FunctionOutputIdentity(component_values={"well": "A01"}, extension=".tif", source="test"),
            main_flow_plane_axis=axis,
        )
        assert replace(record).main_flow_plane_axis is axis
        restored = pickle.loads(pickle.dumps(record))
        assert restored == record
        assert restored.main_flow_plane_axis is axis


def _selected_pattern(name):
    from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
    from openhcs.core.pipeline.function_contracts import artifact_inputs
    from openhcs.core.function_patterns import InvocationArtifactInputEdgePlan, InvocationArtifactInputProjectionKey
    spec = ArtifactSpec.input(name, ImageArtifactType)

    @artifact_inputs(spec)
    def consume(image):
        return image

    pattern = compile_function_pattern(consume, {}, {})
    invocation = pattern.default_group.invocations[0]
    invocation = invocation.with_artifact_input_edges((InvocationArtifactInputEdgePlan(
        key=InvocationArtifactInputProjectionKey(invocation_key=invocation.key, input_index=0),
        spec=spec, storage_plan=None, projection=None, consumes_main_flow=True,
    ),))
    return replace(pattern, groups=(replace(pattern.default_group, invocations=(invocation,)),))


@pytest.mark.parametrize("cache_hit", [False, True])
def test_saved_mixed_named_cohort_rejects_joint_load_and_preserves_selected_domains(tmp_path, monkeypatch, cache_hit):
    from openhcs.core.artifacts import ImageArtifactType
    source = "/input/A01_s001_w1_z001_t001.tif"
    components = {"well": "A01", "site": "1", "channel": "1", "z_index": "1", "timepoint": "1"}
    contexts = tuple(AlignedImageSliceContext.main_flow(name, artifact_kind=ImageArtifactType.value) for name in ("Planes", "Volume"))
    scalar_metadata = ImagePayloadMetadata(source_path=source, source_component_metadata=components)
    declared_metadata = scalar_metadata.replace_fields(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(paths=(source,), component_metadata=(components,)),
    )
    planes = declared_metadata.payload_with(np.arange(20, dtype=np.float32).reshape(1, 4, 5))
    opaque_pixels = np.arange(20, dtype=np.float32).reshape(4, 5) + 100
    opaque = scalar_metadata.payload_with(opaque_pixels)
    producer = _runtime()
    pattern = compile_function_pattern(_identity, {}, {})
    plan = replace(producer.request.execution_plan, output_dir=tmp_path, step_scope_id="mixed-producer", compiled_function_pattern=pattern)
    producer.request.execution_plan = plan
    files = _MemoryFiles()
    context = ProcessingContext(axis_id="A01", filemanager=files)
    context.microscope_handler = SimpleNamespace(parser=SourceSchemaFilenameParser())
    producer.request.context = context
    producer.pattern_repr = "mixed"
    loaded = PatternGroupData(matching_files=[source, source], main_data_stack=planes)

    # A prior homogeneous producer caches the same physical paths. Mixed replacement
    # must invalidate that cache rather than leave a false joint runtime domain.
    old_bundle = ImageOutputBundle((planes, declared_metadata.payload_with(opaque_pixels[None])), contexts)
    old_records = producer._save_outputs(producer._validate_and_unstack(old_bundle, loaded), [source, source])
    assert context.runtime_image_stack_cache.get(tuple(r.output_path for r in old_records), memory_type=MEMORY_TYPE_NUMPY) is not None
    bundle = ImageOutputBundle((planes, opaque), contexts)
    output = producer._validate_and_unstack(bundle, loaded)
    records = producer._save_outputs(output, [source, source])
    manifest = step_output_manifest(context)
    manifest.record_outputs(plan, records)
    assert tuple(r.output_path for r in records) == tuple(r.output_path for r in old_records)
    assert [r.main_flow_plane_axis for r in records] == [RuntimePlaneAxis.RUNTIME_SLICE, None]
    assert context.runtime_image_stack_cache.get(tuple(r.output_path for r in records), memory_type=MEMORY_TYPE_NUMPY) is None
    monkeypatch.setattr(SourceBindingRuntimeContextRequest, "from_context", classmethod(lambda cls, **kwargs: SimpleNamespace(runtime_context=SourceBindingRuntimeContext.empty)))

    def consumer_for(compiled):
        consumer_plan = replace(plan, step_index=1, step_scope_id="mixed-consumer", input_dir=tmp_path,
            compiled_function_pattern=compiled,
            main_input_dependency=StepInputDependency.step_output(source_step_index=0, source_step_scope_id=plan.step_scope_id))
        consumer = PatternGroupRuntime(SimpleNamespace(context=context, execution_plan=consumer_plan,
            compiled_group=compiled.default_group, source_binding_plan=CompiledSourceBindingPlan.empty(),
            component_key=None, pattern_group_info="A01_s001_w1_z{iii}_t001.tif"))
        monkeypatch.setattr(consumer, "source_workspace_projection_authority", lambda: SimpleNamespace(projection_if_available=lambda: None))
        return consumer

    with pytest.raises(ValueError, match="different declared image axes"):
        consumer_for(pattern)._load_input_stack()
    for name, expected, axis in (("Planes", image_payload_data(planes), RuntimePlaneAxis.RUNTIME_SLICE), ("Volume", opaque_pixels, None)):
        selected = consumer_for(_selected_pattern(name))
        actual = selected._load_input_stack().main_data_stack
        np.testing.assert_array_equal(image_payload_data(actual), expected)
        assert image_payload_metadata(actual).plane_axis is axis
        if not cache_hit:
            context.runtime_image_stack_cache.clear()
        else:
            selected_path = next(r.output_path for r in records if r.producer_identity.output_key == name)
            context.runtime_image_stack_cache.store((selected_path,), memory_type=MEMORY_TYPE_NUMPY, stack=actual)
        repeated = selected._load_input_stack().main_data_stack
        np.testing.assert_array_equal(image_payload_data(repeated), expected)
        assert image_payload_metadata(repeated).plane_axis is axis


def test_multiple_unprojected_named_binding_domains_fail_existing_bundle_grammar():
    contexts = tuple(AlignedImageSliceContext.main_flow(name) for name in ("First", "Second"))
    payloads = tuple(ImagePayloadMetadata(plane_axis=RuntimePlaneAxis.SOURCE_BINDING).payload_with(
        np.ones((1, 4, 5), dtype=np.float32)) for _ in contexts)
    with pytest.raises(ValueError, match="plane axis to be projected"):
        _runtime()._validate_and_unstack(ImageOutputBundle(payloads, contexts), PatternGroupData(matching_files=[], main_data_stack=payloads[0]))


def test_opaque_named_bundle_uses_existing_same_slice_mask_composition():
    from openhcs.core.aligned_image_payload import ImagePayloadBundleContext
    contexts = tuple(AlignedImageSliceContext.main_flow(name) for name in ("First", "Second"))
    first_mask = np.ones((4, 5), dtype=bool)
    second_mask = first_mask.copy()
    second_mask[0, 0] = False
    payloads = tuple(ImagePayloadMetadata(source_image_names=(name,)).payload_with(
        np.ones((4, 5), dtype=np.float32) * i, mask)
        for i, (name, mask) in enumerate(zip(("First", "Second"), (first_mask, second_mask), strict=True)))
    output = _runtime()._validate_and_unstack(ImageOutputBundle(payloads, contexts), PatternGroupData(matching_files=[], main_data_stack=payloads[0]))
    expected = ImagePayloadBundleContext.from_payloads(payloads).compose()
    assert image_payload_metadata(output.stack_payload).plane_axis is RuntimePlaneAxis.SOURCE_BINDING
    np.testing.assert_array_equal(image_payload_data(output.stack_payload), image_payload_data(expected))
    np.testing.assert_array_equal(image_payload_mask(output.stack_payload), image_payload_mask(expected))
