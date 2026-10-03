"""Loaded cohorts retain original input facts while plans and call images remain live."""

from dataclasses import FrozenInstanceError, fields, replace
import inspect
import pickle
from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.constants.constants import AllComponents, VariableComponents
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import compile_function_pattern
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data, image_payload_metadata
from openhcs.core.source_bindings import CompiledSourceBindingPlan, SourceBindingRuntimeContext
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.steps import function_runtime
from openhcs.core.steps.function_runtime import (
    ComponentArtifactPlans,
    FunctionCoreExecutor,
    PatternGroupData,
    PatternGroupExecutionRequest,
    PatternGroupExecutionScope,
    PatternGroupRuntime,
    RuntimeProfileSink,
)
from openhcs.core.steps.function_output_manifest import NoStepOutputManifestMatch


def _identity(image):
    return image


def _fixture():
    pattern = compile_function_pattern(_identity, {}, {})
    plan = CompiledStepPlan(
        step_index=0, step_type="FunctionStep", step_name="Loaded", axis_id="A01",
        step_scope_id="loaded-cohort", input_memory_type="numpy", output_memory_type="numpy",
        execution_group_scope=ComponentGroupScope.dynamic(AllComponents.CHANNEL),
        variable_components=(VariableComponents.SITE,),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
    )
    context = ProcessingContext(axis_id="A01")
    request = PatternGroupExecutionRequest(
        context=context, execution_plan=plan, compiled_group=pattern.default_group,
        component_value="1", pattern_group_info="A01_s{iii}_w1_z003_t002.tif",
        component_index=7, component_count=99,
        fixed_component_values=((AllComponents.Z_INDEX, "dispatch-value"),),
    )
    paths = ["A01_s001_w1_z003_t002.tif", "A01_s002_w1_z003_t002.tif"]
    payload = ImagePayloadMetadata(
        source_image_provenance_planes=SourceImageProvenancePlanes.from_components(
            paths=tuple(paths),
            component_metadata=tuple(
                {"well": "A01", "site": str(site), "channel": "1", "z_index": "3", "timepoint": "2"}
                for site in (1, 2)
            ),
        ),
    ).payload_with(np.arange(24, dtype=np.float32).reshape(2, 3, 4))
    source_context = SourceBindingRuntimeContext.empty()
    return request, paths, payload, source_context


def test_complete_loaded_owner_has_one_frozen_eleven_field_contract_and_pickle():
    request, paths, payload, source_context = _fixture()
    loaded = PatternGroupData.from_loaded_group(request, paths, payload, source_context)
    expected = (
        "context", "execution_plan", "compiled_group", "component_value", "fixed_component_values",
        "artifacts", "source_binding_context", "runtime_plane_index", "runtime_plane_count",
        "matching_files", "main_data_stack",
    )
    assert PatternGroupData.__bases__ == (PatternGroupExecutionScope,)
    assert tuple(item.name for item in fields(loaded)) == expected
    assert set(inspect.signature(PatternGroupData).parameters) == set(expected)
    assert all(item.kw_only for item in fields(loaded))
    assert not hasattr(loaded, "__dict__")
    assert loaded.context is request.context
    assert loaded.execution_plan is request.execution_plan
    assert loaded.compiled_group is request.compiled_group
    assert loaded.source_binding_context is source_context
    assert loaded.matching_files is paths
    assert loaded.main_data_stack is payload
    with pytest.raises(FrozenInstanceError):
        loaded.runtime_plane_count = 0
    replaced = replace(loaded, component_value="2")
    assert replaced.main_data_stack is payload
    assert replaced.matching_files is paths
    from openhcs.core.orchestrator.execution_result import RuntimeExecutionTransportSerialization

    RuntimeExecutionTransportSerialization.register()
    restored = pickle.loads(pickle.dumps(loaded))
    assert type(restored) is PatternGroupData
    assert restored.runtime_plane_index == 7
    assert restored.runtime_plane_count == 2
    assert restored.execution_plan.step_scope_id == "loaded-cohort"
    assert restored.fixed_component_values == loaded.fixed_component_values
    np.testing.assert_array_equal(image_payload_data(restored.main_data_stack), image_payload_data(payload))


def test_initial_coordinates_stay_captured_while_plan_selectors_follow_mutation():
    request, paths, payload, source_context = _fixture()
    loaded = PatternGroupData.from_loaded_group(request, paths, payload, source_context)
    assert loaded.runtime_plane_count == 2
    assert loaded.fixed_component_values == ((AllComponents.Z_INDEX, "3"), (AllComponents.TIMEPOINT, "2"))
    paths.append("later-mutation.tif")
    image_payload_data(payload)[:] = -1
    assert loaded.runtime_plane_count == 2
    assert len(loaded.matching_files) == 3
    request.execution_plan.axis_id = "B02"
    request.execution_plan.execution_group_scope = ComponentGroupScope.dynamic(AllComponents.SITE)
    assert loaded.axis_scope.axis_id == "B02"
    assert loaded.axis_component == "site"
    assert loaded.fixed_component_values == ((AllComponents.Z_INDEX, "3"), (AllComponents.TIMEPOINT, "2"))


def test_chain_shares_cohort_but_advances_only_current_image_and_memory(monkeypatch):
    request, paths, payload, source_context = _fixture()
    invocation = request.compiled_group.invocations[0]
    group = replace(request.compiled_group, invocations=(invocation, invocation))
    request = replace(request, compiled_group=group)
    loaded = PatternGroupData.from_loaded_group(request, paths, payload, source_context)
    first_output = np.ones((2, 3, 4), dtype=np.float32)
    second_output = np.full((2, 3, 4), 2, dtype=np.float32)
    seen = []

    def execute(executor, *, debug_sink=None):
        assert debug_sink is None
        seen.append((executor.group_data, executor.main_data_arg, executor.source_memory_type))
        if len(seen) == 1:
            paths.append("during-call.tif")
            image_payload_data(payload)[:] = -3
            return first_output
        return second_output

    monkeypatch.setattr(FunctionCoreExecutor, "execute", execute)
    monkeypatch.setattr(FunctionCoreExecutor, "memory_types", lambda _executor: SimpleNamespace(output_type="next-memory"))
    monkeypatch.setattr(function_runtime, "debug_event_sink_from_context", lambda _context: SimpleNamespace(captures_invocation_events=lambda: False))
    assert PatternGroupRuntime.execute_chain(loaded) is second_output
    assert seen[0][0] is loaded and seen[1][0] is loaded
    assert seen[0][1] is payload and seen[1][1] is first_output
    assert seen[0][2] == "numpy" and seen[1][2] == "next-memory"
    assert loaded.main_data_stack is payload
    assert loaded.runtime_plane_count == 2
    assert loaded.fixed_component_values == ((AllComponents.Z_INDEX, "3"), (AllComponents.TIMEPOINT, "2"))


def test_scope_admission_follows_load_profile_inside_execution_error_boundary(monkeypatch):
    request, paths, payload, source_context = _fixture()
    runtime = PatternGroupRuntime(request)
    events = []
    failure = RuntimeError("cohort admission failed")
    monkeypatch.setattr(runtime, "_load_input_stack", lambda: (events.append("load") or (paths, payload, source_context)))
    monkeypatch.setattr(RuntimeProfileSink, "record", lambda label, *_args, **_kwargs: events.append(label))

    def fail_capture(cls, observed_request, observed_paths, observed_payload, observed_context):
        assert observed_request is request
        assert observed_paths is paths
        assert observed_payload is payload
        assert observed_context is source_context
        events.append("capture")
        raise failure

    monkeypatch.setattr(PatternGroupData, "from_loaded_group", classmethod(fail_capture))
    with pytest.raises(ValueError, match="Failed to process pattern group") as exc:
        runtime.run()
    assert exc.value.__cause__ is failure
    assert events == ["load", "pattern_load_stack", "capture"]


@pytest.mark.parametrize("failure", [RuntimeError("load failed"), NoStepOutputManifestMatch("stale")])
def test_load_errors_and_stale_skip_precede_capture_and_execution_wrapping(monkeypatch, failure):
    request, _paths, _payload, _source_context = _fixture()
    runtime = PatternGroupRuntime(request)
    events = []

    def failed_load():
        events.append("load")
        raise failure

    monkeypatch.setattr(runtime, "_load_input_stack", failed_load)
    monkeypatch.setattr(RuntimeProfileSink, "record", lambda *_args, **_kwargs: pytest.fail("failed load must not reach profile/capture"))
    if isinstance(failure, NoStepOutputManifestMatch):
        assert runtime.run() is None
    else:
        with pytest.raises(RuntimeError) as exc:
            runtime.run()
        assert exc.value is failure
    assert events == ["load"]


def test_empty_chain_is_rejected_after_full_capture_and_load_profile(monkeypatch):
    request, paths, payload, source_context = _fixture()
    request = replace(request, compiled_group=replace(request.compiled_group, invocations=()))
    runtime = PatternGroupRuntime(request)
    labels = []
    monkeypatch.setattr(runtime, "_load_input_stack", lambda: (paths, payload, source_context))
    monkeypatch.setattr(RuntimeProfileSink, "record", lambda label, *_args, **_kwargs: labels.append(label))
    with pytest.raises(ValueError, match="has no invocations") as exc:
        runtime.run()
    assert isinstance(exc.value.__cause__, ValueError)
    assert labels == ["pattern_load_stack"]


def test_adapter_request_projects_live_fields_and_preserves_current_payload_epoch():
    request, paths, initial, source_context = _fixture()
    loaded = PatternGroupData.from_loaded_group(request, paths, initial, source_context)
    current = np.ones((2, 3, 4), dtype=np.float32)
    invocation = loaded.compiled_group.invocations[0]
    executor = FunctionCoreExecutor(
        loaded, invocation, ComponentArtifactPlans(inputs={}, outputs={}), "1",
        function_runtime.RuntimePlaneProjection.stack(2), current, "numpy",
    )
    adapter = executor.runtime_adapter_request(current)
    assert adapter.context is loaded.context
    assert adapter.callable_contract is invocation.contract
    assert adapter.source_payload is current
    assert adapter.source_payload is not loaded.main_data_stack
    assert adapter.source_binding_context is source_context
    assert adapter.plane_projection is executor.plane_projection
    assert adapter.source_load_plan is request.execution_plan.source_load_plan
    assert adapter.variable_components == (VariableComponents.SITE,)
    assert adapter.axis_scope.fixed_component_values == loaded.fixed_component_values
    request.execution_plan.axis_id = "B02"
    request.execution_plan.variable_components = (VariableComponents.Z_INDEX,)
    updated = executor.runtime_adapter_request(current)
    assert updated.axis_scope.axis_id == "B02"
    assert updated.variable_components == (VariableComponents.Z_INDEX,)
    assert updated.source_binding_context is source_context


def test_adapter_tuple_admission_precedes_output_map_validation():
    request, paths, initial, source_context = _fixture()
    loaded = PatternGroupData.from_loaded_group(request, paths, initial, source_context)
    invocation = loaded.compiled_group.invocations[0]
    executor = FunctionCoreExecutor(
        loaded, invocation, ComponentArtifactPlans(inputs={}, outputs={"invalid": object()}), "1",
        function_runtime.RuntimePlaneProjection.stack(2), initial, "numpy",
    )
    request.execution_plan.variable_components = None
    with pytest.raises(TypeError, match="NoneType.*not iterable"):
        executor.runtime_adapter_request(initial)
    request.execution_plan.variable_components = ()
    with pytest.raises(TypeError, match="Runtime adapter output"):
        executor.runtime_adapter_request(initial)


def test_component_artifact_admission_precedes_source_provenance_capture(monkeypatch):
    request, paths, initial, source_context = _fixture()
    request.execution_plan.artifact_inputs = {"invalid": object()}
    monkeypatch.setattr(function_runtime, "image_payload_metadata", lambda _payload: pytest.fail("source projection must follow artifact-plan admission"))
    with pytest.raises(TypeError, match="Component artifact input"):
        PatternGroupData.from_loaded_group(request, paths, initial, source_context)


def _stored_primary_fixture(*, preserves_main_flow=False):
    from openhcs.constants.constants import Backend
    from openhcs.core.artifacts import (
        ArtifactInputPlan, ArtifactOutputPlan, ArtifactSpec,
        ArtifactSpecCollection, GroupLineageSourceRelation, ImageArtifactType, SpecialArtifactType,
    )
    from openhcs.core.component_set import ComponentSet
    from openhcs.core.pipeline.function_contracts import artifact_inputs, artifact_outputs
    from openhcs.core.pipeline.path_planner import PathPlanner, PathPlannerArtifactStage
    from openhcs.core.runtime_adapters import runtime_adapter
    from openhcs.core.runtime_artifact_values import RuntimeValue
    from openhcs.core.runtime_plane_projection import RuntimePlaneAxis
    from openhcs.core.component_group_scope import RuntimeExecutionAxisScope

    request, _, payload, source_context = _fixture()
    source = ArtifactSpec.input("Canonical", ImageArtifactType)
    output = ArtifactSpec.output(
        "Processed", SpecialArtifactType if preserves_main_flow else ImageArtifactType,
        relations=(GroupLineageSourceRelation(source=source.ref()),),
    )

    @artifact_inputs(source)
    @artifact_outputs(output)
    @runtime_adapter("runtime", lambda _request: object(), manages_artifact_inputs=True)
    def consume(image, *, runtime):
        return image

    output_plan = ArtifactOutputPlan(
        name=output.name, path="/memory/processed", artifact_type=output.artifact_type,
        relations=output.relations,
    )
    input_plan = ArtifactInputPlan(
        name=source.name, path="/memory/canonical", artifact_type=ImageArtifactType,
        source_step_id=0,
    )
    pattern = compile_function_pattern(consume, {}, {output_plan.ref(): output_plan})
    pattern = PathPlannerArtifactStage(PathPlanner.__new__(PathPlanner)).compile_invocation_input_edges(
        pattern,
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes={},
        execution_group_scope=ComponentGroupScope.ungrouped(),
        consumer_variable_components=ComponentSet((AllComponents.SITE,)),
        main_flow_artifacts=ArtifactSpecCollection((source,)),
    )
    request.execution_plan.step_index = 1
    request.execution_plan.execution_group_scope = ComponentGroupScope.ungrouped()
    request.execution_plan.artifact_inputs = {input_plan.ref(): input_plan}
    request.execution_plan.artifact_outputs = {output_plan.ref(): output_plan}
    request.execution_plan.compiled_function_pattern = pattern
    request = function_runtime.ArtifactPatternGroupExecutionRequest(
        context=request.context, execution_plan=request.execution_plan,
        compiled_group=pattern.default_group, pattern_group_info=input_plan.path,
        component_index=7, component_count=99,
        fixed_component_values=((AllComponents.Z_INDEX, "3"), (AllComponents.TIMEPOINT, "2")),
    )
    payload = image_payload_metadata(payload).replace_fields(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE,
    ).payload_with(image_payload_data(payload), np.ones((2, 3, 4), dtype=bool))
    value = RuntimeValue.from_spec(
        source, payload,
        execution_scope=RuntimeExecutionAxisScope.from_raw("A01", component=None, value=None, fixed_component_values=request.fixed_component_values),
    )
    request.context.runtime_value_store.replace(
        value, path=input_plan.path, backend=Backend.MEMORY.value,
    )
    return request, value, source_context


def test_stored_primary_admission_owns_independent_buffer_and_live_primary_binding(monkeypatch):
    from openhcs.constants.constants import Backend
    from openhcs.core.runtime_image_values import image_payload_mask
    from openhcs.interop.cellprofiler.runtime.artifact_binding import RuntimeInputBindingRequest
    from tests.unit.cellprofiler_runtime_test_support import cellprofiler_runtime_adapter_for_test

    request, canonical, source_context = _stored_primary_fixture()
    runtime = PatternGroupRuntime(request)
    monkeypatch.setattr(
        runtime, "source_workspace_projection_authority",
        lambda: SimpleNamespace(projection_if_available=lambda: None),
    )
    monkeypatch.setattr(
        function_runtime.SourceBindingRuntimeContextRequest, "from_context",
        classmethod(lambda cls, **kwargs: SimpleNamespace(runtime_context=lambda: source_context)),
    )
    paths, admitted, admitted_context = request.load_input_stack(runtime)
    assert paths == ["/memory/canonical"]
    assert admitted_context is source_context
    assert not np.shares_memory(image_payload_data(admitted), image_payload_data(canonical.data))
    assert not np.shares_memory(image_payload_mask(admitted), image_payload_mask(canonical.data))
    loaded = PatternGroupData.from_loaded_group(request, paths, admitted, admitted_context)
    assert loaded.runtime_plane_count == 2
    assert loaded.runtime_plane_index == 7
    assert loaded.fixed_component_values == ((AllComponents.Z_INDEX, "3"), (AllComponents.TIMEPOINT, "2"))
    replacement = replace(canonical, data=image_payload_metadata(canonical.data).payload_with(
        np.full((2, 3, 4), 31, dtype=np.float32), np.zeros((2, 3, 4), dtype=bool),
    ))
    request.context.runtime_value_store.replace(
        replacement, path=paths[0], backend=Backend.MEMORY.value,
    )
    image_payload_data(admitted)[:] = 17
    image_payload_mask(admitted)[:] = False
    invocation = request.compiled_group.invocations[0]
    edge = invocation.artifact_input_edges[0]
    adapter = cellprofiler_runtime_adapter_for_test(
        runtime_value_store=request.context.runtime_value_store,
        callable_contract=invocation.contract,
        artifact_inputs={edge.key: edge}, axis_scope=request.axis_scope,
    )
    bound = RuntimeInputBindingRequest(adapter=adapter, kwargs={}, current_image=admitted).artifact_value(edge)
    assert bound is admitted
    np.testing.assert_array_equal(image_payload_data(bound), 17)
    np.testing.assert_array_equal(image_payload_data(replacement.data), 31)
    _, next_admitted, _ = request.load_input_stack(runtime)
    np.testing.assert_array_equal(image_payload_data(next_admitted), 31)
    assert not np.shares_memory(image_payload_data(next_admitted), image_payload_data(replacement.data))
    assert loaded.runtime_plane_count == 2


def test_checkpoint_demand_follows_preserved_input_to_native_reader():
    from openhcs.constants.constants import Backend
    from openhcs.core.step_dependencies import StepInputDependency

    request, _, _ = _stored_primary_fixture()
    source = replace(request.execution_plan, step_index=0, step_scope_id="source", write_backend=Backend.MEMORY.value)
    preserving_request, _, _ = _stored_primary_fixture(preserves_main_flow=True)
    preserving_pattern = preserving_request.execution_plan.compiled_function_pattern
    preserving = replace(
        source, step_index=1, step_scope_id="preserving", compiled_function_pattern=preserving_pattern,
        main_input_dependency=StepInputDependency.step_output(source_step_index=0, source_step_scope_id="source"),
    )
    native = replace(
        source, step_index=2, step_scope_id="native", compiled_function_pattern=compile_function_pattern(_identity, {}, {}),
        main_input_dependency=StepInputDependency.step_output(source_step_index=1, source_step_scope_id="preserving"),
    )
    plans = {0: source, 1: preserving, 2: native}
    assert source.requires_main_flow_checkpoint(plans)
    assert preserving.requires_main_flow_checkpoint(plans)
    native.compiled_function_pattern = source.compiled_function_pattern
    assert not source.requires_main_flow_checkpoint(plans)
    source.streaming_configs = {"viewer": object()}
    assert source.requires_main_flow_checkpoint(plans)


def test_artifact_loaded_coordinates_keep_producer_authority_over_original_source():
    request, canonical, source_context = _stored_primary_fixture()
    exact_coordinates = (
        (AllComponents.CHANNEL, "ProducedChannel"),
        (AllComponents.Z_INDEX, "3"),
        (AllComponents.TIMEPOINT, "2"),
    )
    request = replace(request, fixed_component_values=exact_coordinates)
    assert image_payload_metadata(canonical.data).source_provenance.with_common_scalar_identity_from_planes().source_component_metadata["channel"] == "1"
    loaded = PatternGroupData.from_loaded_group(
        request, ["/memory/canonical"], canonical.data, source_context,
    )
    assert loaded.fixed_component_values == exact_coordinates
    canonical.data.metadata.source_provenance = canonical.data.metadata.source_provenance.with_source_component_metadata({"channel": "9"})
    assert loaded.fixed_component_values == exact_coordinates


def test_conversion_and_sequential_filter_use_the_same_transport_admission():
    from pathlib import Path
    from openhcs.constants.constants import Backend, SequentialComponents
    from openhcs.core.compiled_step_plan import (
        InputConversionPlan, SequentialRuntimeFilter, SequentialRuntimeFilterPlan,
    )

    request, _, _ = _stored_primary_fixture()
    plan = request.execution_plan
    assert plan.stored_primary_input_edges_for_group(request.compiled_group, None)
    plan.input_conversion = InputConversionPlan(
        output_dir=Path("/memory/input"), backend=Backend.MEMORY.value,
        uses_virtual_workspace=True, original_subdir="images",
    )
    assert plan.stored_primary_input_edges_for_group(request.compiled_group, None) is None
    plan.input_conversion = None
    plan.sequential_filter_plan = SequentialRuntimeFilterPlan(
        filters=(SequentialRuntimeFilter(SequentialComponents.TIMEPOINT, "2"),),
    )
    assert plan.stored_primary_input_edges_for_group(request.compiled_group, None) is None


def test_same_step_primary_producer_is_not_queried_before_its_callable_runs():
    request, _, _ = _stored_primary_fixture()
    plan = request.execution_plan
    assert plan.stored_primary_input_edges_for_group(request.compiled_group, None)
    invocation = request.compiled_group.invocations[0]
    edge = invocation.artifact_input_edges[0]
    later_edge = replace(edge, storage_plan=replace(
        edge.storage_plan, source_step_id=plan.step_index,
        source_step_scope_id=plan.step_scope_id,
    ))
    group = replace(request.compiled_group, invocations=(
        invocation.with_artifact_input_edges((later_edge,)),
    ))
    assert plan.stored_primary_input_edges_for_group(group, None) is None
