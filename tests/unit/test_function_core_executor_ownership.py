"""One executor owns invocation state and polymorphic artifact-edge resolution."""

from dataclasses import FrozenInstanceError, MISSING, fields, replace
import inspect
import pickle
from types import SimpleNamespace

import numpy as np
import pytest

from openhcs.core.artifacts import (
    ArtifactSpec,
    ArtifactSpecCollection,
    MetadataArtifactType,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.component_group_scope import ComponentGroupScope
from openhcs.core.function_patterns import (
    CompiledMetadataArtifactInputEdgePlan,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
    compile_function_pattern,
)
from openhcs.core.pipeline.function_contracts import artifact_inputs
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.source_bindings import CompiledSourceBindingPlan
from openhcs.core.steps.function_runtime import (
    FunctionCoreExecutor,
    PatternGroupData,
)

_FIRST = ArtifactSpec.input("First", MetadataArtifactType, parameter_name="first")
_SECOND = ArtifactSpec.input("Second", MetadataArtifactType, parameter_name="second")


@artifact_inputs(_FIRST, _SECOND)
def _consume_metadata(image, *, first, second):
    return image


def _executor():
    first = {"value": 1}
    second = {"value": 2}
    pattern = compile_function_pattern(
        (_consume_metadata, {"first": first, "second": second}), {}, {}
    )
    invocation = next(pattern.iter_invocations())
    edges = tuple(
        InvocationArtifactInputEdgePlan.from_source_declarations(
            key=InvocationArtifactInputProjectionKey(
                invocation_key=invocation.key, input_index=index
            ),
            spec=spec,
            main_flow_artifacts=ArtifactSpecCollection(()),
            invocation_sources=ArtifactSpecCollection(()),
            metadata_available=True,
        )
        for index, spec in enumerate((_FIRST, _SECOND))
    )
    invocation = invocation.with_artifact_input_edges(edges)
    plan = CompiledStepPlan(
        step_index=0,
        step_name="MetadataBinding",
        step_scope_id="metadata-binding",
        axis_id="A01",
        input_memory_type="numpy",
        output_memory_type="numpy",
        execution_group_scope=ComponentGroupScope.ungrouped(),
        source_binding_plan=CompiledSourceBindingPlan.empty(),
    )
    artifacts = ({edge.key: edge for edge in edges}, {})
    initial_image = np.arange(6, dtype=np.float32).reshape(1, 2, 3)
    scope = PatternGroupData(
        matching_files=["input.tif"],
        main_data_stack=initial_image,
        context=SimpleNamespace(axis_id="A01"),
        execution_plan=plan,
        compiled_group=replace(pattern.default_group, invocations=(invocation,)),
        artifact_inputs={},
        artifact_outputs={},
        runtime_plane_index=0,
        runtime_plane_count=1,
    )
    return FunctionCoreExecutor(
        scope,
        invocation,
        *artifacts,
        None,
        RuntimePlaneProjection.stack(),
        initial_image,
        "numpy",
    )


def test_executor_retains_positional_layout_with_loaded_group_owner_and_frozen_slots():
    expected = (
        "group_data",
        "invocation",
        "artifact_inputs",
        "artifact_outputs",
        "group_key",
        "plane_projection",
        "main_data_arg",
        "source_memory_type",
    )
    declaration = fields(FunctionCoreExecutor)
    assert tuple(field.name for field in declaration) == expected
    assert tuple(inspect.signature(FunctionCoreExecutor).parameters) == expected
    assert all(
        field.init and field.compare and field.repr and not field.kw_only
        for field in declaration
    )
    assert all(
        field.default is MISSING and field.default_factory is MISSING
        for field in declaration
    )
    executor = _executor()
    assert not hasattr(executor, "__dict__")
    with pytest.raises(FrozenInstanceError):
        executor.source_memory_type = "other"
    replaced = replace(executor, group_key="changed")
    assert replaced.group_key == "changed"
    assert replaced.group_data is executor.group_data
    assert replaced.artifact_inputs is executor.artifact_inputs
    assert replaced.artifact_outputs is executor.artifact_outputs


def test_executor_pickle_retains_real_scope_edges_and_ordered_field_state():
    executor = _executor()
    original_state = executor.__getstate__()
    assert len(original_state) == len(fields(FunctionCoreExecutor))
    assert original_state[0] is executor.group_data
    assert original_state[-1] == "numpy"
    restored = pickle.loads(pickle.dumps(executor))
    assert type(restored) is FunctionCoreExecutor
    assert restored.group_data.execution_plan.step_scope_id == "metadata-binding"
    assert tuple(edge.spec.ref() for edge in restored.artifact_inputs.values()) == (
        _FIRST.ref(),
        _SECOND.ref(),
    )
    assert all(
        isinstance(edge, CompiledMetadataArtifactInputEdgePlan)
        for edge in restored.artifact_inputs.values()
    )
    assert restored.invocation.kwargs_dict == executor.invocation.kwargs_dict
    np.testing.assert_array_equal(restored.main_data_arg, executor.main_data_arg)
    assert not hasattr(restored, "__dict__")


def test_metadata_edge_dispatch_keeps_live_compiled_arguments_and_declaration_order(monkeypatch):
    executor = _executor()

    def unexpected_source_resolution(*args, **kwargs):
        pytest.fail("metadata edge owns its compiled argument; no image-source lookup")

    monkeypatch.setattr(FunctionCoreExecutor, "declared_source_payload", unexpected_source_resolution)
    kwargs = {}
    loaded = executor.load_artifact_inputs(kwargs, executor.main_data_arg)
    assert tuple(kwargs) == ("first", "second")
    assert tuple(loaded) == (_FIRST.ref(), _SECOND.ref())
    assert kwargs["first"] is executor.invocation.kwargs_dict["first"]
    kwargs["first"]["value"] = 7
    repeated = {}
    executor.load_artifact_inputs(repeated, executor.main_data_arg)
    assert repeated["first"] is kwargs["first"]
    assert repeated["first"]["value"] == 7


def test_missing_metadata_argument_error_stays_on_selected_edge_before_later_binding():
    executor = _executor()
    invocation = replace(executor.invocation, kwargs=(("second", {"value": 2}),))
    executor = replace(executor, invocation=invocation)
    kwargs = {}
    with pytest.raises(ValueError, match="Metadata artifact .* has no compiled parameter value"):
        executor.load_artifact_inputs(kwargs, executor.main_data_arg)
    assert kwargs == {}


def test_missing_storage_error_remains_owned_by_executor():
    executor = _executor()
    with pytest.raises(ValueError, match="storage-backed edge"):
        executor.load_artifact_input(
            "first", next(iter(executor.artifact_inputs.values()))
        )
