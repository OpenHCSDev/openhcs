from types import SimpleNamespace
from dataclasses import FrozenInstanceError, fields, replace

import numpy as np
import pytest

from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactSpec,
    ImageArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.callable_contract import CallableContract, CallableMetadata
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.function_patterns import (
    FunctionInvocationKey,
    InvocationArtifactInputEdgePlan,
    InvocationArtifactInputProjectionKey,
    MainFlowInputProjection,
)
from openhcs.core.runtime_adapters import RuntimeAdapterRequest
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.interop.cellprofiler.runtime.artifact_binding import RuntimeInputBindingRequest
from openhcs.interop.cellprofiler.runtime.output_record_request import (
    CellProfilerOutputRecordRequest,
)


def _output_record_request(
    declared_inputs: tuple[ArtifactSpec, ...],
    active_occurrences: tuple[tuple[int, ArtifactSpec], ...],
) -> tuple[
    CellProfilerOutputRecordRequest,
    tuple[InvocationArtifactInputEdgePlan, ...],
]:
    output = ArtifactSpec.output("Result", ObjectLabelsArtifactType)
    contract = CallableContract(
        func=lambda image: image,
        function_name="active_occurrence_probe",
        module_name=__name__,
        metadata=CallableMetadata(
            artifact_inputs=declared_inputs,
            artifact_outputs=(output,),
        ),
    )
    invocation_key = FunctionInvocationKey(
        function_name=contract.function_name,
        group_key="default",
        position=0,
    )
    edges = tuple(
        InvocationArtifactInputEdgePlan(
            key=InvocationArtifactInputProjectionKey(invocation_key, input_index),
            spec=spec,
            storage_plan=None,
            projection=None,
            consumes_main_flow=True,
        )
        for input_index, spec in active_occurrences
    )
    output_plan = ArtifactOutputPlan(
        name=output.name,
        path="/artifacts/result",
        artifact_type=output.artifact_type,
    )
    runtime_request = RuntimeAdapterRequest(
        context=object(),
        callable_contract=contract,
        artifact_inputs={edge.key: edge for edge in edges},
        artifact_outputs={output_plan.ref(): output_plan},
        axis_scope=RuntimeExecutionAxisScope(axis_id="A01"),
    )
    return (
        CellProfilerOutputRecordRequest(
            callable_contract=contract,
            active_input_edges=edges,
            adapter=SimpleNamespace(request=runtime_request),
            spec=output,
            output_plan=output_plan,
            output_value=object(),
            source=SimpleNamespace(),
            kwargs={},
            current_image=object(),
        ),
        edges,
    )


def test_output_source_uses_compiled_runtime_occurrence_for_repeated_roles(
    monkeypatch,
) -> None:
    primary = ArtifactSpec.input(
        "Objects",
        ObjectLabelsArtifactType,
        parameter_name="primary_objects",
    )
    neighbor = ArtifactSpec.input(
        "Objects",
        ObjectLabelsArtifactType,
        parameter_name="neighbor_objects",
    )
    output = ArtifactSpec.output_preserving_source_stack_scope(
        "Result",
        ObjectLabelsArtifactType,
        primary,
    )
    contract = CallableContract(
        func=lambda image: image,
        function_name="repeated_role_probe",
        module_name=__name__,
        metadata=CallableMetadata(
            artifact_inputs=(primary, neighbor),
            artifact_outputs=(output,),
        ),
    )
    invocation_key = FunctionInvocationKey(
        function_name=contract.function_name,
        group_key="default",
        position=0,
    )
    edges = tuple(
        InvocationArtifactInputEdgePlan(
            key=InvocationArtifactInputProjectionKey(invocation_key, input_index),
            spec=spec,
            storage_plan=None,
            projection=None,
            consumes_main_flow=True,
        )
        for input_index, spec in enumerate(contract.artifact_inputs)
    )
    output_plan = ArtifactOutputPlan(
        name=output.name,
        path="/artifacts/result",
        artifact_type=output.artifact_type,
        relations=output.relations,
    )
    runtime_request = RuntimeAdapterRequest(
        context=object(),
        callable_contract=contract,
        artifact_inputs={edge.key: edge for edge in edges},
        artifact_outputs={output_plan.ref(): output_plan},
        axis_scope=RuntimeExecutionAxisScope(axis_id="A01"),
    )
    marker = object()

    monkeypatch.setattr(
        CellProfilerOutputRecordRequest,
        "artifact_source_payload",
        lambda _self, _edge: marker,
    )
    request = CellProfilerOutputRecordRequest(
        callable_contract=contract,
        active_input_edges=edges,
        adapter=SimpleNamespace(request=runtime_request),
        spec=output,
        output_plan=output_plan,
        output_value=object(),
        source=SimpleNamespace(),
        kwargs={},
        current_image=object(),
    )

    assert request.declared_source_payload() is marker
    assert tuple(runtime_request.artifact_inputs) == tuple(edge.key for edge in edges)


def test_output_record_request_accepts_nonzero_duplicate_ref_occurrence() -> None:
    primary = ArtifactSpec.input(
        "Objects",
        ObjectLabelsArtifactType,
        parameter_name="primary_objects",
    )
    neighbor = ArtifactSpec.input(
        "Objects",
        ObjectLabelsArtifactType,
        parameter_name="neighbor_objects",
    )

    request, edges = _output_record_request(
        (primary, neighbor),
        ((1, neighbor),),
    )

    assert request.exact_input_edge(neighbor) is edges[0]
    with pytest.raises(RuntimeError, match="has no exact compiled input edge"):
        request.exact_input_edge(primary)


def test_output_record_request_accepts_noncontiguous_ordered_subset() -> None:
    declared_inputs = tuple(
        ArtifactSpec.input(name, ObjectLabelsArtifactType)
        for name in ("First", "Inactive", "Third")
    )

    request, edges = _output_record_request(
        declared_inputs,
        ((0, declared_inputs[0]), (2, declared_inputs[2])),
    )

    assert request.active_input_edges == edges
    assert tuple(edge.key.input_index for edge in edges) == (0, 2)


def test_output_record_request_accepts_empty_active_subset() -> None:
    declared = ArtifactSpec.input("Inactive", ObjectLabelsArtifactType)

    request, edges = _output_record_request((declared,), ())

    assert request.active_input_edges == edges == ()


def test_output_record_request_rejects_compacted_parameter_role() -> None:
    primary = ArtifactSpec.input(
        "Objects",
        ObjectLabelsArtifactType,
        parameter_name="primary_objects",
    )
    neighbor = ArtifactSpec.input(
        "Objects",
        ObjectLabelsArtifactType,
        parameter_name="neighbor_objects",
    )

    with pytest.raises(ValueError, match="exact declared occurrence"):
        _output_record_request(
            (primary, neighbor),
            ((0, neighbor),),
        )


@pytest.mark.parametrize("active_indexes", ((1, 1), (2, 0)))
def test_output_record_request_rejects_duplicate_or_reordered_indexes(
    active_indexes: tuple[int, int],
) -> None:
    declared_inputs = tuple(
        ArtifactSpec.input(name, ObjectLabelsArtifactType)
        for name in ("First", "Second", "Third")
    )

    with pytest.raises(ValueError, match="strictly increasing declared occurrence"):
        _output_record_request(
            declared_inputs,
            tuple((index, declared_inputs[index]) for index in active_indexes),
        )


def test_output_record_request_rejects_out_of_range_index() -> None:
    declared = ArtifactSpec.input("Only", ObjectLabelsArtifactType)

    with pytest.raises(ValueError, match=r"declared occurrence range \[0, 1\)"):
        _output_record_request(
            (declared,),
            ((1, declared),),
        )


def _image_record_request() -> tuple[CellProfilerOutputRecordRequest, ArtifactSpec]:
    spec = ArtifactSpec.input("Original", ImageArtifactType)
    request, (edge,) = _output_record_request((spec,), ((0, spec),))
    edge = replace(edge, main_flow_projection=MainFlowInputProjection.COMPLETE_PAYLOAD)
    adapter = SimpleNamespace(request=replace(
        request.adapter.request, artifact_inputs={edge.key: edge}
    ))
    return replace(
        request, adapter=adapter, active_input_edges=(edge,),
        current_image=np.zeros((3, 4), dtype=np.float32),
    ), spec


def test_record_binding_keeps_output_admission_before_live_input_validation(
    monkeypatch,
) -> None:
    request, _spec = _image_record_request()
    error = RuntimeError("live input declaration failed")

    def fail_selection(_self):
        raise error

    monkeypatch.setattr(RuntimeAdapterRequest, "selected_artifact_input_specs", fail_selection)
    # Output-only recording does not observe input declaration callbacks.
    assert replace(request).output_value is request.output_value
    with pytest.raises(ValueError, match="does not match active output"):
        replace(request, output_plan=replace(request.output_plan, name="Wrong"))
    # Both source-read operations preserve the original first exception identity.
    for read in (request.artifact_input_value, request.artifact_source_payload):
        with pytest.raises(RuntimeError) as caught:
            read(request.active_input_edges[0])
        assert caught.value is error


def test_record_binding_reads_current_pixels_and_mutable_kwargs_without_holder_aliases() -> None:
    request, spec = _image_record_request()
    assert isinstance(request, RuntimeInputBindingRequest)
    assert "call_kwargs" not in {item.name for item in fields(request)}
    assert not hasattr(request, "__dict__")
    with pytest.raises(TypeError):
        CellProfilerOutputRecordRequest(
            request.callable_contract, request.active_input_edges,
            adapter=request.adapter, kwargs=request.kwargs,
            current_image=request.current_image, spec=request.spec,
            output_plan=request.output_plan, output_value=request.output_value,
            source=request.source,
        )
    with pytest.raises(FrozenInstanceError):
        request.kwargs = {}
    request.kwargs["after_call"] = [1]
    copied = replace(request)
    assert copied.kwargs is request.kwargs
    request.kwargs["after_call"].append(2)
    request.current_image[:] = 0.5
    value = request.declared_artifact_value(spec)
    assert image_payload_data(value) is request.current_image
    assert copied.kwargs["after_call"] == [1, 2]
    np.testing.assert_array_equal(image_payload_data(value), 0.5)
    request.current_image[:] = 0.75
    source = request.artifact_source_payload(request.active_input_edges[0])
    assert image_payload_data(source) is request.current_image
    np.testing.assert_array_equal(image_payload_data(source), 0.75)
    assert image_payload_metadata(source).source_image_names == (spec.name,)


def test_record_endpoint_identity_does_not_change_reference_broadcast_selection() -> None:
    request, spec = _image_record_request()
    equivalent = replace(spec)
    with pytest.raises(RuntimeError, match="has no exact compiled input edge"):
        request.declared_artifact_value(equivalent)
    # The parent's edge API and its reference-only broadcast keep their domains.
    edge = request.active_input_edges[0]
    assert request.artifact_value(edge) is request.current_image
    assert request.input_edge_for_spec(equivalent) is edge
    broadcast = request.stack_broadcast_source_value(equivalent.ref())
    assert image_payload_data(broadcast) is request.current_image


def test_record_input_selection_effects_remain_at_each_read_epoch(monkeypatch) -> None:
    request, spec = _image_record_request()
    original_selection = RuntimeAdapterRequest.selected_artifact_input_specs
    events = []

    def observe_selection(adapter_request):
        events.append(request.kwargs["epoch"])
        return original_selection(adapter_request)

    monkeypatch.setattr(
        RuntimeAdapterRequest, "selected_artifact_input_specs", observe_selection
    )
    # The original binding operation is an independent reference for callback
    # ordering; the record specialization must not move it to construction.
    for epoch in ("first", "after_raw_mutation"):
        request.kwargs["epoch"] = epoch
        events.clear()
        original = RuntimeInputBindingRequest(
            adapter=request.adapter, kwargs=request.kwargs,
            current_image=request.current_image,
        ).runtime_value(request.active_input_edges[0])
        expected_events = tuple(events)
        events.clear()
        actual = request.declared_artifact_value(spec)
        assert tuple(events) == expected_events
        assert image_payload_data(actual) is image_payload_data(original)
        assert image_payload_metadata(actual) == image_payload_metadata(original)


def test_record_explicit_object_subset_preserves_binding_admission() -> None:
    first = ArtifactSpec.input("First", ObjectLabelsArtifactType)
    second = ArtifactSpec.input("Second", ObjectLabelsArtifactType)
    request, _edges = _output_record_request((first, second), ((0, first), (1, second)))
    standalone = RuntimeInputBindingRequest(
        adapter=request.adapter, kwargs=request.kwargs, current_image=request.current_image,
    )
    for subset in ((first,), (replace(second),), ()):
        actual = request.with_object_inputs(subset)
        expected = standalone.with_object_inputs(subset)
        assert actual.object_inputs == expected.object_inputs
        assert actual.active_input_edges is request.active_input_edges
        assert actual.output_value is request.output_value
        assert actual.kwargs is request.kwargs
    undeclared = (ArtifactSpec.input("Unknown", ObjectLabelsArtifactType),)
    with pytest.raises(ValueError) as expected:
        standalone.with_object_inputs(undeclared)
    with pytest.raises(ValueError) as actual:
        request.with_object_inputs(undeclared)
    assert str(actual.value) == str(expected.value)


def test_record_subset_validation_runs_after_output_admission_and_preserves_error_identity(
    monkeypatch,
) -> None:
    request, _spec = _image_record_request()
    error = RuntimeError("subset declaration failure")

    def fail_selection(_self):
        raise error

    monkeypatch.setattr(RuntimeAdapterRequest, "selected_artifact_input_specs", fail_selection)
    for change in (
        lambda: RuntimeInputBindingRequest(
            adapter=request.adapter, kwargs=request.kwargs,
            current_image=request.current_image, selected_object_inputs=(),
        ),
        lambda: request.with_object_inputs(()),
    ):
        with pytest.raises(RuntimeError) as caught:
            change()
        assert caught.value is error
    with pytest.raises(ValueError, match="does not match active output"):
        replace(
            request, selected_object_inputs=(),
            output_plan=replace(request.output_plan, name="Wrong"),
        )
    # The ordinary post-call record still observes no input selector at birth.
    assert replace(request).selected_object_inputs is None
