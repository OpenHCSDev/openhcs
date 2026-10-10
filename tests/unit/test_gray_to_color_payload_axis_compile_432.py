"""#432: a created color payload axis is not inherited from grayscale source files."""

from dataclasses import replace

import numpy as np
import pytest
import tifffile

from openhcs.core.callable_contract import (
    CallableContract, CreatedPayloadAxis, PayloadAxisRequirement, PreservedPayloadAxes,
    creates_payload_axis, preserves_payload_axes,
)
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.function_patterns import (
    CompiledFunctionGroup, CompiledFunctionPattern, PayloadAxisProof,
    InheritedPayloadAxisProof, CreatedPayloadAxisProof,
    UnprovedPayloadAxisProof,
)
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.aligned_image_payload import ImagePayloadBundleContext
from openhcs.core.image_payload_execution_mode import NaturalExecution
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.color import (
    ColorToGrayMode, ImageChannelType, color_to_gray, gray_to_color,
    split_color_to_gray,
)
from test_gray_to_color_binding_axis_432 import _execute_bound_stack, _source_plane
from test_payload_axis_compile_gate import _compiled_pattern, _session
from openhcs.core.payload_axes import ColourSampleAxisSpec
from openhcs.core.axes import ColourAxis


def _gray_creator_session(tmp_path):
    path = tmp_path / "synthetic-gray.tif"
    tifffile.imwrite(path, np.zeros((4, 5), dtype=np.uint16))
    session = _session(tmp_path, (path,))
    producer = replace(
        session.plans[0], step_name="ComposeScalarRoles", step_scope_id="step-0",
        compiled_function_pattern=_compiled_pattern(gray_to_color),
    )
    consumer = CompiledStepPlan(
        step_index=1, step_name="SplitComposedRoles", axis_id="A01",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=0, source_step_scope_id="step-0",
        ),
        compiled_function_pattern=_compiled_pattern(color_to_gray),
    )
    session.plans = {0: producer, 1: consumer}
    session.context.step_plans = session.plans
    return session


def test_declared_gray_creator_proves_color_consumer_before_execution(tmp_path):
    # Intended acceptance: unchanged strict consumer accepts a declared creator.
    # Original RED matched the installed producer-step error, not a live replay.
    PipelineCompiler.validate_payload_axis_requirements(_gray_creator_session(tmp_path))


def test_declared_gray_creator_proves_same_group_color_consumer(tmp_path):
    session = _gray_creator_session(tmp_path)
    group = CompiledFunctionGroup("default", tuple(
        invocation
        for plan in session.plans.values()
        for invocation in plan.compiled_function_pattern.iter_invocations()
    ))
    session.plans = {0: replace(session.plans[0], compiled_function_pattern=CompiledFunctionPattern(
        groups=(group,), is_grouped=False,
    ))}
    session.context.step_plans = session.plans
    PipelineCompiler.validate_payload_axis_requirements(session)


def test_preservation_annotation_cannot_create_missing_source_payload_axis(tmp_path):
    session = _gray_creator_session(tmp_path)
    producer = session.plans[0]
    (invocation,) = tuple(producer.compiled_function_pattern.iter_invocations())
    # A local counterexample only: do not mutate production callable/registry.
    falsely_preserving = replace(invocation, contract=replace(invocation.contract, metadata=replace(
        invocation.contract.metadata, payload_axis_transition=PreservedPayloadAxes(),
    )))
    session.plans[0] = replace(producer, compiled_function_pattern=CompiledFunctionPattern(
        groups=(CompiledFunctionGroup("default", (falsely_preserving,)),), is_grouped=False,
    ))
    session.context.step_plans = session.plans
    with pytest.raises(ValueError, match="requires a declared ColourAxis payload axis"):
        PipelineCompiler.validate_payload_axis_requirements(session)


def _runtime_scalar_role_split():
    raw = np.arange(20, dtype=np.float32).reshape(4, 5) * 1000 / 65535
    capped = np.clip((raw - 39 / 65535) / (5961 / 65535), 0, 1)
    bundle = ImagePayloadBundleContext.from_payloads(tuple(
        _source_plane(pixels, name)
        for pixels, name in ((raw, "RawBody"), (capped, "CappedOutgrowth"))
    )).compose()
    composite = _execute_bound_stack(bundle)
    assert composite.data.shape == (4, 5, 2)
    assert composite.metadata.axis_position(ColourAxis) == -1
    contract = CallableContract.from_callable(color_to_gray)
    result = CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), composite,
        {"mode": ColorToGrayMode.SPLIT, "image_type": ImageChannelType.CHANNELS,
         "channel_indices": (0, 1), "contributions": (1.0, 1.0)},
        execution_mode=NaturalExecution,
    )
    return result, (raw, capped)


def test_original_runtime_split_preserves_both_role_values_and_physical_channel():
    result, expected_roles = _runtime_scalar_role_split()
    assert len(result.slices) == 2
    for output, expected in zip(result.slices, expected_roles, strict=True):
        assert output.data.shape == (4, 5)
        np.testing.assert_array_equal(output.data, expected)
        assert output.metadata.source_component_metadata["channel"] == "2"
        assert set(output.metadata.source_image_paths) == {"/synthetic/A01_s1_w2_z1_t1.tif"}


def test_scalar_role_outputs_consume_the_color_payload_axis():
    result, _expected_roles = _runtime_scalar_role_split()
    for output in result.slices:
        assert output.data.shape == (4, 5)
        assert output.metadata.axis_position(ColourAxis) is None


@pytest.mark.parametrize("same_group", [False, True])
def test_independent_creator_declaration_needs_no_consumer_edits(tmp_path, monkeypatch, same_group):
    @creates_payload_axis(ColourAxis)
    def independent_lane_creator(image):
        return np.stack((image, image * 2), axis=-1)

    @preserves_payload_axes
    def independent_lane_preserver(image):
        return image.copy()

    # Behavior, not an inheritance assertion or a fake source-color header.
    gray = np.arange(20, dtype=np.float32).reshape(4, 5)
    created = independent_lane_preserver(independent_lane_creator(gray))
    np.testing.assert_array_equal(created[..., 0], gray)
    np.testing.assert_array_equal(created[..., 1], gray * 2)
    session = _gray_creator_session(tmp_path)
    producer_invocations = tuple(
        invocation
        for callable_ in (independent_lane_creator, independent_lane_preserver)
        for invocation in _compiled_pattern(callable_).iter_invocations()
    )
    if same_group:
        consumer_invocations = tuple(session.plans[1].compiled_function_pattern.iter_invocations())
        session.plans = {0: replace(session.plans[0], compiled_function_pattern=CompiledFunctionPattern(
            groups=(CompiledFunctionGroup("default", producer_invocations + consumer_invocations),),
            is_grouped=False,
        ))}
    else:
        session.plans[0] = replace(session.plans[0], compiled_function_pattern=CompiledFunctionPattern(
            groups=(CompiledFunctionGroup("default", producer_invocations),), is_grouped=False,
        ))
    session.context.step_plans = session.plans

    def reject_source_backtracking(*args, **kwargs):
        pytest.fail("A declared creator must stop source-payload axis backtracking")

    monkeypatch.setattr(
        "openhcs.core.pipeline.compiler.require_image_file_source_metadata",
        reject_source_backtracking,
    )
    PipelineCompiler.validate_payload_axis_requirements(session)


@pytest.mark.parametrize("unknown_after_creator", [False, True])
def test_group_proof_stops_at_creator_but_rejects_later_unknown(unknown_after_creator):
    def unknown(image):
        return image

    functions = (gray_to_color, unknown) if unknown_after_creator else (unknown, gray_to_color)
    invocations = tuple(
        invocation for callable_ in functions
        for invocation in _compiled_pattern(callable_).iter_invocations()
    )
    proof = CompiledFunctionGroup("default", invocations).payload_axis_proof(
        PayloadAxisRequirement(ColourAxis),
    )
    failures = []
    assert proof.validate_obligation(
        failure_message=lambda invocation: invocation.contract.function_name,
        source_validation=lambda: pytest.fail("Creation/rejection must stop source validation"),
        failures=failures,
    )
    assert failures == (["unknown"] if unknown_after_creator else [])


@pytest.mark.parametrize("source_complete", [False, True])
def test_inherited_proof_executes_actual_source_obligation_once(source_complete):
    visits, failures = [], []

    def validate_source():
        visits.append("source")
        return source_complete

    complete = InheritedPayloadAxisProof().validate_obligation(
        source_validation=validate_source,
        failure_message=lambda invocation: pytest.fail("Inherited proof has no failed invocation"),
        failures=failures,
    )
    assert complete is source_complete
    assert visits == ["source"]
    assert failures == []


@pytest.mark.parametrize("capability_first", [False, True])
@pytest.mark.parametrize("proof_type,args,expected_visits,expected_failures", [
    (InheritedPayloadAxisProof, (), ["before", "source", "after"], []),
    (CreatedPayloadAxisProof, (), ["before", "after"], []),
    (UnprovedPayloadAxisProof,
     tuple(_compiled_pattern(color_to_gray).iter_invocations()), ["before", "after"], ["rejected color_to_gray"]),
])
def test_independent_same_node_validation_capability_composes_both_mro_orders(
    capability_first, proof_type, args, expected_visits, expected_failures,
):
    visits, failures = [], []

    class ValidationVisitCapability(PayloadAxisProof):
        def validate_obligation(self, **kwargs):
            visits.append("before")
            result = super().validate_obligation(**kwargs)
            visits.append("after")
            return result

    # Same nominal owner in both bases puts the independent capability before
    # the shared operation in C3, regardless of its position beside the leaf.
    bases = (ValidationVisitCapability, proof_type) if capability_first else (proof_type, ValidationVisitCapability)
    declared_proof = type("IndependentlyObservedProof", bases, {})(*args)

    def validate_source():
        visits.append("source")
        return True

    assert declared_proof.validate_obligation(
        source_validation=validate_source,
        failure_message=lambda invocation: "rejected " + invocation.contract.function_name,
        failures=failures,
    )
    assert visits == expected_visits
    assert failures == expected_failures


def test_source_validation_rejection_is_collected_once_by_proof_owner():
    failures = []

    def reject_source():
        raise ValueError("exact source missing its declared payload axis")

    assert InheritedPayloadAxisProof().validate_obligation(
        source_validation=reject_source,
        failure_message=lambda invocation: pytest.fail("No failed invocation"),
        failures=failures,
    )
    assert failures == ["exact source missing its declared payload axis"]


def test_color_to_gray_does_not_preserve_consumed_payload_axis_for_later_consumer(tmp_path):
    session = _gray_creator_session(tmp_path)
    consumer = session.plans[1]
    session.plans[2] = replace(
        consumer, step_index=2, step_name="RejectSecondScalarSplit",
        main_input_dependency=StepInputDependency.step_output(
            source_step_index=1, source_step_scope_id="step-1",
        ),
    )
    session.plans[1] = replace(consumer, step_scope_id="step-1")
    session.context.step_plans = session.plans
    with pytest.raises(ValueError, match="not preserved by producer step 1 callable 'color_to_gray'"):
        PipelineCompiler.validate_payload_axis_requirements(session)


@pytest.mark.parametrize("image_type", tuple(ImageChannelType))
def test_scalar_projection_modes_keep_pixels_mask_and_original_source(image_type):
    pixels = np.arange(60, dtype=np.float32).reshape(4, 5, 3) / 60
    mask = np.arange(20).reshape(4, 5) % 3 != 0
    source = _source_plane(pixels, "OriginalColor")
    metadata = source.metadata.with_axis(ColourSampleAxisSpec(), -1)
    source = metadata.payload_with(pixels, mask)
    expected = split_color_to_gray(source, image_type, (0, 1))
    contract = CallableContract.from_callable(color_to_gray)
    result = CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), source,
        {"mode": ColorToGrayMode.SPLIT, "image_type": image_type,
         "channel_indices": (0, 1), "contributions": (1.0, 1.0)},
        execution_mode=NaturalExecution,
    )
    for output, expected_pixels in zip(result.slices, expected, strict=True):
        np.testing.assert_array_equal(output.data, expected_pixels)
        np.testing.assert_array_equal(output.mask, mask)
        output_metadata = output.metadata
        assert output_metadata.axis_position(ColourAxis) is None
        assert output_metadata.source_path == metadata.source_path
        assert output_metadata.source_component_metadata == metadata.source_component_metadata
        assert output_metadata.source_image_names == metadata.source_image_names
        assert output_metadata.source_voxel_spacing == metadata.source_voxel_spacing
        assert output_metadata.source_spatial_domain == metadata.source_spatial_domain
    np.testing.assert_array_equal(source.data, pixels)
    assert source.metadata.axis_position(ColourAxis) == -1
