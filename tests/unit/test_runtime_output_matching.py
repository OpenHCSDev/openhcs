from __future__ import annotations

import numpy as np
import pytest

from openhcs.constants.constants import AllComponents
from openhcs.core.aligned_image_payload import (
    AlignedImageSliceContext,
    AlignedImageStack,
)
from openhcs.core.artifacts import (
    ArtifactOutputPlan,
    ArtifactSpec,
    ImageArtifactType,
    MeasurementsArtifactType,
    ObjectLabelsArtifactType,
)
from openhcs.core.callable_contract import (
    CallableContract,
    CallableMetadata,
    FunctionStepExecutionScope,
)
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data
from openhcs.core.runtime_plane_projection import (
    RuntimePlaneAxis,
    RuntimePlaneAxisValueProjection,
)
from openhcs.core.runtime_slice_projection import RuntimeSliceProjectionDeclarationError
from openhcs.core.function_patterns import (
    CompiledFunctionInvocation,
    FunctionInvocationKey,
)


def _contract(
    *outputs: ArtifactSpec,
    inputs: tuple[ArtifactSpec, ...] = (),
    execution_scope: FunctionStepExecutionScope = FunctionStepExecutionScope.AXIS,
) -> CallableContract:
    return CallableContract(
        func=lambda value: value,
        function_name="process",
        module_name=None,
        metadata=CallableMetadata(
            artifact_inputs=inputs,
            artifact_outputs=outputs,
            execution_scope=execution_scope,
        ),
    )


def test_runtime_output_matcher_maps_canonical_and_trailing_slots() -> None:
    image = ArtifactSpec.output("Image", ImageArtifactType)
    measurements = ArtifactSpec.output("Measurements", MeasurementsArtifactType)

    resolved = _contract(image, measurements).resolve_returned_output(
        ("image", "measurements")
    )

    assert resolved == {
        image.ref(): "image",
        measurements.ref(): "measurements",
    }


def test_matcher_contextualizes_declared_axis_before_resolving_complete_abi() -> None:
    first = ArtifactSpec.output("First", ImageArtifactType)
    second = ArtifactSpec.output("Second", ImageArtifactType)
    measurements = ArtifactSpec.output("Measurements", MeasurementsArtifactType)
    data = np.arange(24, dtype=np.float32).reshape((2, 3, 4))
    payload = ImagePayloadMetadata(
        plane_axis=RuntimePlaneAxis.RUNTIME_SLICE
    ).payload_with(data, None)
    trailing = object()
    contract = _contract(first, second, measurements)
    matcher_returned_output = (payload, trailing)
    projection = RuntimePlaneAxisValueProjection.preserve(
        axis=RuntimePlaneAxis.RUNTIME_SLICE,
        axis_size=2,
    )

    returned = contract.contextualize_returned_canonical_output(
        matcher_returned_output, plane_projection=projection
    )
    resolved = contract.resolve_returned_output(returned)

    assert returned[1] is trailing
    assert resolved[measurements.ref()] is trailing
    for index, spec in enumerate((first, second)):
        selected = image_payload_data(resolved[spec.ref()])
        np.testing.assert_array_equal(selected, data[index])
        assert np.shares_memory(selected, data)
    assert contract.contextualize_returned_canonical_output(returned) is returned

    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="without a compiled"):
        contract.contextualize_returned_canonical_output(matcher_returned_output)
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="already selected"):
        contract.contextualize_returned_canonical_output(
            matcher_returned_output, plane_projection=projection.selected_plane(0)
        )
    with pytest.raises(ValueError, match="projection declares 3 value"):
        contract.contextualize_returned_canonical_output(
            matcher_returned_output,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.RUNTIME_SLICE,
                axis_size=3,
            ),
        )
    with pytest.raises(RuntimeSliceProjectionDeclarationError, match="plane axis"):
        contract.contextualize_returned_canonical_output(
            matcher_returned_output,
            plane_projection=RuntimePlaneAxisValueProjection.preserve(
                axis=RuntimePlaneAxis.SOURCE_BINDING,
                axis_size=2,
            ),
        )


def test_runtime_output_matcher_uses_exact_multi_canonical_contexts() -> None:
    first = ArtifactSpec.output("First", ImageArtifactType)
    second = ArtifactSpec.output("Second", ImageArtifactType)
    measurements = ArtifactSpec.output("Measurements", MeasurementsArtifactType)
    canonical = AlignedImageStack(
        ("second-value", "first-value"),
        (
            AlignedImageSliceContext.main_flow(
                second.name,
                artifact_kind=second.artifact_type.value,
            ),
            AlignedImageSliceContext.main_flow(
                first.name,
                artifact_kind=first.artifact_type.value,
            ),
        ),
    )

    resolved = _contract(first, second, measurements).resolve_returned_output(
        (canonical, "measurements")
    )

    assert resolved == {
        first.ref(): "first-value",
        second.ref(): "second-value",
        measurements.ref(): "measurements",
    }


def test_runtime_output_matcher_binds_selected_plans_after_resolving_complete_abi() -> (
    None
):
    image = ArtifactSpec.output("Image", ImageArtifactType)
    measurements = ArtifactSpec.output("Measurements", MeasurementsArtifactType)
    measurement_plan = ArtifactOutputPlan(
        name=measurements.name,
        path="/memory/measurements",
        artifact_type=measurements.artifact_type,
    )

    resolved, matched_outputs = _contract(
        image, measurements
    ).resolve_returned_plan_values(("image", "measurements"), (measurement_plan,))

    assert resolved == {
        image.ref(): "image",
        measurements.ref(): "measurements",
    }
    assert matched_outputs == ((measurement_plan, measurements, "measurements"),)


def test_runtime_invocation_selects_storage_without_truncating_callable_abi() -> None:
    first_input = ArtifactSpec.input("FirstInput", ImageArtifactType)
    second_input = ArtifactSpec.input("SecondInput", ImageArtifactType)
    first = ArtifactSpec.output("First", ImageArtifactType)
    second = ArtifactSpec.output("Second", ImageArtifactType)
    first_plan = ArtifactOutputPlan(
        name=first.name,
        path="/memory/first",
        artifact_type=first.artifact_type,
    )
    second_plan = ArtifactOutputPlan(
        name=second.name,
        path="/memory/second",
        artifact_type=second.artifact_type,
    )
    compiled = CompiledFunctionInvocation(
        key=FunctionInvocationKey("process", "default", 0),
        contract=_contract(
            first,
            second,
            inputs=(first_input, second_input),
        ),
        artifact_output_plans=(first_plan, second_plan),
    )
    runtime_output_plans = (second_plan,)
    first_value = np.zeros((4, 5), dtype=np.float32)
    second_value = np.ones((4, 5), dtype=np.float32)
    returned_stack = AlignedImageStack(
        (first_value, second_value),
        (
            AlignedImageSliceContext.main_flow(
                first.name,
                artifact_kind=first.artifact_type.value,
            ),
            AlignedImageSliceContext.main_flow(
                second.name,
                artifact_kind=second.artifact_type.value,
            ),
        ),
    )

    resolved, matched = compiled.contract.resolve_returned_plan_values(
        returned_stack, runtime_output_plans
    )

    assert compiled.contract.canonical_return_output_specs.specs == (first, second)
    assert compiled.contract.artifact_inputs.specs == (first_input, second_input)
    assert resolved == {
        first.ref(): first_value,
        second.ref(): second_value,
    }
    assert matched == ((second_plan, second, second_value),)


@pytest.mark.parametrize(
    ("returned_output", "expected_count"),
    (("canonical", 0), (("canonical", "first", "second"), 2)),
)
def test_runtime_output_matcher_rejects_trailing_slot_count_mismatch(
    returned_output: object,
    expected_count: int,
) -> None:
    measurements = ArtifactSpec.output("Measurements", MeasurementsArtifactType)

    with pytest.raises(
        ValueError,
        match=rf"declared trailing output slots: {expected_count} != 1",
    ):
        _contract(measurements).resolve_returned_output(returned_output)


def test_runtime_output_matcher_rejects_duplicate_abi_specs() -> None:
    objects = ArtifactSpec.output("Objects", ObjectLabelsArtifactType)

    with pytest.raises(ValueError, match="duplicate artifact ref"):
        _contract(objects, objects).resolve_returned_output("objects")


def test_runtime_output_matcher_rejects_selected_plan_not_in_abi() -> None:
    declared = ArtifactSpec.output("Declared", ImageArtifactType)
    undeclared = ArtifactSpec.output("Undeclared", ImageArtifactType)
    undeclared_plan = ArtifactOutputPlan(
        name=undeclared.name,
        path="/memory/undeclared",
        artifact_type=undeclared.artifact_type,
    )

    with pytest.raises(ValueError, match="plan .* is not declared by the callable ABI"):
        _contract(declared).resolve_returned_plan_values("declared", (undeclared_plan,))


@pytest.mark.parametrize(
    "artifact_type",
    (ImageArtifactType, MeasurementsArtifactType),
)
def test_compiled_output_selection_accepts_exact_runtime_group_projection(
    artifact_type,
) -> None:
    output = ArtifactSpec.output("Output", artifact_type)
    compiled_plan = ArtifactOutputPlan(
        name=output.name,
        path="/memory/output",
        artifact_type=output.artifact_type,
        group_keys=("1", "2"),
        group_component=AllComponents.CHANNEL,
        paths_by_group={
            "1": "/memory/output/1",
            "2": "/memory/output/2",
        },
    )
    invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("process", "default", 0),
        contract=_contract(output),
        artifact_output_plans=(compiled_plan,),
    )
    runtime_plan = compiled_plan.for_group("1")

    assert invocation.select_outputs({runtime_plan.ref(): runtime_plan}) == {
        runtime_plan.ref(): runtime_plan
    }


def test_compiled_output_selection_rejects_same_ref_non_owner_projection() -> None:
    output = ArtifactSpec.output("Output", ImageArtifactType)
    compiled_plan = ArtifactOutputPlan(
        name=output.name,
        path="/memory/output",
        artifact_type=output.artifact_type,
        group_keys=("1", "2"),
        group_component=AllComponents.CHANNEL,
        paths_by_group={
            "1": "/memory/output/1",
            "2": "/memory/output/2",
        },
    )
    invocation = CompiledFunctionInvocation(
        key=FunctionInvocationKey("process", "default", 0),
        contract=_contract(output),
        artifact_output_plans=(compiled_plan,),
    )
    drifted_plan = ArtifactOutputPlan(
        name=output.name,
        path="/memory/wrong",
        artifact_type=output.artifact_type,
        group_keys=("1",),
        group_component=AllComponents.CHANNEL,
        paths_by_group={"1": "/memory/wrong"},
    )

    with pytest.raises(ValueError, match="differs from its compiled owner"):
        invocation.select_outputs({drifted_plan.ref(): drifted_plan})


def test_runtime_output_matcher_rejects_context_free_multi_canonical_stack() -> None:
    first = ArtifactSpec.output("First", ImageArtifactType)
    second = ArtifactSpec.output("Second", ImageArtifactType)

    with pytest.raises(ValueError, match="require exact AlignedImageStack"):
        _contract(first, second).resolve_returned_output(
            AlignedImageStack(("first", "second"))
        )


def test_plate_scope_uses_first_declared_output_as_canonical() -> None:
    measurements = ArtifactSpec.output("Measurements", MeasurementsArtifactType)
    image = ArtifactSpec.output("Image", ImageArtifactType)
    contract = _contract(
        measurements,
        image,
        execution_scope=FunctionStepExecutionScope.PLATE,
    )

    assert contract.canonical_return_output_specs.specs == (measurements,)
    assert contract.trailing_return_output_specs.specs == (image,)
    assert contract.resolve_returned_output(("measurements", "image")) == {
        measurements.ref(): "measurements",
        image.ref(): "image",
    }
