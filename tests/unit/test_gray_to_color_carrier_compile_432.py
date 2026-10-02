"""#432: a created color carrier is not inherited from grayscale source files."""

from dataclasses import replace

import numpy as np
import pytest
import tifffile

from openhcs.core.callable_contract import CallableContract, PrimaryImageCarrierTransition
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.function_patterns import CompiledFunctionGroup, CompiledFunctionPattern
from openhcs.core.pipeline.compiler import PipelineCompiler
from openhcs.core.runtime_image_values import image_payload_data, image_payload_metadata
from openhcs.core.aligned_image_payload import ImagePayloadBundleContext, ImagePayloadExecutionMode
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.interop.cellprofiler.runtime.function_contract_execution import CellProfilerFunctionContractExecutor
from openhcs.processing.backends.cellprofiler.color import (
    ColorToGrayMode, ImageChannelType, color_to_gray, gray_to_color,
)
from test_gray_to_color_binding_axis_432 import _execute_bound_stack, _source_plane
from test_primary_image_carrier_compile_gate import _compiled_pattern, _session


def _gray_creator_session(tmp_path):
    path = tmp_path / "synthetic-gray.tif"
    tifffile.imwrite(path, np.zeros((4, 5), dtype=np.uint16))
    session = _session(tmp_path, (path,))
    producer = replace(
        session.plans[0], step_name="ComposeScalarRoles", step_scope_id="step-0",
        compiled_function_pattern=_compiled_pattern(gray_to_color),
    )
    consumer = CompiledStepPlan(
        step_index=1, step_name="SplitComposedRoles", step_type="FunctionStep", axis_id="A01",
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
    # Current RED matches the installed producer-step error, not a live replay.
    PipelineCompiler.validate_primary_image_carrier_requirements(_gray_creator_session(tmp_path))


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
    PipelineCompiler.validate_primary_image_carrier_requirements(session)


def test_preservation_annotation_cannot_create_missing_source_carrier(tmp_path):
    session = _gray_creator_session(tmp_path)
    producer = session.plans[0]
    (invocation,) = tuple(producer.compiled_function_pattern.iter_invocations())
    # A local counterexample only: do not mutate production callable/registry.
    falsely_preserving = replace(invocation, contract=replace(invocation.contract, metadata=replace(
        invocation.contract.metadata, primary_image_carrier_transition=PrimaryImageCarrierTransition.PRESERVE,
    )))
    session.plans[0] = replace(producer, compiled_function_pattern=CompiledFunctionPattern(
        groups=(CompiledFunctionGroup("default", (falsely_preserving,)),), is_grouped=False,
    ))
    session.context.step_plans = session.plans
    with pytest.raises(ValueError, match="requires a declared source channel axis"):
        PipelineCompiler.validate_primary_image_carrier_requirements(session)


def _runtime_scalar_role_split():
    raw = np.arange(20, dtype=np.float32).reshape(4, 5) * 1000 / 65535
    capped = np.clip((raw - 39 / 65535) / (5961 / 65535), 0, 1)
    bundle = ImagePayloadBundleContext.from_payloads(tuple(
        _source_plane(pixels, name)
        for pixels, name in ((raw, "RawBody"), (capped, "CappedOutgrowth"))
    )).compose()
    composite = _execute_bound_stack(bundle)
    assert image_payload_data(composite).shape == (4, 5, 2)
    assert image_payload_metadata(composite).source_channel_axis == -1
    contract = CallableContract.from_callable(color_to_gray)
    result = CellProfilerFunctionContractExecutor().execute(
        contract, contract.resolve_canonical_raw_callable(), composite,
        {"mode": ColorToGrayMode.SPLIT, "image_type": ImageChannelType.CHANNELS,
         "channel_indices": (0, 1), "contributions": (1.0, 1.0)},
        execution_mode=ImagePayloadExecutionMode.NATURAL,
    )
    return result, (raw, capped)


def test_original_runtime_split_preserves_both_role_values_and_physical_channel():
    result, expected_roles = _runtime_scalar_role_split()
    assert len(result.slices) == 2
    for output, expected in zip(result.slices, expected_roles, strict=True):
        assert image_payload_data(output).shape == (4, 5)
        np.testing.assert_array_equal(image_payload_data(output), expected)
        assert image_payload_metadata(output).source_component_metadata["channel"] == "2"
        assert set(image_payload_metadata(output).source_image_paths) == {"/synthetic/A01_s1_w2_z1_t1.tif"}


def test_scalar_role_outputs_consume_the_color_carrier():
    result, _expected_roles = _runtime_scalar_role_split()
    for output in result.slices:
        assert image_payload_data(output).shape == (4, 5)
        assert image_payload_metadata(output).source_channel_axis is None
