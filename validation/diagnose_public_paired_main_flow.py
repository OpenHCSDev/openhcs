"""Readonly declaration/return-ABI probe; never execute the engineering fixture."""

import importlib.util
import sys
from dataclasses import replace

import numpy as np

from openhcs.core.artifacts import ArtifactInputPlan, ArtifactOutputPlan, ArtifactSpecCollection, MeasurementsArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.component_group_scope import RuntimeExecutionAxisScope
from openhcs.core.function_patterns import DEFAULT_GROUP_KEY, FunctionInvocationKey
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.pipeline.artifact_planning import artifact_producers_for_outputs
from openhcs.core.runtime_output_matching import RuntimeReturnedOutputMatcher
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.interop.cellprofiler.runtime.adapter import CellProfilerRuntimeAdapter
from openhcs.interop.cellprofiler.runtime.module_execution import CellProfilerModuleExecutor
from openhcs.processing.backends.cellprofiler.classification import (
    ClassificationThresholdMethod, ClassifyObjectsSingleMeasurementModule,
    classify_objects_two_measurements,
)
from tests.unit.test_cellprofiler_conditional_analysis_images import _public_function_step_contract
from tests.unit.cellprofiler_runtime_test_support import cellprofiler_runtime_adapter_for_test

fixture_path = (
    "/home/ts/wt/openhcs-issue-batch-20260929/"
    "calibration371-classification372-installed-20261001/engineering_fixture.py"
)
spec = importlib.util.spec_from_file_location("original_paired_main_flow_probe", fixture_path)
fixture = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = fixture
spec.loader.exec_module(fixture)
original = CallableContract.from_callable(fixture.engineering_calibration_classification_fixture)
assert original.canonical_return_output_specs.names() == ("engineering_calibration_image",)
assert original.trailing_return_output_specs.names() == ("engineering_cells", "engineering_object_rows")
context = ArtifactDeclarationStepContext(
    step_name="engineering_pair_classification", step_index=1,
    available_artifacts=original.artifact_outputs,
    main_flow_artifacts=ArtifactSpecCollection(
        output.for_plan_type(ArtifactInputPlan)
        for output in original.canonical_return_output_specs
    ),
    available_artifact_producers=artifact_producers_for_outputs(
        original.artifact_outputs, groups=(None,),
        invocation_keys=(FunctionInvocationKey("engineering_fixture", DEFAULT_GROUP_KEY, 0),),
    ),
)
compiled = _public_function_step_contract(
    ClassifyObjectsSingleMeasurementModule, classify_objects_two_measurements,
    dict(select_the_object_to_be_classified="engineering_cells",
         measurement1_feature="pixel_count", measurement2_feature="calibration_um",
         threshold1_method=ClassificationThresholdMethod.CUSTOM, threshold1_value=100.0,
         threshold2_method=ClassificationThresholdMethod.CUSTOM, threshold2_value=2.0),
    context,
)
assert len(compiled.artifact_outputs) == 1
assert compiled.artifact_outputs[0].artifact_type is MeasurementsArtifactType
assert not compiled.canonical_return_output_specs
assert compiled.preserves_input_main_flow()
advanced = ClassifyObjectsSingleMeasurementModule.advance_artifact_context(
    context, contract=compiled,
    invocation_key=FunctionInvocationKey("engineering_pair_classification", DEFAULT_GROUP_KEY, 0),
)
assert advanced.main_flow_artifacts == context.main_flow_artifacts

# Probe the actual matcher, not a copied positional decoder or fixture body.
labels = np.zeros((64, 64), dtype=np.int32)
rows = fixture.DataclassMeasurementColumnarRows((), row_type=fixture.EngineeringObjectRow)
matcher = RuntimeReturnedOutputMatcher(compiled, (labels, rows))
assert matcher.canonical_output is labels
resolved = matcher.resolve()
assert tuple(resolved) == (compiled.artifact_outputs[0].ref(),)
assert resolved[compiled.artifact_outputs[0].ref()] is rows
row_spec = compiled.artifact_outputs[0]
row_plan = ArtifactOutputPlan(name=row_spec.name, path="/memory/paired_rows.pkl",
                              artifact_type=row_spec.artifact_type)
# The declaration helper stops before the provider's runtime-adapter injection.
# Request its original declaration, as compile_time_contracts.py:271 does.
compiled = replace(compiled, metadata=replace(
    compiled.metadata, runtime_adapter=CellProfilerRuntimeAdapter.runtime_adapter_spec(),
))
adapter = cellprofiler_runtime_adapter_for_test(
    runtime_value_store=RuntimeValueStore(), axis_scope=RuntimeExecutionAxisScope("A01_s001"),
    callable_contract=compiled, artifact_output_bindings=((row_spec, row_plan),),
)
executor = CellProfilerModuleExecutor(compiled.resolve_canonical_raw_callable(), compiled)
calibration = np.full((64, 64), 1.3556, dtype=np.float64)
_returned_values, matched = matcher.resolve_plan_values((row_plan,))
published = executor._published_active_main_flow_output(
    matched_outputs=matched, declared_only_outputs={}, adapter=adapter,
    current_image=calibration, invocation_image=labels, plane_projection=None,
)
assert published is calibration
print("ORIGINAL_FIXTURE_CANONICAL=engineering_calibration_image")
print("ORIGINAL_FIXTURE_AUXILIARY_LABELS=engineering_cells")
print("PAIRED_COMPILED_OUTPUTS=measurements_only")
print("RAW_FIRST_RETURN_IS_NOT_A_DECLARED_MAIN_FLOW_OUTPUT=True")
print("DECLARATION_GRAPH_PRESERVES_CALIBRATION_MAIN_FLOW=True")
print("ORIGINAL_ADAPTER_PUBLISHES_IDENTICAL_CALIBRATION_OBJECT=True")
print("NO_FIXTURE_EXECUTION_OR_NATIVE_PROCESS=True")
