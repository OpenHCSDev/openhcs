from openhcs.core.pipeline.compilation_session import ResolvedPipelineDefinition
from dataclasses import dataclass, replace
from pathlib import Path
from types import SimpleNamespace

import pytest
import numpy as np

from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import (
    ArtifactMeasurementSubjectRelation,
    ArtifactInputPlan,
    ArtifactOutputPlan,
    ArtifactSidecarRole,
    ArtifactSpec,
    ArtifactSpecCollection,
    ArtifactSpecRelation,
    GroupLineageSourceRelation,
    ImageArtifactType,
    ImageMeasurementSubjectRelation,
    InputGroupLineageSourceRelation,
    InputStackBroadcastSourceRelation,
    ObjectLabelsArtifactType,
    ObjectMeasurementSubjectRelation,
    MeasurementsArtifactType,
    RelationshipsArtifactType,
    SpecialArtifactType,
)
from openhcs.core.compiled_step_plan import (
    CompiledStepPlan,
    MaterializedOutputPlan,
)
from openhcs.core.callable_contract import CallableContract, FunctionStepExecutionScope
from openhcs.core.component_set import ComponentSet
from openhcs.core.component_group_scope import (
    ComponentGroupScope,
    RuntimeExecutionAxisScope,
)
from openhcs.constants.constants import MEMORY_TYPE_NUMPY
from openhcs.core.memory import numpy
from openhcs.core.runtime_image_values import ImagePayloadMetadata, image_payload_data
from openhcs.core.runtime_plane_projection import RuntimePlaneProjection
from openhcs.core.runtime_stores import RuntimeValueStore
from openhcs.core.runtime_artifact_values import RuntimeValue
from openhcs.core.config import ProcessingConfig, StepMaterializationConfig
from openhcs.core.invocation_artifacts import (
    ArtifactDeclarationStepContext,
    CompositeInvocationContractProvider,
    InvocationContractPlan,
    InvocationContractProvider,
    unnamed_main_flow_artifact_name,
)
from openhcs.core.function_patterns import (
    DEFAULT_GROUP_KEY,
    CompiledMetadataArtifactInputEdgePlan,
    FunctionInvocationKey,
)
from openhcs.core.function_patterns import (
    CompiledFunctionGroup,
    CompiledFunctionInvocation,
    CompiledFunctionPattern,
    compile_function_pattern,
)
from openhcs.core.pipeline.artifact_planning import (
    ArtifactConsumer,
    ArtifactGraph,
    ArtifactProducer,
    extract_artifact_declarations,
)
from openhcs.core.pipeline.function_contracts import (
    artifact_inputs,
    artifact_outputs,
    execution_scope,
    runtime_bound_parameters,
    special_inputs,
)
from openhcs.core.pipeline.funcstep_contract_validator import FuncStepContractValidator
from openhcs.core.pipeline.path_planner import (
    ArtifactPlanMaps,
    MissingArtifactInputError,
    PathPlanner,
    PathPlannerComponentScopes,
    PathPlannerArtifactStage,
    PathPlannerExecutionGroups,
    PathPlannerGroupScope,
    PathPlannerMaterializationStage,
    PathPlannerPathAuthority,
    PathPlannerStepAssemblyStage,
    PathPlannerValidationStage,
)
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.artifact_key_selection import AdapterRecordedArtifactOutputPolicy
from openhcs.core.runtime_adapters import runtime_adapter
from openhcs.core.runtime_object_labels import ObjectLabelValue
from openhcs.core.runtime_stores import RuntimeArtifactBatch
from openhcs.core.source_bindings import (
    CompiledSourceBindingPlan,
    CompiledSourceUniversePlan,
    ComponentSelector,
    EMPTY_SOURCE_BINDINGS,
    NamedSourceBinding,
    SourceBindingOrigin,
    SourceBindingsConfig,
    SourceProjectionRole,
    StepSourceBindingsConfig,
)
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.core.step_dependencies import StepInputDependencyKind
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.steps.function_step import FunctionStep
from openhcs.core.steps.function_runtime import (
    PatternGroupExecutionScope,
    FunctionCoreExecutor,
    PatternGroupData,
)
from openhcs.core.dataset_sources.interfaces import MetadataArtifactProvider
from openhcs.core.dataset_sources.openhcs_format import OpenHCSMetadataHandler
from openhcs.processing.backends.analysis.metaxpress_utils import HiddenPixelSize
from openhcs.core.axes import Axis, GroupingDeclaration, Ungrouped
from openhcs.domains.microscopy.axes import Microscopy


def _execute_compiled_metadata_pattern(compiled, input_plans=None, stored_outputs=()):
    """Execute the original compiler result through the real callable runtime."""
    input_plans = {} if input_plans is None else input_plans
    plan = CompiledStepPlan(
        step_index=3,
        step_scope_id="plate::functionstep_3",
        step_name="metadata-consumer",
        axis_id="A01",
        input_memory_type=MEMORY_TYPE_NUMPY,
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        variable_components=(),
        execution_group_scope=ComponentGroupScope.ungrouped(),
        compiled_function_pattern=compiled,
        artifact_inputs=input_plans,
        artifact_outputs={},
    )
    context = SimpleNamespace(axis_id="A01", runtime_value_store=RuntimeValueStore())
    for producer, value in stored_outputs:
        context.runtime_value_store.record(
            RuntimeValue.from_output_plan(
                producer,
                value,
                execution_scope=RuntimeExecutionAxisScope(axis_id="A01"),
            ),
            path=producer.path,
            backend="memory",
        )
    scope = PatternGroupData(
        matching_files=["input.tif"],
        main_data_stack=np.zeros((1, 3, 4), dtype=np.uint16),
        context=context,
        execution_plan=plan,
        compiled_group=compiled.default_group,
        component_value=None,
        artifact_inputs=dict(plan.artifact_inputs),
        artifact_outputs=PatternGroupExecutionScope._select_output_plans_for_component(
            plan.artifact_outputs, plan.execution_group_scope, None
        ),
        runtime_plane_index=0,
        runtime_plane_count=1,
    )
    (invocation,) = compiled.default_group.invocations
    source = np.arange(6, dtype=np.uint16).reshape(1, 2, 3)
    result = FunctionCoreExecutor.from_group_invocation(
        scope,
        invocation,
        main_data_arg=ImagePayloadMetadata().payload_with(source),
        source_memory_type=MEMORY_TYPE_NUMPY,
        declared_source_bindings=scope.execution_plan.source_binding_plan,
    ).execute()
    np.testing.assert_array_equal(image_payload_data(result), source)
    return result


class _EngineeringMetadataHandler(OpenHCSMetadataHandler):
    def get_pixel_size(self, plate_path):
        return 1.3556

    def get_exposure_duration(self, plate_path):
        return 17.25


class _EngineeringExposureMetadataArtifactProvider(MetadataArtifactProvider):
    artifact_name = "engineering_exposure_duration"

    @classmethod
    def supports_handler(cls, handler):
        return isinstance(handler, _EngineeringMetadataHandler)

    def resolve(self, handler, plate_path):
        return handler.get_exposure_duration(plate_path)


def _prepare_step_declarations(planner, step, step_index):
    context = replace(
        planner.artifact_context, step_name=step.name, step_index=step_index,
    ).with_source_binding_scope(
        source_bindings=step.source_bindings,
        group_by=PathPlannerExecutionGroups.normalized_group_by(step),
        input_source=step.processing_config.input_source,
    )
    graph = extract_artifact_declarations(
        step.func, invocation_contract_provider=planner.invocation_contract_provider,
        step_context=context,
    )
    contracts = tuple(item.contract for item in graph.pattern.iter_items())
    return graph, graph.pattern, FunctionStepExecutionScope.require_uniform(contracts), contracts


def _compile_metadata_pattern(planner, pattern):
    snapshot = _resolved_step(func=pattern)
    declarations, pattern, _, _ = _prepare_step_declarations(planner,
        snapshot, 3
    )
    input_plans = planner.artifacts.process_artifact_inputs(
        declarations,
        3,
        PathPlannerGroupScope.ungrouped(),
        EMPTY_SOURCE_BINDINGS,
        ComponentSet(),
        snapshot.name,
        execution_scope=FunctionStepExecutionScope.AXIS,
    )
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        3,
        True,
        planner.artifacts.inject_metadata(pattern, declarations.inputs),
        input_plans,
        {},
        {},
        PathPlannerGroupScope.ungrouped(),
        declarations=declarations,
    )
    return compiled, input_plans


@dataclass(frozen=True)
class PathConfigStub:
    sub_dir: str
    output_dir_suffix: str = "_processed"
    global_output_folder: str | None = None


def _artifact_planner_stub() -> PathPlanner:
    planner = PathPlanner.__new__(PathPlanner)
    planner.plate_path = Path("/data/plate1")
    planner.cfg = PathConfigStub(sub_dir="images")
    planner.session = SimpleNamespace(
        global_config=SimpleNamespace(materialization_results_path="analysis"),
        realized_source_metadata=None,
        path_resolver=None,
    )
    planner.ctx = SimpleNamespace(
        axis_id="A01",
        microscope_handler=SimpleNamespace(
            can_resolve_metadata_artifact=lambda _artifact_name: False,
        ),
    )
    planner.orchestrator = SimpleNamespace(
        get_component_keys=lambda _component, *, resolved_config: (),
    )
    planner.plans = {
        2: CompiledStepPlan(
            step_index=2,
            step_scope_id="plate::functionstep_2",
            step_name="identify",
            axis_id="A01",
        ),
        3: CompiledStepPlan(
            step_index=3,
            step_scope_id="plate::functionstep_3",
            step_name="filter",
            axis_id="A01",
        ),
    }
    planner.declared = {}
    planner.future_artifact_inputs = [set() for _ in range(5)]
    planner.source_bindings_defaults = SourceBindingsConfig()
    planner.step_source_bindings_defaults = StepSourceBindingsConfig()
    planner.invocation_contract_provider = CompositeInvocationContractProvider(())
    planner.artifact_context = ArtifactDeclarationStepContext.empty()
    planner.main_flow_component_scopes = {}
    planner.execution_groups = PathPlannerExecutionGroups(planner)
    planner.paths = PathPlannerPathAuthority(planner)
    planner.artifacts = PathPlannerArtifactStage(planner)
    planner.materialization = PathPlannerMaterializationStage(planner)
    planner.validation = PathPlannerValidationStage(planner)
    planner.steps = PathPlannerStepAssemblyStage(planner)
    return planner


def _record_declared_output(
    planner: PathPlanner,
    plan: ArtifactOutputPlan,
) -> ArtifactOutputPlan:
    """Record one test producer under its exact graph identity."""

    planner.declared[plan.ref()] = plan
    return plan


class _NonFunctionStep(AbstractStep):
    def process(self, context, step_index: int) -> None:
        del context, step_index


def _resolved_step(
    *,
    name: str = "step",
    is_function_step: bool = True,
    func=None,
    source_bindings: StepSourceBindingsConfig = EMPTY_SOURCE_BINDINGS,
    group_by: type[GroupingDeclaration] = Microscopy.Channel,
    variable_components: tuple[type[Axis], ...] = (Microscopy.Site,),
    input_source: InputSource = InputSource.PREVIOUS_STEP,
    processing_config: ProcessingConfig | None = None,
    step_materialization_config=None,
) -> AbstractStep:
    if func is None:

        def passthrough(image):
            return image

        func = passthrough
    processing_config = processing_config or ProcessingConfig(
        group_by=group_by,
        variable_components=list(variable_components),
        input_source=input_source,
    )
    step_kwargs = dict(
        name=name,
        processing_config=processing_config,
        source_bindings=source_bindings,
        step_materialization_config=(
            step_materialization_config or StepMaterializationConfig()
        ),
    )
    step = (
        FunctionStep(func=func, **step_kwargs)
        if is_function_step
        else _NonFunctionStep(**step_kwargs)
    )
    return step


def test_metadata_satisfied_artifact_input_compiles_without_runtime_plan():
    received = []

    @numpy
    @artifact_inputs("grid_dimensions")
    def metadata_consumer(image, grid_dimensions):
        received.append(grid_dimensions)
        return image

    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = SimpleNamespace(
        can_resolve_metadata_artifact=lambda name: name == "grid_dimensions",
        resolve_metadata_artifact=lambda name, _plate_path: (
            (2, 3) if name == "grid_dimensions" else None
        ),
    )
    planner.ctx.plate_path = planner.plate_path
    pattern = (metadata_consumer, {"grid_dimensions": None})
    snapshot = _resolved_step(
        func=pattern,
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="DNA"),),
        ),
    )
    declarations, pattern, _, contracts = _prepare_step_declarations(planner,
        snapshot, 3
    )
    execution_bindings = CompiledSourceBindingPlan.from_contracts(
        snapshot.source_bindings,
        contracts,
        StepInputDependency.step_output(
            source_step_index=2,
            source_step_scope_id="plate::functionstep_2",
        ),
        planner.artifact_context.available_artifacts,
    )
    execution_group_scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
        source_bindings=execution_bindings,
        contracts=contracts,
    )
    runtime_input_plans = planner.artifacts.process_artifact_inputs(
        declarations,
        3,
        PathPlannerGroupScope.ungrouped(),
        execution_bindings,
        ComponentSet(),
        snapshot.name,
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        3,
        True,
        planner.artifacts.inject_metadata(pattern, declarations.inputs),
        runtime_input_plans,
        {},
        {},
        PathPlannerGroupScope.ungrouped(),
        declarations=declarations,
    )

    assert execution_bindings == CompiledSourceBindingPlan.empty()
    assert execution_group_scope == PathPlannerGroupScope.dynamic(Microscopy.Channel)
    assert runtime_input_plans == {}
    assert compiled is not None
    (invocation,) = compiled.default_group.invocations
    assert invocation.kwargs_dict["grid_dimensions"] == (2, 3)
    (edge,) = invocation.artifact_input_edges
    assert edge.spec == invocation.contract.artifact_inputs[0]
    assert edge.spec.parameter_name == "grid_dimensions"
    assert edge.storage_plan is None
    assert edge.projection is None
    _execute_compiled_metadata_pattern(compiled)
    assert received == [(2, 3)]


@pytest.mark.parametrize(
    "artifact_name, expected",
    [("pixel_size", 1.3556), ("engineering_exposure_duration", 17.25)],
)
def test_registered_metadata_provider_value_reaches_runtime_unchanged(artifact_name, expected):
    received = []
    spec = ArtifactSpec.input(artifact_name, SpecialArtifactType, parameter_name="calibration")

    @numpy
    @artifact_inputs(spec)
    def metadata_consumer(image, *, calibration):
        received.append(calibration)
        return image

    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = _EngineeringMetadataHandler(filemanager=object())
    planner.ctx.plate_path = planner.plate_path
    assert planner.ctx.microscope_handler.can_resolve_metadata_artifact(artifact_name)
    compiled, input_plans = _compile_metadata_pattern(planner, (metadata_consumer, {"calibration": -7.0}))
    (invocation,) = compiled.default_group.invocations
    (edge,) = invocation.artifact_input_edges
    assert isinstance(edge, CompiledMetadataArtifactInputEdgePlan)
    assert input_plans == {}
    assert invocation.kwargs_dict == {"calibration": expected}
    assert all(binding.parameter_name != "calibration" for binding in invocation.runtime_parameter_bindings)
    _execute_compiled_metadata_pattern(compiled)
    assert received == [expected]


def test_new_metadata_provider_composes_cooperative_capabilities_through_runtime():
    events = []
    received = []

    class PositiveMetadataValue:
        def resolve(self, handler, plate_path):
            value = super().resolve(handler, plate_path)
            events.append(("validate", value))
            if value <= 0:
                raise ValueError("Exposure duration must be positive")
            return value

    class ResolutionReceipt:
        def resolve(self, handler, plate_path):
            events.append("resolve")
            value = super().resolve(handler, plate_path)
            events.append(("resolved", value))
            return value

    class CheckedExposureMetadataProvider(
        ResolutionReceipt, PositiveMetadataValue,
        _EngineeringExposureMetadataArtifactProvider,
    ):
        artifact_name = "engineering_checked_exposure_duration"

    @numpy
    @artifact_inputs(CheckedExposureMetadataProvider.require_artifact_name())
    def metadata_consumer(image, engineering_checked_exposure_duration):
        received.append(engineering_checked_exposure_duration)
        return image

    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = _EngineeringMetadataHandler(filemanager=object())
    planner.ctx.plate_path = planner.plate_path
    assert planner.ctx.microscope_handler.can_resolve_metadata_artifact(
        CheckedExposureMetadataProvider.require_artifact_name()
    )
    compiled, _ = _compile_metadata_pattern(planner, metadata_consumer)
    _execute_compiled_metadata_pattern(compiled)
    assert received == [17.25]
    assert events == ["resolve", ("validate", 17.25), ("resolved", 17.25)]

    class InvalidExposureHandler(_EngineeringMetadataHandler):
        def get_exposure_duration(self, plate_path):
            return -17.25

    events.clear()
    planner.ctx.microscope_handler = InvalidExposureHandler(filemanager=object())
    with pytest.raises(ValueError, match="Exposure duration must be positive"):
        _compile_metadata_pattern(planner, metadata_consumer)
    assert events == ["resolve", ("validate", -17.25)]
    assert received == [17.25]


def test_hidden_pixel_size_reaches_callable_with_exact_source_calibration():
    received = []

    @numpy
    @artifact_inputs("pixel_size")
    def metadata_consumer(image, pixel_size: HiddenPixelSize = HiddenPixelSize(1.0)):
        received.append(pixel_size)
        return image

    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = _EngineeringMetadataHandler(filemanager=object())
    planner.ctx.plate_path = planner.plate_path
    compiled, _ = _compile_metadata_pattern(planner, metadata_consumer)
    _execute_compiled_metadata_pattern(compiled)
    assert received == [1.3556]
    assert received != [1.0]


@pytest.mark.parametrize("value", [None, 0.0, False])
def test_required_metadata_input_has_no_magic_default(value):
    @numpy
    @artifact_inputs("pixel_size")
    def metadata_consumer(image, pixel_size):
        assert pixel_size is value
        return image

    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = SimpleNamespace(
        can_resolve_metadata_artifact=lambda name: name == "pixel_size",
        resolve_metadata_artifact=lambda name, plate_path: value,
    )
    planner.ctx.plate_path = planner.plate_path
    compiled, _ = _compile_metadata_pattern(planner, metadata_consumer)
    if value is None:
        with pytest.raises(ValueError, match="Required metadata artifact .* has no value"):
            _execute_compiled_metadata_pattern(compiled)
    else:
        _execute_compiled_metadata_pattern(compiled)


def test_authored_kwarg_does_not_satisfy_an_unknown_artifact_origin():
    @numpy
    @artifact_inputs("unknown_metadata")
    def metadata_consumer(image, unknown_metadata):
        return image

    planner = _artifact_planner_stub()
    with pytest.raises(MissingArtifactInputError):
        _compile_metadata_pattern(planner, (metadata_consumer, {"unknown_metadata": 1.3556}))


def test_exact_producer_takes_precedence_over_metadata_provider():
    @numpy
    @artifact_inputs("pixel_size")
    def metadata_consumer(image, pixel_size):
        assert pixel_size == 2.125
        return image

    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = _EngineeringMetadataHandler(filemanager=object())
    planner.ctx.plate_path = planner.plate_path
    producer = _record_declared_output(planner, ArtifactOutputPlan(
        name="pixel_size", path="/memory/pixel_size.pkl",
        artifact_type=SpecialArtifactType, producer_step_index=2,
        producer_step_scope_id="plate::functionstep_2",
    ))
    compiled, input_plans = _compile_metadata_pattern(planner, metadata_consumer)
    (invocation,) = compiled.default_group.invocations
    (edge,) = invocation.artifact_input_edges
    assert not isinstance(edge, CompiledMetadataArtifactInputEdgePlan)
    assert edge.storage_plan.source_step_scope_id == producer.producer_step_scope_id
    assert invocation.kwargs_dict == {}
    _execute_compiled_metadata_pattern(compiled, input_plans, ((producer, 2.125),))


def test_plate_artifact_consumer_omits_inherited_source_plans():
    source_image = ArtifactSpec.input("DNA", ImageArtifactType)
    measurements = ArtifactSpec.input("Measurements", MeasurementsArtifactType)
    export_bundle = ArtifactSpec.output("ExportBundle", SpecialArtifactType)

    @execution_scope(FunctionStepExecutionScope.PLATE)
    @runtime_bound_parameters(RuntimeArtifactBatch)
    @artifact_inputs(source_image, measurements)
    @artifact_outputs(export_bundle)
    def export_measurements(*, artifact_batch: RuntimeArtifactBatch):
        del artifact_batch
        return {"Measurements.csv": b""}

    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=measurements.name,
            path="/memory/Measurements.pkl",
            artifact_type=MeasurementsArtifactType,
            producer_step_index=2,
            producer_step_scope_id="plate::functionstep_2",
            producer_step_name="Measure",
        ),
    )
    planner.artifact_context = replace(
        planner.artifact_context,
        available_artifacts=ArtifactSpecCollection((measurements,)),
    )
    snapshot = _resolved_step(
        func=export_measurements,
        name="PlateExporter",
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="DNA"),),
        ),
        group_by=Ungrouped,
        variable_components=(),
        input_source=InputSource.PIPELINE_START,
    )
    (
        declarations,
        pattern,
        callable_scope,
        contracts,
    ) = _prepare_step_declarations(planner, snapshot, 3)
    execution_bindings = CompiledSourceBindingPlan.from_contracts(
        snapshot.source_bindings,
        contracts,
        StepInputDependency.no_main_flow(),
        planner.artifact_context.available_artifacts,
    )
    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        3,
        declarations,
        PathPlannerGroupScope.ungrouped(),
        callable_scope,
        execution_bindings,
    )
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        3,
        True,
        pattern,
        maps.inputs,
        maps.outputs,
        maps.relation_source_scopes,
        maps.group_scope,
        declarations=declarations,
    )
    plan = planner.plans[3]
    plan.step_name = snapshot.name
    plan.main_input_dependency = StepInputDependency.no_main_flow()
    plan.artifact_inputs = maps.inputs
    plan.artifact_outputs = maps.outputs
    plan.compiled_function_pattern = compiled
    plan.source_binding_plan = maps.source_binding_plan
    plan.source_universe_plan = maps.source_universe_plan

    FuncStepContractValidator.validate_compiled_step_plan(plan)

    assert callable_scope is FunctionStepExecutionScope.PLATE
    assert tuple(contracts[0].artifact_inputs) == (source_image, measurements)
    assert tuple(contracts[0].artifact_outputs) == (export_bundle,)
    assert execution_bindings.declares_artifact_ref(source_image.ref())
    assert maps.source_binding_plan.declares_artifact_ref(source_image.ref())
    assert (
        maps.source_universe_plan
        == CompiledSourceUniversePlan.from_source_binding_plan(maps.source_binding_plan)
    )
    assert tuple(maps.inputs) == (measurements.ref(),)
    assert maps.inputs[measurements.ref()].source_step_id == 2
    invocation = next(compiled.iter_invocations())
    assert tuple(edge.spec for edge in invocation.artifact_input_edges) == (
        source_image,
        measurements,
    )
    assert tuple(
        edge.spec
        for edge in invocation.artifact_input_edges
        if edge.storage_plan is not None
    ) == (measurements,)
    assert (
        invocation.artifact_input_edges[1].storage_plan
        is maps.inputs[measurements.ref()]
    )


def test_plate_artifact_output_plan_is_independent_of_axis_context():
    export_bundle = ArtifactSpec.output("ExportBundle", SpecialArtifactType)

    @execution_scope(FunctionStepExecutionScope.PLATE)
    @runtime_bound_parameters(RuntimeArtifactBatch)
    @artifact_outputs(export_bundle)
    def export_measurements(*, artifact_batch: RuntimeArtifactBatch):
        del artifact_batch
        return {"Measurements.csv": b""}

    declarations = extract_artifact_declarations(export_measurements)
    compiled_by_axis = {}
    for axis_id in ("A01", "B01"):
        planner = _artifact_planner_stub()
        planner.ctx.axis_id = axis_id
        output_plans = planner.artifacts.process_artifact_outputs(
            declarations,
            3,
            execution_scope=FunctionStepExecutionScope.PLATE,
            artifact_inputs={},
            source_bindings=EMPTY_SOURCE_BINDINGS,
            variable_components=ComponentSet(),
            step_name="PlateExporter",
        )
        compiled_by_axis[axis_id] = compile_function_pattern(
            export_measurements,
            {},
            output_plans,
        ).default_group.invocations[0]

    assert compiled_by_axis["A01"] == compiled_by_axis["B01"]
    (output_plan,) = compiled_by_axis["A01"].artifact_output_plans
    assert Path(output_plan.path).name == "ExportBundle_step3.pkl"

    axis_planner = _artifact_planner_stub()
    (axis_output_plan,) = axis_planner.artifacts.process_artifact_outputs(
        declarations,
        3,
        execution_scope=FunctionStepExecutionScope.AXIS,
        artifact_inputs={},
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet(),
        step_name="AxisExporter",
    ).values()
    assert Path(axis_output_plan.path).name == "A01_ExportBundle_step3.pkl"


def test_compiled_pattern_rejects_accumulator_owned_output_conflict():
    def identify():
        return None

    crop_mask_measurements = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        sidecar_role=ArtifactSidecarRole.CROP_MASK,
        relations=(ArtifactMeasurementSubjectRelation(),),
    )
    image_copy_measurements = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        sidecar_role=ArtifactSidecarRole.MATERIALIZED_IMAGE_COPY,
        relations=(ArtifactMeasurementSubjectRelation(),),
    )
    base_contract = CallableContract.from_callable(identify)
    contracts = tuple(
        replace(
            base_contract,
            metadata=replace(
                base_contract.metadata,
                artifact_outputs=(output,),
            ),
        )
        for output in (crop_mask_measurements, image_copy_measurements)
    )

    class RepeatedOutputContractProvider(InvocationContractProvider):
        def __call__(self, invocation, step_context):
            del step_context
            return InvocationContractPlan(contracts[invocation.key.position])

    planner = _artifact_planner_stub()
    planner.invocation_contract_provider = RepeatedOutputContractProvider()
    output_plan = ArtifactOutputPlan(
        name=crop_mask_measurements.name,
        path=f"/memory/{crop_mask_measurements.name}.pkl",
        artifact_type=crop_mask_measurements.artifact_type,
    )
    output_plans = {output_plan.ref(): output_plan}
    pattern = [identify, identify]

    with pytest.raises(
        ValueError,
        match="Conflicting compiled invocation output artifact sidecar role",
    ):
        compile_function_pattern(
            pattern, {}, output_plans,
            invocation_contract_provider=planner.invocation_contract_provider,
        ).coalesced_artifact_output_specs()



def test_materialization_collision_updates_results_dir_and_config():
    planner = PathPlanner.__new__(PathPlanner)
    planner.plate_path = Path("/data/plate1")
    planner.plans = {
        3: CompiledStepPlan(
            step_index=3,
            step_name="materialize",
            axis_id="A01",
            materialized_output=MaterializedOutputPlan(
                output_dir=Path("/data/plate1_processed/images"),
                backend="disk",
                plate_root="/data/plate1_processed",
                sub_dir="images",
                analysis_results_dir="/data/plate1_processed/images_results",
            ),
            materialization_config=PathConfigStub(sub_dir="images"),
        )
    }
    snapshot = _resolved_step(
        name="materialize", step_materialization_config=PathConfigStub(sub_dir="images")
    )

    planner.paths = PathPlannerPathAuthority(planner)
    planner.validation = PathPlannerValidationStage(planner)

    planner.validation.resolve_and_update_paths(
        snapshot,
        3,
        Path("/data/plate1_processed/images"),
        "main flow",
    )

    assert snapshot.step_materialization_config.sub_dir == "images"
    materialized_output = planner.plans[3].materialized_output
    assert materialized_output.output_dir == Path("/data/plate1_processed/images_step3")
    assert materialized_output.sub_dir == "images_step3"
    assert materialized_output.analysis_results_dir == (
        "/data/plate1_processed/images_step3_results"
    )
    assert planner.plans[3].materialization_config.sub_dir == "images_step3"


def test_artifact_output_plans_preserve_declared_kind():
    planner = _artifact_planner_stub()
    output = ArtifactSpec.output("nuclei", ObjectLabelsArtifactType)

    outputs = planner.artifacts.process_artifact_outputs(
        ArtifactGraph(
            producers=(
                ArtifactProducer(
                    spec=output,
                    groups=(None,),
                    invocation_keys=(
                        FunctionInvocationKey("identify", DEFAULT_GROUP_KEY, 0),
                    ),
                ),
            )
        ),
        sid=2,
        output_groups={output.ref(): PathPlannerGroupScope.ungrouped()},
        artifact_inputs={},
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet(),
        step_name="identify",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert outputs[output.ref()].artifact_type is ObjectLabelsArtifactType
    assert planner.declared[outputs[output.ref()].ref()].artifact_type is (
        ObjectLabelsArtifactType
    )


def test_same_name_typed_artifacts_compile_through_producer_and_consumer_plans():
    planner = _artifact_planner_stub()
    image_output = ArtifactSpec.output("shared", ImageArtifactType)
    labels_output = ArtifactSpec.output("shared", ObjectLabelsArtifactType)

    @artifact_outputs(image_output, labels_output)
    def produce_shared():
        return None

    producer_snapshot = _resolved_step(
        name="produce_shared",
        func=produce_shared,
        group_by=Ungrouped,
        variable_components=(),
        input_source=InputSource.PIPELINE_START,
    )
    (
        producer_declarations,
        producer_pattern,
        producer_scope,
        _producer_contracts,
    ) = _prepare_step_declarations(planner, producer_snapshot, 2)
    producer_maps = planner.artifacts.compile_plan_maps(
        producer_snapshot,
        2,
        producer_declarations,
        PathPlannerGroupScope.ungrouped(),
        producer_scope,
        EMPTY_SOURCE_BINDINGS,
    )
    producer_compiled = planner.artifacts.build_step_compiled_function_pattern(
        producer_snapshot,
        2,
        True,
        producer_pattern,
        producer_maps.inputs,
        producer_maps.outputs,
        producer_maps.relation_source_scopes,
        producer_maps.group_scope,
        declarations=producer_declarations,
    )

    assert tuple(producer_maps.outputs) == (
        image_output.ref(),
        labels_output.ref(),
    )
    producer_paths = {ref: plan.path for ref, plan in producer_maps.outputs.items()}
    assert Path(producer_paths[image_output.ref()]).name == (
        "A01_shared__image_step2.pkl"
    )
    assert Path(producer_paths[labels_output.ref()]).name == (
        "A01_shared__object_labels_step2.pkl"
    )
    assert len(set(producer_paths.values())) == 2
    assert tuple(
        plan.ref()
        for plan in next(producer_compiled.iter_invocations()).artifact_output_plans
    ) == (image_output.ref(), labels_output.ref())

    image_input = ArtifactSpec.input(
        "shared",
        ImageArtifactType,
        parameter_name="shared_image",
    )
    labels_input = ArtifactSpec.input(
        "shared",
        ObjectLabelsArtifactType,
        parameter_name="shared_labels",
    )

    @artifact_inputs(image_input, labels_input)
    def consume_shared(image, shared_image, shared_labels):
        del shared_image, shared_labels
        return image

    consumer_snapshot = _resolved_step(
        name="consume_shared",
        func=consume_shared,
        group_by=Ungrouped,
        variable_components=(),
    )
    (
        consumer_declarations,
        consumer_pattern,
        consumer_scope,
        _consumer_contracts,
    ) = _prepare_step_declarations(planner, consumer_snapshot, 3)
    consumer_maps = planner.artifacts.compile_plan_maps(
        consumer_snapshot,
        3,
        consumer_declarations,
        PathPlannerGroupScope.ungrouped(),
        consumer_scope,
        EMPTY_SOURCE_BINDINGS,
    )
    consumer_compiled = planner.artifacts.build_step_compiled_function_pattern(
        consumer_snapshot,
        3,
        True,
        consumer_pattern,
        consumer_maps.inputs,
        consumer_maps.outputs,
        consumer_maps.relation_source_scopes,
        consumer_maps.group_scope,
        declarations=consumer_declarations,
    )

    assert tuple(consumer_maps.inputs) == (image_input.ref(), labels_input.ref())
    assert {
        input_ref.for_plan_type(ArtifactOutputPlan): input_plan.path
        for input_ref, input_plan in consumer_maps.inputs.items()
    } == producer_paths
    consumer_edges = next(consumer_compiled.iter_invocations()).artifact_input_edges
    assert tuple(edge.spec.ref() for edge in consumer_edges) == (
        image_input.ref(),
        labels_input.ref(),
    )
    assert tuple(edge.storage_plan.path for edge in consumer_edges) == tuple(
        producer_paths[output_ref]
        for output_ref in (image_output.ref(), labels_output.ref())
    )


def test_derived_artifact_storage_keys_reject_declared_name_collision():
    outputs = (
        ArtifactSpec.output("shared", ImageArtifactType),
        ArtifactSpec.output("shared", ObjectLabelsArtifactType),
        ArtifactSpec.output("shared__image", SpecialArtifactType),
    )
    declarations = ArtifactGraph(
        producers=tuple(
            ArtifactProducer(
                spec=spec,
                groups=(None,),
                invocation_keys=(),
            )
            for spec in outputs
        )
    )

    with pytest.raises(ValueError, match="conflicting storage keys"):
        declarations.output_storage_keys()


def test_artifact_output_plan_only_preserves_explicit_source_stack_scope():
    planner = _artifact_planner_stub()
    source = ArtifactSpec.input("source", ImageArtifactType)
    output_specs = (
        ArtifactSpec.output_inheriting_group_scope(
            "group_lineage",
            ImageArtifactType,
            source,
        ),
        ArtifactSpec.output_preserving_source_stack_scope(
            "stack_lineage",
            ImageArtifactType,
            source,
        ),
    )

    outputs = planner.artifacts.process_artifact_outputs(
        ArtifactGraph(
            producers=tuple(
                ArtifactProducer(
                    spec=spec,
                    groups=(None,),
                    invocation_keys=(
                        FunctionInvocationKey("transform", DEFAULT_GROUP_KEY, 0),
                    ),
                )
                for spec in output_specs
            ),
            consumers=(
                ArtifactConsumer(
                    spec=source,
                    invocation_keys=(
                        FunctionInvocationKey("transform", DEFAULT_GROUP_KEY, 0),
                    ),
                ),
            ),
        ),
        sid=2,
        artifact_inputs={
            source.ref(): ArtifactInputPlan(
                name=source.name,
                path="/memory/source.pkl",
                artifact_type=source.artifact_type,
                variable_components=(Microscopy.Channel,),
            )
        },
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet((Microscopy.Channel,)),
        step_name="transform",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert outputs[output_specs[0].ref()].variable_components == ()
    assert outputs[output_specs[1].ref()].variable_components == (
        Microscopy.Channel,
    )


def test_artifact_output_source_lookup_combines_repeated_main_flow_inputs():
    planner = _artifact_planner_stub()
    source = ArtifactSpec.input("MembFinal", ImageArtifactType)
    output = ArtifactSpec.output_preserving_source_stack_scope(
        "Cells",
        ObjectLabelsArtifactType,
        source,
    )
    invocation_key = FunctionInvocationKey("watershed", DEFAULT_GROUP_KEY, 0)
    repeated_source = ArtifactConsumer(
        spec=source,
        invocation_keys=(invocation_key,),
    )
    planner.artifact_context = ArtifactDeclarationStepContext(
        available_artifacts=ArtifactSpecCollection((source,)),
        main_flow_artifacts=ArtifactSpecCollection((source,)),
    )

    outputs = planner.artifacts.process_artifact_outputs(
        ArtifactGraph(
            producers=(
                ArtifactProducer(
                    spec=output,
                    groups=(None,),
                    invocation_keys=(invocation_key,),
                ),
            ),
            non_plan_consumers=(repeated_source, repeated_source),
        ),
        sid=2,
        artifact_inputs={},
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet((Microscopy.ZIndex,)),
        step_name="watershed",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert outputs[output.ref()].variable_components == (Microscopy.ZIndex,)


@pytest.mark.parametrize("stored_main_flow", [False, True])
@pytest.mark.parametrize("stored_secondary", [False, True])
def test_compiled_source_edges_only_consume_relation_owned_main_flow(
    stored_main_flow, stored_secondary,
):
    source_specs = (
        ArtifactSpec.input("DNA", ImageArtifactType),
        ArtifactSpec.input("Membrane", ImageArtifactType, parameter_name="secondary"),
        ArtifactSpec.input("Mitochondria", ImageArtifactType),
    )
    output_spec = ArtifactSpec.output_preserving_source_stack_scope(
        "Combined",
        ImageArtifactType,
        source_specs[0],
    )
    output_plan = ArtifactOutputPlan(
        name=output_spec.name,
        path="/memory/Combined.pkl",
        artifact_type=output_spec.artifact_type,
        relations=output_spec.relations,
    )

    @artifact_inputs(*source_specs)
    @artifact_outputs(output_spec)
    def combine_sources(image, secondary=None):
        return image

    compiled = compile_function_pattern(
        combine_sources,
        {},
        {plan.ref(): plan for plan in (output_plan,)},
    )
    stored_inputs = {
        spec.ref(): ArtifactInputPlan(
            name=spec.name,
            path=f"/memory/previous-step/{spec.name}.pkl",
            artifact_type=ImageArtifactType,
            source_step_id=0,
        )
        for spec, stored in zip(source_specs[:2], (stored_main_flow, stored_secondary))
        if stored
    }
    compiled = _artifact_planner_stub().artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs=stored_inputs,
        relation_source_scopes={},
        execution_group_scope=PathPlannerGroupScope.ungrouped(),
        consumer_variable_components=ComponentSet((Microscopy.ZIndex,)),
        main_flow_artifacts=ArtifactSpecCollection(source_specs),
    )

    edges = next(compiled.iter_invocations()).artifact_input_edges
    assert tuple(edge.spec for edge in edges) == source_specs
    assert tuple((edge.main_flow_projection is not None) for edge in edges) == (True, False, False)
    assert edges[0].storage_plan is None
    assert edges[0].projection is None
    assert edges[1].storage_plan is stored_inputs.get(source_specs[1].ref())
    assert (edges[1].projection is not None) is stored_secondary
    assert edges[1].spec.parameter_name == "secondary"


def test_implicit_native_main_flow_provenance_drives_artifact_owned_scope():
    from openhcs.core.config import (
        GlobalPipelineConfig,
        LazyProcessingConfig,
        PipelineConfig,
    )
    from openhcs.core.context.processing_context import ProcessingContext
    from openhcs.core.function_patterns import normalize_function_pattern
    from openhcs.core.pipeline.compilation_session import CompilationSession
    from openhcs.interop.cellprofiler.compile_time_contracts import (
        CellProfilerInvocationContractProviderFactory,
    )
    from openhcs.processing.backends.cellprofiler.thresholding import threshold
    from openhcs.processing.backends.processors.numpy_processor import (
        percentile_normalize,
    )

    processing_config = LazyProcessingConfig(
        variable_components=[Microscopy.Site],
        group_by=Microscopy.Channel,
        input_source=InputSource.PREVIOUS_STEP,
    )
    steps = (
        FunctionStep(
            func=percentile_normalize,
            name="percentile_normalize",
            processing_config=processing_config,
        ),
        FunctionStep(
            func=(threshold, {"name_the_output_image": "Thresholded"}),
            name="Threshold",
            processing_config=processing_config,
        ),
    )
    session = CompilationSession.from_context(
        context=ProcessingContext(
            step_plans={
                index: CompiledStepPlan(
                    step_index=index,
                    step_name=step.name,
                    axis_id="A01",
                )
                for index, step in enumerate(steps)
            },
            axis_id="A01",
        ),
        orchestrator=SimpleNamespace(pipeline_config=PipelineConfig()),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=steps,
            step_scope_ids={
                index: f"plate::step_{index}" for index in range(len(steps))
            },
            step_provenance={index: {} for index in range(len(steps))},
        ),
    )
    provider = CellProfilerInvocationContractProviderFactory.provider_for_pipeline(
        session.pipeline
    )
    assert provider is not None

    planner = _artifact_planner_stub()
    planner.artifact_context = ArtifactDeclarationStepContext(
        step_name="percentile_normalize",
        step_index=0,
    )
    channel_scope = PathPlannerGroupScope.from_raw(
        ("1", "2", "4"),
        component=Microscopy.Channel,
    )
    planner.plans[0] = CompiledStepPlan(
        step_index=0,
        step_name="percentile_normalize",
        axis_id="A01",
        execution_group_scope=channel_scope,
    )
    native_pattern = compile_function_pattern(percentile_normalize, {}, {})
    native_invocation = next(native_pattern.iter_invocations())
    planner.artifact_context = (
        extract_artifact_declarations(percentile_normalize).advance_declaration_context(
            planner.artifact_context,
        )
    )
    cursor_name = unnamed_main_flow_artifact_name(0, native_invocation.key)
    cursor = ArtifactSpec.input(cursor_name, ImageArtifactType)
    consumer_context = replace(
        planner.artifact_context,
        step_name=steps[1].name,
        step_index=1,
        group_by=Microscopy.Channel,
        input_source=InputSource.PREVIOUS_STEP,
    )
    planner.artifact_context = consumer_context
    consumer_invocation = next(normalize_function_pattern(steps[1].func).iter_items())
    consumer_plan = provider(consumer_invocation, consumer_context)
    assert consumer_plan is not None
    consumer_contract = consumer_plan.contract
    assert consumer_contract.artifact_inputs.names() == (cursor_name,)
    assert consumer_contract.group_scope_inputs.names() == (cursor_name,)
    consumer_graph = extract_artifact_declarations(
        steps[1].func,
        invocation_contract_provider=provider,
        step_context=consumer_context,
    )

    assert planner.artifact_context.main_flow_artifacts == ArtifactSpecCollection(
        (cursor,)
    )
    assert planner.artifact_context.available_artifact_producer_for(cursor) == (
        ArtifactProducer(
            spec=cursor.for_plan_type(ArtifactOutputPlan),
            groups=(None,),
            invocation_keys=(native_invocation.key,),
            producer_step_index=0,
        )
    )
    assert planner.declared == {}

    execution_scope = planner.execution_groups.get_execution_groups(
        steps[1],
        PathPlannerComponentScopes.empty(),
        contracts=(consumer_contract,),
    )
    assert execution_scope == channel_scope

    compiled_inputs = planner.artifacts.process_artifact_inputs(
        consumer_graph,
        sid=1,
        consumer_scope=execution_scope,
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet((Microscopy.Site,)),
        step_name="Threshold",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )
    assert compiled_inputs == {}

    compiled_consumer = compile_function_pattern(
        steps[1].func,
        {},
        {},
        invocation_contract_provider=provider,
        step_context=consumer_context,
    )
    compiled_consumer = planner.artifacts.compile_invocation_input_edges(
        compiled_consumer,
        artifact_inputs=compiled_inputs,
        relation_source_scopes={},
        execution_group_scope=execution_scope,
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
        main_flow_artifacts=planner.artifact_context.main_flow_artifacts,
    )
    edge = next(compiled_consumer.iter_invocations()).artifact_input_edges[0]
    assert edge.spec == cursor
    assert edge.storage_plan is None
    assert edge.main_flow_projection is not None


def test_artifact_output_source_uses_compiled_plan_across_parameter_occurrences():
    planner = _artifact_planner_stub()
    measured = ArtifactSpec.input(
        "Cells",
        ObjectLabelsArtifactType,
        parameter_name="labels",
    )
    neighbors = replace(measured, parameter_name="neighbor_labels")
    output = ArtifactSpec.output_preserving_source_stack_scope(
        "Neighbors",
        RelationshipsArtifactType,
        measured,
    )
    invocation_key = FunctionInvocationKey(
        "measure_object_neighbors",
        DEFAULT_GROUP_KEY,
        0,
    )

    outputs = planner.artifacts.process_artifact_outputs(
        ArtifactGraph(
            producers=(
                ArtifactProducer(
                    spec=output,
                    groups=(None,),
                    invocation_keys=(invocation_key,),
                ),
            ),
            consumers=(
                ArtifactConsumer(measured, (invocation_key,)),
                ArtifactConsumer(neighbors, (invocation_key,)),
            ),
        ),
        sid=2,
        artifact_inputs={
            measured.ref(): ArtifactInputPlan(
                name=measured.name,
                path="/memory/Cells.pkl",
                artifact_type=measured.artifact_type,
                variable_components=(Microscopy.ZIndex,),
            )
        },
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet((Microscopy.ZIndex,)),
        step_name="MeasureObjectNeighbors",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert outputs[output.ref()].variable_components == (Microscopy.ZIndex,)
    assert outputs[output.ref()].relations == output.relations


def test_artifact_output_source_lookup_ignores_shared_input_broadcast_projections():
    planner = _artifact_planner_stub()
    green = ArtifactSpec.input("OrigGreen", ImageArtifactType)
    red = ArtifactSpec.input("OrigRed", ImageArtifactType)
    mask_name = ArtifactSidecarRole.CROP_MASK.name_for("CropBlue")
    green_mask = ArtifactSpec.input(
        mask_name,
        ImageArtifactType,
        sidecar_role=ArtifactSidecarRole.CROP_MASK,
        relations=(InputStackBroadcastSourceRelation(source=green.ref()),),
    )
    red_mask = replace(
        green_mask,
        relations=(InputStackBroadcastSourceRelation(source=red.ref()),),
    )
    green_output = ArtifactSpec.output_preserving_source_stack_scope(
        "CropGreen",
        ImageArtifactType,
        green,
    )
    red_output = ArtifactSpec.output_preserving_source_stack_scope(
        "CropRed",
        ImageArtifactType,
        red,
    )
    green_key = FunctionInvocationKey("crop", "2", 0)
    red_key = FunctionInvocationKey("crop", "3", 0)
    consumers = (
        ArtifactConsumer(green, (green_key,)),
        ArtifactConsumer(green_mask, (green_key,)),
        ArtifactConsumer(red, (red_key,)),
        ArtifactConsumer(red_mask, (red_key,)),
    )
    artifact_inputs = {
        green.ref(): ArtifactInputPlan(
            name=green.name,
            path="/memory/OrigGreen.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("2",),
            group_component=Microscopy.Channel,
            variable_components=(Microscopy.Site,),
        ),
        red.ref(): ArtifactInputPlan(
            name=red.name,
            path="/memory/OrigRed.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("3",),
            group_component=Microscopy.Channel,
            variable_components=(Microscopy.Site,),
        ),
        green_mask.ref(): ArtifactInputPlan(
            name=mask_name,
            path="/memory/CropBlue__crop_mask.pkl",
            artifact_type=ImageArtifactType,
            sidecar_role=ArtifactSidecarRole.CROP_MASK,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            variable_components=(Microscopy.Site,),
        ),
    }

    outputs = planner.artifacts.process_artifact_outputs(
        ArtifactGraph(
            producers=(
                ArtifactProducer(
                    spec=green_output,
                    groups=("2",),
                    invocation_keys=(green_key,),
                ),
                ArtifactProducer(
                    spec=red_output,
                    groups=("3",),
                    invocation_keys=(red_key,),
                ),
            ),
            consumers=consumers,
        ),
        sid=2,
        artifact_inputs=artifact_inputs,
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet((Microscopy.Site,)),
        step_name="Crop",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    for output_spec, source in (
        (green_output, green),
        (red_output, red),
    ):
        output_plan = outputs[output_spec.ref()]
        assert output_plan.source_context_source() == source.ref()
        assert output_plan.group_scope_sources() == (source.ref(),)
        assert output_plan.materialization_source() is None

    ambiguous_output = ArtifactSpec.output_preserving_source_stack_scope(
        "ProjectedCropMask",
        ImageArtifactType,
        green_mask,
    )
    projected = planner.artifacts.process_artifact_outputs(
        ArtifactGraph(
            producers=(
                ArtifactProducer(
                    spec=ambiguous_output,
                    groups=("2",),
                    invocation_keys=(green_key,),
                ),
            ),
            consumers=consumers,
        ),
        sid=2,
        artifact_inputs=artifact_inputs,
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet((Microscopy.Site,)),
        step_name="Crop",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert projected[ambiguous_output.ref()].variable_components == (
        Microscopy.Site,
    )


def test_enabled_source_bindings_preserve_previous_step_main_flow():
    input_image = ArtifactSpec.input("Input", ImageArtifactType)
    measurements = ArtifactSpec.input("Measurements", MeasurementsArtifactType)
    context = ArtifactDeclarationStepContext(
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias="Input"),),
        ),
        input_source=InputSource.PREVIOUS_STEP,
        main_flow_artifacts=ArtifactSpecCollection(
            (ArtifactSpec.input("Previous", ImageArtifactType),)
        ),
    ).with_source_declarations((input_image, measurements))

    assert context.available_artifacts.names() == ("Input", "Measurements")
    assert context.main_flow_artifacts.names() == ("Previous",)


def test_artifact_lineage_projects_exact_source_binding_component():
    source_binding_spec = ArtifactSpec.input("OrigStain1", ImageArtifactType)
    aligned_output = ArtifactSpec.output_preserving_source_stack_scope(
        "Stain1",
        ImageArtifactType,
        source_binding_spec,
    )
    aligned_input = aligned_output.for_plan_type(ArtifactInputPlan)
    object_output = ArtifactSpec.output_preserving_source_stack_scope(
        "Objects1",
        ObjectLabelsArtifactType,
        aligned_input,
    )

    @artifact_inputs(aligned_input)
    @artifact_outputs(object_output)
    def identify(main_image, Stain1):
        del Stain1
        return main_image

    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(
            NamedSourceBinding(
                alias=source_binding_spec.name,
                component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
            ),
        ),
    )
    planner = _artifact_planner_stub()
    planner.artifact_context = (
        ArtifactDeclarationStepContext(source_bindings=source_bindings)
        .with_source_declarations((source_binding_spec,))
        .advance_artifact_graph(
            ArtifactGraph(
                producers=(
                    ArtifactProducer(
                        spec=aligned_output,
                        groups=("1", "2"),
                        invocation_keys=(
                            FunctionInvocationKey("align", DEFAULT_GROUP_KEY, 0),
                        ),
                    ),
                ),
            ),
            # Stain1 is the stored auxiliary operand whose projection is tested.
            # It must not also be declared as already carried in the main payload.
            main_flow_artifacts=ArtifactSpecCollection(()),
        )
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=aligned_input.name,
            path="/memory/Stain1.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1", "2"),
            group_component=Microscopy.Site,
            variable_components=(Microscopy.Channel,),
            paths_by_group={
                "1": "/memory/Stain1_site_1.pkl",
                "2": "/memory/Stain1_site_2.pkl",
            },
            relations=aligned_output.relations,
            producer_step_index=2,
            producer_step_name="Align",
        ),
    )
    snapshot = _resolved_step(
        name="IdentifyPrimaryObjects", func=identify, source_bindings=source_bindings
    )
    declarations = extract_artifact_declarations(identify)
    execution_scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
        source_bindings=source_bindings,
    )
    declarations = declarations

    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        3,
        declarations,
        execution_scope,
        source_bindings=source_bindings,
    )
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        3,
        True,
        identify,
        maps.inputs,
        maps.outputs,
        maps.relation_source_scopes,
        maps.group_scope,
        declarations=declarations,
    )

    expected_channel_scope = ComponentGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )
    assert maps.group_scope.keys == expected_channel_scope.keys
    assert maps.group_scope.component is expected_channel_scope.component
    assert maps.outputs[object_output.ref()].group_keys == ("1",)
    assert maps.outputs[object_output.ref()].variable_components == (
        Microscopy.Site,
    )
    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    assert edge.projection.invocation_scope == expected_channel_scope
    assert edge.projection.component_scope(Microscopy.Channel) == (
        expected_channel_scope
    )
    assert edge.projection.producer_selection_scope == ComponentGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Site,
    )


@pytest.mark.parametrize(
    ("artifact_type", "output_name"),
    (
        (ImageArtifactType, "CorrProtein"),
        (ObjectLabelsArtifactType, "AdvancedObjects"),
    ),
    ids=("produced-image", "produced-object-labels"),
)
def test_fixed_source_component_domain_survives_produced_artifact_lineage(
    artifact_type,
    output_name,
):
    source = ArtifactSpec.input("OrigProtein", ImageArtifactType)
    output_spec = ArtifactSpec.output_preserving_source_stack_scope(
        output_name,
        artifact_type,
        source,
    )
    invocation_key = FunctionInvocationKey("produce", DEFAULT_GROUP_KEY, 0)
    producer_declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=output_spec,
                groups=(None,),
                invocation_keys=(invocation_key,),
            ),
        ),
        non_plan_consumers=(ArtifactConsumer(source, (invocation_key,)),),
    )
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(
            NamedSourceBinding(
                alias=source.name,
                component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
            ),
        ),
    )
    planner = _artifact_planner_stub()
    planner.artifact_context = ArtifactDeclarationStepContext(
        source_bindings=source_bindings,
    ).with_source_declarations((source,))
    producer_scope = PathPlannerGroupScope.from_raw(
        ("1",),
        component=Microscopy.Site,
    )
    relation_scopes = planner.artifacts.relation_source_scopes_by_ref(
        producer_declarations,
        {},
        group_scope=producer_scope,
        source_bindings=source_bindings,
        group_by=Microscopy.Site,
    )
    output_groups = planner.artifacts.output_groups_from_declared_relations(
        producer_declarations,
        group_scope=producer_scope,
        relation_source_scopes=relation_scopes,
        consumer_variable_components=ComponentSet((Microscopy.Channel,)),
        step_index=2,
        step_name="produce",
    )
    output_plan = planner.artifacts.process_artifact_outputs(
        producer_declarations,
        2,
        output_groups,
        artifact_inputs={},
        relation_source_scopes=relation_scopes,
        source_bindings=source_bindings,
        variable_components=ComponentSet((Microscopy.Channel,)),
        step_name="produce",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )[output_spec.ref()]

    fixed_channel = ComponentGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )
    assert output_plan.component_domain(Microscopy.Channel) == fixed_channel

    input_spec = output_spec.for_plan_type(ArtifactInputPlan)

    @artifact_inputs(input_spec)
    def consume(image):
        return image

    consumer_declarations = ArtifactGraph(
        consumers=(
            ArtifactConsumer(
                input_spec,
                (FunctionInvocationKey("consume", "2", 0),),
            ),
        ),
    )
    consumer_scope = PathPlannerGroupScope.from_raw(
        ("2",),
        component=Microscopy.Channel,
    )
    input_plan = planner.artifacts.process_artifact_inputs(
        consumer_declarations,
        3,
        consumer_scope,
        EMPTY_SOURCE_BINDINGS,
        ComponentSet((Microscopy.Site,)),
        step_name="consume",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )[input_spec.ref()]
    consumer_relation_scopes = planner.artifacts.relation_source_scopes_by_ref(
        consumer_declarations,
        {input_plan.ref(): input_plan},
        group_scope=consumer_scope,
        source_bindings=EMPTY_SOURCE_BINDINGS,
        group_by=Microscopy.Channel,
    )
    compiled = planner.artifacts.compile_invocation_input_edges(
        compile_function_pattern(
            {"2": consume},
            {plan.ref(): plan for plan in (input_plan,)},
            {},
        ),
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes=consumer_relation_scopes,
        execution_group_scope=consumer_scope,
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
    )
    edge = next(compiled.iter_invocations()).artifact_input_edges[0]

    assert input_plan.component_domain(Microscopy.Channel) == fixed_channel
    assert consumer_relation_scopes[input_spec.ref()] == (
        PathPlannerGroupScope.from_raw(
            fixed_channel.keys,
            component=fixed_channel.component,
        )
    )
    assert edge.projection.component_scope(Microscopy.Channel) == fixed_channel


@pytest.mark.parametrize(
    ("step_name", "consumer_axes", "source_axes"),
    (
        (
            "Crop",
            (Microscopy.Site,),
            ((), (Microscopy.Site,)),
        ),
        (
            "Align",
            (Microscopy.Channel,),
            ((Microscopy.Channel,), (), ()),
        ),
    ),
    ids=("crop-site-and-scalar-sources", "align-channel-and-scalar-sources"),
)
def test_measurement_provenance_does_not_preserve_source_stack_axes(
    step_name,
    consumer_axes,
    source_axes,
):
    planner = _artifact_planner_stub()
    sources = tuple(
        ArtifactSpec.input(f"source_{index}", ImageArtifactType)
        for index in range(len(source_axes))
    )
    measurement = ArtifactSpec.output(
        f"{step_name}_measurements",
        MeasurementsArtifactType,
        relations=tuple(
            ArtifactSpecRelation(source=source.ref()) for source in sources
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=measurement,
                groups=(None,),
                invocation_keys=(
                    FunctionInvocationKey(
                        step_name.lower(),
                        DEFAULT_GROUP_KEY,
                        0,
                    ),
                ),
            ),
        ),
    )
    artifact_inputs = {
        source.ref(): ArtifactInputPlan(
            name=source.name,
            path=f"/memory/{source.name}.pkl",
            artifact_type=source.artifact_type,
            variable_components=axes,
        )
        for source, axes in zip(sources, source_axes, strict=True)
    }

    outputs = planner.artifacts.process_artifact_outputs(
        declarations,
        sid=2,
        artifact_inputs=artifact_inputs,
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet(consumer_axes),
        step_name=step_name,
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert outputs[measurement.ref()].variable_components == ()
    assert all(
        relation.source_stack_scope_source() is None
        for relation in outputs[measurement.ref()].relations
    )
    assert {relation.source for relation in outputs[measurement.ref()].relations} == {
        source.ref() for source in sources
    }


def test_group_by_namespaces_compiler_owned_outputs():
    @artifact_outputs(ArtifactSpec.output("nuclei", ObjectLabelsArtifactType))
    def identify(image):
        return image

    planner = _artifact_planner_stub()
    declarations = extract_artifact_declarations(identify)

    namespaced = declarations

    scopes = planner.artifacts.output_groups_from_declared_relations(
        namespaced,
        group_scope=PathPlannerGroupScope.from_raw(("1", "2"), component=Microscopy.Channel),
        relation_source_scopes={}, consumer_variable_components=ComponentSet(),
        step_index=0, step_name="identify",
    )
    assert scopes[ArtifactSpec.output("nuclei", ObjectLabelsArtifactType).ref()].keys == ("1", "2")


def test_artifact_graph_preserves_same_name_outputs_of_different_types():
    image_output = ArtifactSpec.output("shared", ImageArtifactType)
    object_output = ArtifactSpec.output("shared", ObjectLabelsArtifactType)

    @artifact_outputs(image_output, object_output)
    def produce(image):
        return image, image

    declarations = extract_artifact_declarations(produce)

    assert tuple(declarations.outputs) == (
        image_output.ref(),
        object_output.ref(),
    )


def test_group_by_namespaces_runtime_adapter_artifact_outputs():
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    def correct_illumination(image, *, runtime):
        return image

    def declarations_for_invocation(invocation, step_context):
        del invocation, step_context

        @artifact_outputs(ArtifactSpec.output("Hoechst", ImageArtifactType))
        def declared_artifact_owner(image):
            return image

        return CallableContract.from_callable(declared_artifact_owner)

    planner = _artifact_planner_stub()
    declarations = extract_artifact_declarations(
        correct_illumination,
        declaration_provider=declarations_for_invocation,
    )

    namespaced = declarations

    output_ref = ArtifactSpec.output("Hoechst", ImageArtifactType).ref()
    assert declarations.output_groups[output_ref] == {None}
    scopes = planner.artifacts.output_groups_from_declared_relations(
        namespaced,
        group_scope=PathPlannerGroupScope.from_raw(("1", "2"), component=Microscopy.Channel),
        relation_source_scopes={}, consumer_variable_components=ComponentSet(),
        step_index=0, step_name="correct_illumination",
    )
    assert scopes[output_ref].keys == ("1", "2")


def test_declared_group_lineage_scopes_outputs_without_rewriting_execution():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="Tile_of_grid",
            path="/memory/Tile_of_grid.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/Tile_of_grid_1.pkl"},
        ),
    )
    source = ArtifactSpec.input("Tile_of_grid", ObjectLabelsArtifactType).ref()
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "Filtered_tiles",
                    ObjectLabelsArtifactType,
                    source,
                ),
                groups=("2",),
                invocation_keys=(),
            ),
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "FilterObjects_8_measurements",
                    MeasurementsArtifactType,
                    source,
                ),
                groups=("2",),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("Tile_of_grid", ObjectLabelsArtifactType),
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="FilterObjects"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(("2",), component=Microscopy.Channel),
    )

    filtered_tiles_ref = ArtifactSpec.output(
        "Filtered_tiles",
        ObjectLabelsArtifactType,
    ).ref()
    measurements_ref = ArtifactSpec.output(
        "FilterObjects_8_measurements",
        MeasurementsArtifactType,
    ).ref()
    assert maps.outputs[filtered_tiles_ref].group_keys == ("1",)
    assert maps.outputs[measurements_ref].group_keys == ("1",)
    assert maps.outputs[filtered_tiles_ref].group_component is Microscopy.Channel
    assert maps.outputs[measurements_ref].group_component is Microscopy.Channel
    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("2",),
        component=Microscopy.Channel,
    )


def test_declared_group_lineage_uses_main_flow_scope_without_artifact_plan():
    planner = _artifact_planner_stub()
    source = ArtifactSpec.input("Stain1", ImageArtifactType)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "MeasureColocalization_4_measurements",
                    MeasurementsArtifactType,
                    source.ref(),
                ),
                groups=(None,),
                invocation_keys=(),
            ),
        ),
        non_plan_consumers=(
            ArtifactConsumer(
                spec=source,
                invocation_keys=(),
            ),
        ),
    )
    group_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Site,
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="MeasureColocalization"),
        3,
        declarations,
        group_scope,
    )

    assert maps.inputs == {}
    measurements_ref = ArtifactSpec.output(
        "MeasureColocalization_4_measurements",
        MeasurementsArtifactType,
    ).ref()
    assert maps.outputs[measurements_ref].group_keys == (
        "1",
        "2",
    )
    assert maps.outputs[measurements_ref].group_component is Microscopy.Site


def test_prior_main_flow_artifact_scopes_output_without_rewriting_execution():
    planner = _artifact_planner_stub()
    producer = ArtifactOutputPlan(
        name="CropRed",
        path="/memory/CropRed.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("3",),
        group_component=Microscopy.Channel,
        paths_by_group={"3": "/memory/CropRed_3.pkl"},
    )
    _record_declared_output(planner, producer)
    source = ArtifactSpec.input("CropRed", ImageArtifactType)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "Nuclei",
                    ObjectLabelsArtifactType,
                    source.ref(),
                ),
                groups=("2", "3"),
                invocation_keys=(),
            ),
        ),
        non_plan_consumers=(
            ArtifactConsumer(
                spec=source,
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="IdentifyPrimaryObjects"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("2", "3"),
            component=Microscopy.Channel,
        ),
    )

    assert maps.inputs == {}
    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("2", "3"),
        component=Microscopy.Channel,
    )
    nuclei_ref = ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType).ref()
    assert maps.outputs[nuclei_ref].group_keys == ("3",)


def test_dict_invocation_lineage_uses_its_non_plan_input_group_scope():
    planner = _artifact_planner_stub()
    source = ArtifactSpec.input("Stain1", ImageArtifactType)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "Objects1",
                    ObjectLabelsArtifactType,
                    source.ref(),
                ),
                groups=("1",),
                invocation_keys=(FunctionInvocationKey("identify", "1", 0),),
            ),
        ),
        non_plan_consumers=(
            ArtifactConsumer(
                spec=source,
                invocation_keys=(FunctionInvocationKey("identify", "1", 0),),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="IdentifyPrimaryObjects"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        ),
    )

    objects_ref = ArtifactSpec.output("Objects1", ObjectLabelsArtifactType).ref()
    assert maps.outputs[objects_ref].group_keys == ("1",)


def test_measurement_output_scope_compiles_exact_cross_group_consumer_edge():
    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = SimpleNamespace(
        can_resolve_metadata_artifact=lambda artifact_name: artifact_name == "DF_image",
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="Tile_of_grid",
            path="/memory/Tile_of_grid.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/Tile_of_grid_1.pkl"},
        ),
    )
    image_ref = ArtifactSpec.input("DF_image", ImageArtifactType).ref()
    object_ref = ArtifactSpec.input(
        "Tile_of_grid",
        ObjectLabelsArtifactType,
    ).ref()
    invocation_key = FunctionInvocationKey("measure_object_intensity", "2", 0)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "MeasureObjectIntensity_3_measurements",
                    MeasurementsArtifactType,
                    relations=(
                        ArtifactSpecRelation(image_ref),
                        ArtifactSpecRelation(object_ref),
                        GroupLineageSourceRelation(image_ref),
                    ),
                ),
                groups=("2",),
                invocation_keys=(invocation_key,),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "Tile_of_grid",
                    ObjectLabelsArtifactType,
                    relations=(InputGroupLineageSourceRelation(source=image_ref),),
                ),
                invocation_keys=(invocation_key,),
            ),
        ),
        non_plan_consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("DF_image", ImageArtifactType),
                invocation_keys=(invocation_key,),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="MeasureObjectIntensity"),
        2,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("2",),
            component=Microscopy.Channel,
        ),
    )

    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("2",),
        component=Microscopy.Channel,
    )
    measurement_name = "MeasureObjectIntensity_3_measurements"
    measurement_ref = ArtifactSpec.output(
        measurement_name,
        MeasurementsArtifactType,
    ).ref()
    assert maps.outputs[measurement_ref].group_keys == ("2",)
    _record_declared_output(planner, maps.outputs[measurement_ref])
    measurement_input = ArtifactSpec.input(
        measurement_name,
        MeasurementsArtifactType,
    )

    @artifact_inputs(measurement_input)
    def filter_objects(main_image, MeasureObjectIntensity_3_measurements):
        del MeasureObjectIntensity_3_measurements
        return main_image

    consumer_invocation = FunctionInvocationKey(
        "filter_objects",
        DEFAULT_GROUP_KEY,
        0,
    )
    consumer_snapshot = _resolved_step(
        name="FilterObjects",
        func=filter_objects,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
    )
    consumer_maps = planner.artifacts.compile_plan_maps(
        consumer_snapshot,
        3,
        ArtifactGraph(
            consumers=(
                ArtifactConsumer(
                    spec=measurement_input,
                    invocation_keys=(consumer_invocation,),
                ),
            ),
        ),
        PathPlannerGroupScope.from_raw(
            ("1",),
            component=Microscopy.Channel,
        ),
    )
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        consumer_snapshot,
        3,
        True,
        filter_objects,
        consumer_maps.inputs,
        consumer_maps.outputs,
        consumer_maps.relation_source_scopes,
        consumer_maps.group_scope,
        declarations=extract_artifact_declarations(filter_objects, invocation_contract_provider=planner.invocation_contract_provider, step_context=planner.artifact_context),
    )

    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    assert edge.projection.producer_selection_scope == ComponentGroupScope(
        ("2",),
        component=Microscopy.Channel,
    )


def test_artifact_managed_lineage_keeps_exact_named_inputs_in_one_invocation():
    planner = _artifact_planner_stub()
    producer_declarations = (
        ("CropBlue", ImageArtifactType, "1"),
        ("Nuclei", ObjectLabelsArtifactType, "1"),
        ("Cells", ObjectLabelsArtifactType, "2"),
        ("Cytoplasm", ObjectLabelsArtifactType, "2"),
    )
    for name, artifact_type, channel in producer_declarations:
        _record_declared_output(
            planner,
            ArtifactOutputPlan(
                name=name,
                path=f"/memory/{name}.pkl",
                artifact_type=artifact_type,
                group_keys=(channel,),
                group_component=Microscopy.Channel,
                variable_components=(Microscopy.Site,),
                paths_by_group={channel: f"/memory/{name}_{channel}.pkl"},
            ),
        )

    declared_inputs = tuple(
        ArtifactSpec.input(name, artifact_type)
        for name, artifact_type, _channel in producer_declarations
    )
    inputs = tuple(
        replace(
            spec,
            relations=(InputGroupLineageSourceRelation(source=spec.ref()),),
        )
        for spec in declared_inputs
    )
    input_by_name = {spec.name: spec for spec in inputs}
    invocation_key = FunctionInvocationKey("measure", DEFAULT_GROUP_KEY, 0)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "Measurements",
                    MeasurementsArtifactType,
                    relations=(
                        GroupLineageSourceRelation(input_by_name["Nuclei"].ref()),
                        GroupLineageSourceRelation(input_by_name["Cells"].ref()),
                        GroupLineageSourceRelation(input_by_name["Cytoplasm"].ref()),
                        ArtifactSpecRelation(input_by_name["CropBlue"].ref()),
                    ),
                ),
                groups=(None,),
                invocation_keys=(invocation_key,),
            ),
        ),
        consumers=tuple(
            ArtifactConsumer(
                spec=spec,
                invocation_keys=(invocation_key,),
            )
            for spec in inputs
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="MeasureObjectSizeShape"),
        3,
        declarations,
        PathPlannerGroupScope.ungrouped(),
    )

    assert maps.group_scope == PathPlannerGroupScope.ungrouped()
    assert set(maps.inputs) == {spec.ref() for spec in inputs}


def test_artifact_managed_single_source_output_retains_source_group_scope():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="CropBlue",
            path="/memory/CropBlue.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/CropBlue_1.pkl"},
        ),
    )
    declared_source = ArtifactSpec.input("CropBlue", ImageArtifactType)
    source = replace(
        declared_source,
        relations=(InputGroupLineageSourceRelation(source=declared_source.ref()),),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "Nuclei",
                    ObjectLabelsArtifactType,
                    relations=(GroupLineageSourceRelation(source.ref()),),
                ),
                groups=(None,),
                invocation_keys=(
                    FunctionInvocationKey("identify", DEFAULT_GROUP_KEY, 0),
                ),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=source,
                invocation_keys=(
                    FunctionInvocationKey("identify", DEFAULT_GROUP_KEY, 0),
                ),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="IdentifyPrimaryObjects"),
        3,
        declarations,
        PathPlannerGroupScope.ungrouped(),
    )

    assert maps.group_scope == PathPlannerGroupScope.ungrouped()
    nuclei_ref = ArtifactSpec.output("Nuclei", ObjectLabelsArtifactType).ref()
    assert maps.outputs[nuclei_ref].group_keys == ("1",)
    assert maps.outputs[nuclei_ref].group_component is Microscopy.Channel


def test_declared_group_lineage_unions_compatible_source_groups():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="OrigStain1",
            path="/memory/OrigStain1.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/OrigStain1_1.pkl"},
        ),
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="OrigStain2",
            path="/memory/OrigStain2.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("2",),
            group_component=Microscopy.Channel,
            paths_by_group={"2": "/memory/OrigStain2_2.pkl"},
        ),
    )
    first_ref = ArtifactSpec.input("OrigStain1", ImageArtifactType).ref()
    second_ref = ArtifactSpec.input("OrigStain2", ImageArtifactType).ref()
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "Measurements",
                    MeasurementsArtifactType,
                    relations=(
                        GroupLineageSourceRelation(first_ref),
                        GroupLineageSourceRelation(second_ref),
                    ),
                ),
                groups=("1", "2"),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("OrigStain1", ImageArtifactType),
                invocation_keys=(FunctionInvocationKey("measure", "1", 0),),
            ),
            ArtifactConsumer(
                spec=ArtifactSpec.input("OrigStain2", ImageArtifactType),
                invocation_keys=(FunctionInvocationKey("measure", "2", 0),),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="Measure"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        ),
    )

    measurements_ref = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
    ).ref()
    assert maps.outputs[measurements_ref].group_keys == ("1", "2")
    assert maps.relation_source_scopes[first_ref] == (
        PathPlannerGroupScope.from_raw(("1",), component=Microscopy.Channel)
    )
    assert maps.relation_source_scopes[second_ref] == (
        PathPlannerGroupScope.from_raw(("2",), component=Microscopy.Channel)
    )


def test_dynamic_group_scope_union_remains_dynamic():
    dynamic_scope = PathPlannerGroupScope.dynamic(Microscopy.Site)
    concrete_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Site,
    )

    assert (
        PathPlannerGroupScope.union_compatible((dynamic_scope, concrete_scope))
        == dynamic_scope
    )


def test_collected_lineage_outputs_use_relation_owned_group_scope():
    planner = _artifact_planner_stub()
    for name, channel, artifact_type in (
        ("CropBlue", "1", ImageArtifactType),
        ("CropGreen", "2", ImageArtifactType),
        ("Nuclei", "1", ObjectLabelsArtifactType),
    ):
        _record_declared_output(
            planner,
            ArtifactOutputPlan(
                name=name,
                path=f"/memory/{name}.pkl",
                artifact_type=artifact_type,
                group_keys=(channel,),
                group_component=Microscopy.Channel,
                variable_components=(Microscopy.Site,),
                paths_by_group={channel: f"/memory/{name}_{channel}.pkl"},
            ),
        )

    input_specs = (
        ArtifactSpec.input("CropBlue", ImageArtifactType),
        ArtifactSpec.input("CropGreen", ImageArtifactType),
        ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "Measurements",
                    MeasurementsArtifactType,
                    relations=tuple(
                        GroupLineageSourceRelation(spec.ref()) for spec in input_specs
                    ),
                ),
                groups=(None,),
                invocation_keys=(),
            ),
        ),
        consumers=tuple(
            ArtifactConsumer(
                spec=spec,
                invocation_keys=(),
            )
            for spec in input_specs
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(
            name="MeasureColocalization",
            group_by=Microscopy.Site,
            variable_components=(Microscopy.Channel,),
        ),
        3,
        declarations,
        PathPlannerGroupScope.dynamic(Microscopy.Site),
    )

    assert maps.group_scope == PathPlannerGroupScope.dynamic(Microscopy.Site)
    measurements_ref = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
    ).ref()
    assert maps.outputs[measurements_ref].group_keys == (None,)
    assert maps.outputs[measurements_ref].group_component is Microscopy.Site


def test_output_lineage_uses_input_qualified_consumer_scope():
    planner = _artifact_planner_stub()
    nuclei = ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType)
    prior_measurements = ArtifactSpec.input(
        "PriorMeasurements",
        MeasurementsArtifactType,
        relations=(InputGroupLineageSourceRelation(nuclei.ref()),),
    )
    result = ArtifactSpec.output(
        "ResultMeasurements",
        MeasurementsArtifactType,
        relations=(GroupLineageSourceRelation(prior_measurements.ref()),),
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=nuclei.name,
            path="/memory/Nuclei.pkl",
            artifact_type=nuclei.artifact_type,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/Nuclei_1.pkl"},
        ),
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=prior_measurements.name,
            path="/memory/PriorMeasurements.pkl",
            artifact_type=prior_measurements.artifact_type,
            group_keys=("1", "2"),
            group_component=Microscopy.Channel,
            paths_by_group={
                "1": "/memory/PriorMeasurements_1.pkl",
                "2": "/memory/PriorMeasurements_2.pkl",
            },
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=result,
                groups=(None,),
                invocation_keys=(
                    FunctionInvocationKey("calculate", DEFAULT_GROUP_KEY, 0),
                ),
            ),
        ),
        consumers=(
            ArtifactConsumer(prior_measurements, invocation_keys=()),
            ArtifactConsumer(nuclei, invocation_keys=()),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="Calculate"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        ),
    )

    output_plan = maps.outputs[result.ref()]
    assert maps.relation_source_scopes[prior_measurements.ref()] == (
        PathPlannerGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        )
    )
    assert output_plan.group_keys == ("1",)
    assert output_plan.group_scope_sources_by_group == {
        "1": (prior_measurements.ref(),),
    }


def test_planner_derived_group_lineage_selects_exact_managed_invocation():
    blue = ArtifactSpec.input("OrigBlue", ImageArtifactType)
    green = ArtifactSpec.input("OrigGreen", ImageArtifactType)
    blue_measurements = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        relations=(
            GroupLineageSourceRelation(blue.ref()),
            ArtifactMeasurementSubjectRelation(),
        ),
    )
    green_measurements = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        relations=(
            GroupLineageSourceRelation(green.ref()),
            ArtifactMeasurementSubjectRelation(),
        ),
    )

    @artifact_inputs(blue)
    @artifact_outputs(blue_measurements)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    def measure_blue(image, *, runtime):
        del runtime
        return image

    @artifact_inputs(green)
    @artifact_outputs(green_measurements)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    def measure_green(image, *, runtime):
        del runtime
        return image

    functions = [measure_blue, measure_green]
    declarations = extract_artifact_declarations(functions)
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=tuple(
            NamedSourceBinding(
                alias=name,
                origin=SourceBindingOrigin.PIPELINE_START,
                component_identity=(ComponentSelector(Microscopy.Channel, channel),),
            )
            for name, channel in ((blue.name, "1"), (green.name, "2"))
        ),
    )
    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        name="MeasureChannels",
        func=functions,
        source_bindings=source_bindings,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        input_source=InputSource.PIPELINE_START,
    )
    execution_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )

    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        3,
        declarations,
        execution_scope,
        source_bindings=source_bindings,
    )
    compiled = compile_function_pattern(functions, maps.inputs, maps.outputs)
    compiled = planner.artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs=maps.inputs,
        relation_source_scopes=maps.relation_source_scopes,
        execution_group_scope=execution_scope,
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
        source_bindings=source_bindings,
        available_artifacts=planner.artifact_context.available_artifacts,
        main_flow_artifacts=planner.artifact_context.main_flow_artifacts,
    )

    output_plan = maps.outputs[blue_measurements.ref()]
    assert output_plan.group_scope_sources_by_group == {
        "1": (blue.ref(),),
        "2": (green.ref(),),
    }
    assert {
        channel: tuple(
            invocation.key.function_name
            for invocation in compiled.default_group.invocations
            if invocation.output_plans_for_component(execution_scope, channel)
            is not None
        )
        for channel in execution_scope.keys
    } == {
        "1": ("measure_blue",),
        "2": ("measure_green",),
    }


@pytest.mark.parametrize("measurement_group", ["1", "2", DEFAULT_GROUP_KEY])
def test_real_object_measurement_preserves_selected_labels_group_scope(
    measurement_group,
):
    """An exact label selector does not rewrite an explicitly authored group."""
    from openhcs.core.function_patterns import normalize_function_pattern
    from openhcs.interop.cellprofiler.compile_time_contracts import (
        CellProfilerInvocationContractProvider,
    )
    from openhcs.processing.backends.cellprofiler.shape import (
        MeasureObjectSizeShapeModule,
        measure_object_size_shape,
    )

    planner = _artifact_planner_stub()
    labels_plan = _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="Cells",
            path="/memory/Cells.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=("2",),
            group_component=Microscopy.Channel,
            variable_components=(Microscopy.Site,),
            paths_by_group={"2": "/memory/Cells_2.pkl"},
        ),
    )
    selector = (
        MeasureObjectSizeShapeModule.object_measurement_binding.require_parameter_name()
    )
    invocation_pattern = (measure_object_size_shape, {selector: "Cells"})
    pattern = (
        invocation_pattern
        if measurement_group == DEFAULT_GROUP_KEY
        else {measurement_group: [invocation_pattern]}
    )
    snapshot = _resolved_step(name="MeasureCells", func=pattern)
    labels_input = ArtifactSpec.input("Cells", ObjectLabelsArtifactType)
    step_context = ArtifactDeclarationStepContext(
        step_name=snapshot.name,
        step_index=3,
        group_by=Microscopy.Channel,
        available_artifacts=ArtifactSpecCollection((labels_input,)),
        available_artifact_producers=(
            ArtifactProducer(
                ArtifactSpec.output("Cells", ObjectLabelsArtifactType),
                groups=labels_plan.group_keys,
                invocation_keys=(),
                producer_step_index=2,
            ),
        ),
    )
    authored = next(normalize_function_pattern(pattern).iter_items())
    blocks, consumed_names = MeasureObjectSizeShapeModule.module_blocks_for_invocation(
        invocation=authored,
        step_context=step_context,
    )
    (numbered_blocks,), _ = MeasureObjectSizeShapeModule.number_step_invocation_blocks(
        (blocks,), first_module_num=4
    )
    contract, consumed_names = (
        MeasureObjectSizeShapeModule.invocation_callable_contract(
            invocation=authored,
            numbered_module_blocks=numbered_blocks,
            consumed_kwarg_names=consumed_names,
            step_context=step_context,
        )
    )
    provider = CellProfilerInvocationContractProvider(
        {(3, authored.key): InvocationContractPlan(contract, consumed_names)}
    )
    declarations = extract_artifact_declarations(
        pattern,
        invocation_contract_provider=provider,
        step_context=step_context,
    )
    (measurement,) = contract.artifact_outputs.of_artifact_type(
        MeasurementsArtifactType
    )
    (object_input,) = contract.artifact_inputs.of_artifact_type(
        ObjectLabelsArtifactType
    )
    assert object_input.ref() == labels_input.ref()
    assert object_input.parameter_name == "labels"
    assert measurement.measurement_feature_owner is MeasureObjectSizeShapeModule
    assert measurement.name == "MeasureCells_4_measurements"
    assert measurement.group_scope_sources() == (labels_input.ref(),)
    assert (
        MeasurementsArtifactType.require_output_subject(measurement)
        == ObjectMeasurementSubjectRelation(labels_input.ref()).measurement_subject()
    )
    assert selector in consumed_names
    group_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"), component=Microscopy.Channel
    )

    if measurement_group == "1":
        with pytest.raises(
            ValueError,
            match="MeasureCells_4_measurements.*group '1' has no declared group-scope source",
        ):
            planner.artifacts.compile_plan_maps(snapshot, 3, declarations, group_scope)
        return

    maps = planner.artifacts.compile_plan_maps(snapshot, 3, declarations, group_scope)
    measurement_plan = maps.outputs[measurement.ref()]
    assert maps.inputs[labels_input.ref()].group_keys == labels_plan.group_keys
    assert measurement_plan.group_keys == ("2",)
    assert measurement_plan.group_scope_sources_by_group == {
        "2": (labels_input.ref(),),
    }
    compiled = compile_function_pattern(
        pattern,
        maps.inputs,
        maps.outputs,
        invocation_contract_provider=provider,
        step_context=step_context,
    )
    (invocation,) = tuple(compiled.iter_invocations())
    assert selector not in dict(invocation.kwargs)
    assert invocation.contract is contract


def test_declared_group_lineage_cannot_rewrite_scalar_step_execution_scope():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="MembInvertRemoveHoles",
            path="/memory/MembInvertRemoveHoles.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("3",),
            group_component=Microscopy.Channel,
            paths_by_group={"3": "/memory/MembInvertRemoveHoles_3.pkl"},
        ),
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="MonolayerMask",
            path="/memory/MonolayerMask.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/MonolayerMask_1.pkl"},
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "MembMasked",
                    ImageArtifactType,
                    ArtifactSpec.input(
                        "MembInvertRemoveHoles",
                        ImageArtifactType,
                    ).ref(),
                ),
                groups=("1", "3"),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("MembInvertRemoveHoles", ImageArtifactType),
                invocation_keys=(),
            ),
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "MonolayerMask",
                    ImageArtifactType,
                    relations=(
                        InputGroupLineageSourceRelation(
                            source=ArtifactSpec.input(
                                "MembInvertRemoveHoles",
                                ImageArtifactType,
                            ).ref()
                        ),
                    ),
                ),
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="MaskImage"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(("1", "3"), component=Microscopy.Channel),
    )

    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("1", "3"),
        component=Microscopy.Channel,
    )
    masked_ref = ArtifactSpec.output("MembMasked", ImageArtifactType).ref()
    assert maps.outputs[masked_ref].group_keys == ("3",)
    assert maps.outputs[masked_ref].relations == (
        GroupLineageSourceRelation(
            ArtifactSpec.input(
                "MembInvertRemoveHoles",
                ImageArtifactType,
            ).ref()
        ),
    )
    monolayer_ref = ArtifactSpec.input("MonolayerMask", ImageArtifactType).ref()
    assert tuple(maps.inputs) == (
        ArtifactSpec.input("MembInvertRemoveHoles", ImageArtifactType).ref(),
        monolayer_ref,
    )
    assert maps.inputs[monolayer_ref].path == ("/memory/MonolayerMask_1.pkl")
    assert maps.inputs[monolayer_ref].group_keys == ("1",)


def test_artifact_output_storage_scope_is_independent_of_execution_scope():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="PriorMeasurements",
            path="/memory/PriorMeasurements.pkl",
            artifact_type=MeasurementsArtifactType,
            group_keys=("1", "2"),
            group_component=Microscopy.Channel,
            paths_by_group={
                "1": "/memory/PriorMeasurements_1.pkl",
                "2": "/memory/PriorMeasurements_2.pkl",
            },
            producer_step_index=1,
            producer_step_name="MeasureObjectIntensity",
        ),
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="Nuclei",
            path="/memory/Nuclei.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/Nuclei_1.pkl"},
            producer_step_index=2,
            producer_step_name="IdentifyPrimaryObjects",
        ),
    )
    nuclei_input = ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "Ratio",
                    MeasurementsArtifactType,
                    relations=(GroupLineageSourceRelation(nuclei_input.ref()),),
                ),
                groups=("3",),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "PriorMeasurements",
                    MeasurementsArtifactType,
                ),
                invocation_keys=(),
            ),
            ArtifactConsumer(
                spec=nuclei_input,
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="CalculateMath"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(("3",), component=Microscopy.Channel),
    )

    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("3",),
        component=Microscopy.Channel,
    )
    ratio_ref = ArtifactSpec.output("Ratio", MeasurementsArtifactType).ref()
    assert maps.outputs[ratio_ref].group_keys == ("1",)
    assert tuple(maps.inputs) == (
        ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType).ref(),
        ArtifactSpec.input("PriorMeasurements", MeasurementsArtifactType).ref(),
    )


def test_each_output_storage_scope_is_independent_of_execution_scope():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="source",
            path="/memory/source.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("2",),
            group_component=Microscopy.Channel,
            paths_by_group={"2": "/memory/source_2.pkl"},
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "scoped",
                    ImageArtifactType,
                    ArtifactSpec.input("source", ImageArtifactType).ref(),
                ),
                groups=("1", "2"),
                invocation_keys=(),
            ),
            ArtifactProducer(
                spec=ArtifactSpec.output("ambiguous", MeasurementsArtifactType),
                groups=("1", "2"),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "source",
                    ImageArtifactType,
                    relations=(
                        InputGroupLineageSourceRelation(
                            source=ArtifactSpec.input(
                                "source",
                                ImageArtifactType,
                            ).ref()
                        ),
                    ),
                ),
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="invocation-scoped-output"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        ),
    )

    execution_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )
    relation_scope = PathPlannerGroupScope.from_raw(
        ("2",),
        component=Microscopy.Channel,
    )
    assert maps.group_scope == execution_scope
    scoped_ref = ArtifactSpec.output("scoped", ImageArtifactType).ref()
    ambiguous_ref = ArtifactSpec.output(
        "ambiguous",
        MeasurementsArtifactType,
    ).ref()
    assert PathPlannerGroupScope.from_output_plan(maps.outputs[scoped_ref]) == (
        relation_scope
    )
    assert PathPlannerGroupScope.from_output_plan(maps.outputs[ambiguous_ref]) == (
        execution_scope
    )


def test_dict_pattern_output_groups_do_not_drive_scalar_scope_narrowing():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="source",
            path="/memory/source.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("3",),
            group_component=Microscopy.Channel,
            paths_by_group={"3": "/memory/source_3.pkl"},
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "output",
                    ImageArtifactType,
                    ArtifactSpec.input("source", ImageArtifactType).ref(),
                ),
                groups=("1",),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "source",
                    ImageArtifactType,
                    relations=(
                        InputGroupLineageSourceRelation(
                            source=ArtifactSpec.input(
                                "source",
                                ImageArtifactType,
                            ).ref()
                        ),
                    ),
                ),
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="dict_pattern"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(("1", "3"), component=Microscopy.Channel),
    )

    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("1", "3"),
        component=Microscopy.Channel,
    )


def test_source_binding_component_identity_narrows_declared_output_lineage():
    planner = _artifact_planner_stub()
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "Cells",
                    ObjectLabelsArtifactType,
                    ArtifactSpec.input("origMemb", ImageArtifactType).ref(),
                ),
                groups=("1", "2", "3"),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("origMemb", ImageArtifactType),
                invocation_keys=(),
            ),
        ),
    )
    source_bindings = StepSourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="origMemb",
                component_identity=(ComponentSelector(Microscopy.Channel, "3"),),
            ),
        ),
        enabled=True,
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="Watershed", source_bindings=source_bindings),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("1", "2", "3"),
            component=Microscopy.Channel,
        ),
        source_bindings=source_bindings,
    )

    cells_ref = ArtifactSpec.output("Cells", ObjectLabelsArtifactType).ref()
    assert maps.outputs[cells_ref].group_keys == ("3",)
    assert maps.outputs[cells_ref].group_component is Microscopy.Channel


def test_source_binding_identity_scopes_outputs_without_execution_fanout():
    planner = _artifact_planner_stub()
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "Cells",
                    ObjectLabelsArtifactType,
                    ArtifactSpec.input("origMemb", ImageArtifactType).ref(),
                ),
                groups=(None,),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("origMemb", ImageArtifactType),
                invocation_keys=(),
            ),
        ),
    )
    source_bindings = StepSourceBindingsConfig(
        bindings=(
            NamedSourceBinding(
                alias="origMemb",
                component_identity=(ComponentSelector(Microscopy.Channel, "3"),),
            ),
        ),
        enabled=True,
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="Watershed", source_bindings=source_bindings),
        3,
        declarations,
        PathPlannerGroupScope.ungrouped(),
        source_bindings=source_bindings,
    )

    assert maps.group_scope == PathPlannerGroupScope.ungrouped()
    cells_ref = ArtifactSpec.output("Cells", ObjectLabelsArtifactType).ref()
    assert maps.outputs[cells_ref].group_keys == ("3",)
    assert maps.outputs[cells_ref].group_component is Microscopy.Channel


def test_image_object_outputs_keep_declared_image_execution_group_scope():
    planner = _artifact_planner_stub()
    planner.ctx.microscope_handler = SimpleNamespace(
        can_resolve_metadata_artifact=lambda artifact_name: artifact_name == "DF_image",
    )
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="Tile_of_grid",
            path="/memory/Tile_of_grid.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/Tile_of_grid_1.pkl"},
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "MeasureObjectIntensity_7_measurements",
                    MeasurementsArtifactType,
                ),
                groups=("2",),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "Tile_of_grid",
                    ObjectLabelsArtifactType,
                    relations=(
                        InputGroupLineageSourceRelation(
                            source=ArtifactSpec.input(
                                "DF_image",
                                ImageArtifactType,
                            ).ref()
                        ),
                    ),
                ),
                invocation_keys=(),
            ),
        ),
        non_plan_consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("DF_image", ImageArtifactType),
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="MeasureObjectIntensity"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("2",),
            component=Microscopy.Channel,
        ),
    )

    measurements_ref = ArtifactSpec.output(
        "MeasureObjectIntensity_7_measurements",
        MeasurementsArtifactType,
    ).ref()
    assert maps.outputs[measurements_ref].group_keys == ("2",)


def test_group_lineage_source_resolves_prior_main_flow_output_without_store_input():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="Tile_of_grid",
            path="/memory/Tile_of_grid.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/Tile_of_grid_1.pkl"},
        ),
    )
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output_inheriting_group_scope(
                    "Filtered_tiles",
                    ObjectLabelsArtifactType,
                    ArtifactSpec.input("Tile_of_grid", ObjectLabelsArtifactType).ref(),
                ),
                groups=("2",),
                invocation_keys=(),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input(
                    "Tile_of_grid",
                    ObjectLabelsArtifactType,
                ),
                invocation_keys=(),
            ),
        ),
    )

    maps = planner.artifacts.compile_plan_maps(
        _resolved_step(name="FilterObjects"),
        3,
        declarations,
        PathPlannerGroupScope.from_raw(
            ("2",),
            component=Microscopy.Channel,
        ),
    )

    assert tuple(maps.inputs) == (
        ArtifactSpec.input("Tile_of_grid", ObjectLabelsArtifactType).ref(),
    )
    filtered_tiles_ref = ArtifactSpec.output(
        "Filtered_tiles",
        ObjectLabelsArtifactType,
    ).ref()
    assert maps.outputs[filtered_tiles_ref].group_keys == ("1",)


def test_resolved_pipeline_owns_invocation_aware_artifact_declarations():
    def identify(image, artifact_name: str):
        return image

    def declarations_for_invocation(invocation, step_context):
        assert step_context.step_name == "identify_cells"
        artifact_name = dict(invocation.kwargs)["artifact_name"]

        @artifact_outputs(ArtifactSpec.output(artifact_name, ObjectLabelsArtifactType))
        def declared_artifact_owner(image):
            return image

        return CallableContract.from_callable(declared_artifact_owner)

    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func=(identify, {"artifact_name": "cells"}),
        group_by=Ungrouped,
        variable_components=(Microscopy.Site,),
        name="identify_cells",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )

    pipeline = ResolvedPipelineDefinition(
        steps=(snapshot,), step_scope_ids={0: "plate::identify_cells"},
        step_provenance={0: {}}, declaration_provider=declarations_for_invocation,
    )
    (declarations,) = pipeline.artifact_graphs
    func_pattern = declarations.pattern
    execution_scope = FunctionStepExecutionScope.require_uniform(
        item.contract for item in func_pattern.iter_items()
    )
    planner.artifact_context = pipeline.artifact_contexts[0]
    assert execution_scope is FunctionStepExecutionScope.AXIS
    output_plan = ArtifactOutputPlan(
        name="cells",
        path="/memory/cells.pkl",
        artifact_type=ObjectLabelsArtifactType,
    )
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        2,
        True,
        func_pattern,
        {},
        {output_plan.ref(): output_plan},
        {},
        PathPlannerGroupScope.ungrouped(),
        declarations=declarations,
    )

    assert list(declarations.outputs) == [
        ArtifactSpec.output("cells", ObjectLabelsArtifactType).ref()
    ]
    assert tuple(
        plan.ref() for plan in compiled.groups[0].invocations[0].artifact_output_plans
    ) == (
        ArtifactSpec.output("cells", ObjectLabelsArtifactType).ref(),
    )


def test_artifact_managed_regular_pattern_preserves_group_by_scope():
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    @artifact_inputs(ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType))
    def filter_objects(image, *, runtime):
        del runtime
        return image

    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func=filter_objects,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="FilterObjects",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )
    input_component_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.from_raw(
                ("1", "2"),
                component=Microscopy.Channel,
            )
        }
    )

    _declarations, _pattern, execution_scope, _contracts = (
        _prepare_step_declarations(planner,
            snapshot,
            2,
        )
    )
    execution_groups = planner.execution_groups.get_execution_groups(
        snapshot,
        input_component_scopes,
    )

    assert execution_groups == PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )
    assert execution_scope is FunctionStepExecutionScope.AXIS

    snapshot.func = {
        "1": [filter_objects],
        "2": [filter_objects],
    }
    _declarations, _pattern, execution_scope, _contracts = (
        _prepare_step_declarations(planner,
            snapshot,
            2,
        )
    )
    execution_groups = planner.execution_groups.get_execution_groups(
        snapshot,
        input_component_scopes,
    )

    assert execution_groups == PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )
    assert execution_scope is FunctionStepExecutionScope.AXIS


def test_adapter_managed_edges_bind_only_compatible_special_parameters():
    labels = ArtifactSpec.input(
        "Nuclei",
        ObjectLabelsArtifactType,
        parameter_name="labels",
    )
    measurements = ArtifactSpec.input("Measurements", MeasurementsArtifactType)

    @artifact_inputs(labels, measurements)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    @special_inputs("labels")
    def consume(image, labels: ObjectLabelValue, *, runtime):
        del labels, runtime
        return image

    input_plans = {
        spec.ref(): ArtifactInputPlan(
            name=spec.name,
            path=f"/memory/{spec.name}.pkl",
            artifact_type=spec.artifact_type,
        )
        for spec in (labels, measurements)
    }
    compiled = compile_function_pattern(consume, input_plans, {})
    compiled = _artifact_planner_stub().artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs=input_plans,
        relation_source_scopes={
            spec.ref(): input_plans[spec.ref()].producer_group_scope()
            for spec in (labels, measurements)
        },
        execution_group_scope=PathPlannerGroupScope.ungrouped(),
        consumer_variable_components=ComponentSet(),
    )

    invocation = next(compiled.iter_invocations())
    adapter = invocation.contract.runtime_adapter
    assert adapter is not None
    assert adapter.manages_artifact_inputs
    assert tuple(
        (edge.spec, edge.spec.parameter_name)
        for edge in invocation.artifact_input_edges
    ) == ((labels, "labels"), (measurements, None))


def test_artifact_managed_regular_pattern_uses_declared_owner_scope():
    nuclei = ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType)

    @artifact_inputs(nuclei)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    def identify_primary_objects(image, *, runtime):
        del runtime
        return image

    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=nuclei.name,
            path="/memory/Nuclei.pkl",
            artifact_type=nuclei.artifact_type,
            group_keys=("1", "2"),
            group_component=Microscopy.Site,
            component_domains=(
                ComponentGroupScope.from_raw(
                    ("1",),
                    component=Microscopy.Channel,
                ),
                ComponentGroupScope.from_raw(
                    ("1", "2"),
                    component=Microscopy.Site,
                ),
            ),
        ),
    )
    snapshot = _resolved_step(
        is_function_step=True,
        func=identify_primary_objects,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="IdentifyPrimaryObjects",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )
    main_flow_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.from_raw(
                ("2", "3"),
                component=Microscopy.Channel,
            )
        }
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        main_flow_scopes,
        contracts=(CallableContract.from_callable(identify_primary_objects),),
    )

    assert scope == PathPlannerGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )


def test_artifact_managed_regular_pattern_unions_compatible_owner_scopes():
    nuclei_1 = ArtifactSpec.input("Nuclei1", ObjectLabelsArtifactType)
    nuclei_2 = ArtifactSpec.input("Nuclei2", ObjectLabelsArtifactType)

    @artifact_inputs(nuclei_1, nuclei_2)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    def relate_objects(image, *, runtime):
        del runtime
        return image

    planner = _artifact_planner_stub()
    for spec, channel in ((nuclei_1, "1"), (nuclei_2, "2")):
        _record_declared_output(
            planner,
            ArtifactOutputPlan(
                name=spec.name,
                path=f"/memory/{spec.name}.pkl",
                artifact_type=spec.artifact_type,
                group_keys=(channel,),
                group_component=Microscopy.Channel,
            ),
        )
    snapshot = _resolved_step(
        is_function_step=True,
        func=relate_objects,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="RelateObjects",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )
    main_flow_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.from_raw(
                ("1", "2"),
                component=Microscopy.Channel,
            )
        }
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        main_flow_scopes,
        contracts=(CallableContract.from_callable(relate_objects),),
    )

    assert scope == PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )


def test_artifact_owner_variable_axis_projects_to_consumer_scope():
    comet_outline = ArtifactSpec.input("CometOutline", ObjectLabelsArtifactType)

    @artifact_inputs(comet_outline)
    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        manages_artifact_inputs=True,
    )
    def measure_object_size_shape(image, *, runtime):
        del runtime
        return image

    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=comet_outline.name,
            path="/memory/CometOutline.pkl",
            artifact_type=comet_outline.artifact_type,
            group_keys=("1", "2"),
            group_component=Microscopy.Site,
        ),
    )
    snapshot = _resolved_step(
        is_function_step=True,
        func=measure_object_size_shape,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="MeasureObjectSizeShape",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )
    main_flow_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.from_raw(
                ("1",),
                component=Microscopy.Channel,
            )
        }
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        main_flow_scopes,
        contracts=(CallableContract.from_callable(measure_object_size_shape),),
    )

    assert scope == PathPlannerGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )


def test_execution_groups_resolve_non_grouped_variable_component_conflicts():
    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site, Microscopy.Channel),
        name="source_bound_cellprofiler_step",
        source_bindings=EMPTY_SOURCE_BINDINGS,
    )

    assert (
        planner.execution_groups.get_execution_groups(snapshot)
        == PathPlannerGroupScope.ungrouped()
    )


def test_non_dict_group_by_declares_dynamic_scope_without_plate_key_lookup():
    planner = _artifact_planner_stub()
    planner.orchestrator = SimpleNamespace(
        get_component_keys=lambda group_by, *, resolved_config: pytest.fail(
            "non-dict group_by must not request plate component keys"
        )
    )
    source_snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="enhance",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )

    source_scope = planner.execution_groups.get_execution_groups(
        source_snapshot,
        PathPlannerComponentScopes.empty(),
    )
    assert source_scope == PathPlannerGroupScope.from_raw(
        (None,),
        component=Microscopy.Channel,
    )


def test_non_dict_group_by_uses_dynamic_source_scope_for_pipeline_start():
    planner = _artifact_planner_stub()
    source_snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="source_loaded_channel_callable",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PIPELINE_START,
    )

    source_scope = planner.execution_groups.get_execution_groups(
        source_snapshot,
        PathPlannerComponentScopes.empty(),
    )
    assert source_scope == PathPlannerGroupScope.from_raw(
        (None,),
        component=Microscopy.Channel,
    )


def test_dict_pattern_group_by_declares_execution_group_component():
    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func={
            "1": lambda image: image,
            "2": lambda image: image,
        },
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="channel_dispatch",
        source_bindings=EMPTY_SOURCE_BINDINGS,
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
    )

    assert scope == PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )


def test_dict_pattern_rejects_group_by_none_execution_component():
    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func={
            "1": lambda image: image,
            "2": lambda image: image,
        },
        group_by=Ungrouped,
        variable_components=(Microscopy.Channel,),
        name="channel_dispatch",
        source_bindings=EMPTY_SOURCE_BINDINGS,
    )

    with pytest.raises(
        ValueError,
        match="dict function pattern without a concrete group_by component",
    ):
        planner.execution_groups.get_execution_groups(
            snapshot,
            PathPlannerComponentScopes.empty(),
        )


def test_execution_groups_reject_grouped_group_by_axis_conflict():
    planner = _artifact_planner_stub()

    composite_snapshot = _resolved_step(
        is_function_step=True,
        func={"1": lambda image: image},
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Channel,),
        name="channel_dispatch",
        source_bindings=EMPTY_SOURCE_BINDINGS,
    )
    with pytest.raises(
        ValueError,
        match="channel_dispatch.*group_by=channel cannot also appear",
    ):
        planner.execution_groups.get_execution_groups(
            composite_snapshot,
            PathPlannerComponentScopes.empty(),
        )


def test_non_dict_group_by_preserves_explicitly_collapsed_input_axis():
    planner = _artifact_planner_stub()
    input_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.ungrouped(),
            Microscopy.Site: PathPlannerGroupScope.from_raw(
                ("1", "2"),
                component=Microscopy.Site,
            ),
        }
    )
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="measure_channel_named_artifacts_over_site_stack",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )

    scope = planner.execution_groups.get_execution_groups(snapshot, input_scopes)

    assert scope == PathPlannerGroupScope.ungrouped()


def test_module_special_outputs_preserve_existing_main_flow_component_scopes():
    measurement_spec = ArtifactSpec.output("Measurements", MeasurementsArtifactType)

    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(measurement_spec)
    def measurement_only(image, *, runtime):
        del runtime
        return image, object()

    compiled_contract = CallableContract.from_callable(measurement_only)
    pattern = CompiledFunctionPattern(
        groups=(
            CompiledFunctionGroup(
                group_key="default",
                invocations=(
                    CompiledFunctionInvocation(
                        key=FunctionInvocationKey.from_contract(
                            compiled_contract,
                            "default",
                            0,
                        ),
                        contract=compiled_contract,
                    ),
                ),
            ),
        ),
        is_grouped=False,
    )
    input_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.from_raw(
                ("1",),
                component=Microscopy.Channel,
            ),
            Microscopy.Site: PathPlannerGroupScope.ungrouped(),
        }
    )
    snapshot = _resolved_step(
        is_function_step=True,
        variable_components=(Microscopy.Channel,),
        group_by=Microscopy.Site,
        name="measurement_only",
    )

    output_scopes = input_scopes.output_after(
        snapshot,
        PathPlannerGroupScope.dynamic(Microscopy.Site),
        pattern,
    )

    assert output_scopes == input_scopes


def test_module_canonical_output_applies_functionstep_component_transformation():
    image_spec = ArtifactSpec.output("Enhanced", ImageArtifactType)

    @artifact_outputs(image_spec)
    def image_output(image):
        return image

    compiled_contract = CallableContract.from_callable(image_output)
    pattern = CompiledFunctionPattern(
        groups=(
            CompiledFunctionGroup(
                group_key="default",
                invocations=(
                    CompiledFunctionInvocation(
                        key=FunctionInvocationKey.from_contract(
                            compiled_contract,
                            "default",
                            0,
                        ),
                        contract=compiled_contract,
                    ),
                ),
            ),
        ),
        is_grouped=False,
    )
    input_scopes = PathPlannerComponentScopes(
        {
            Microscopy.Channel: PathPlannerGroupScope.from_raw(
                ("1",),
                component=Microscopy.Channel,
            ),
            Microscopy.Site: PathPlannerGroupScope.ungrouped(),
        }
    )
    snapshot = _resolved_step(
        is_function_step=True,
        variable_components=(Microscopy.Channel,),
        group_by=Microscopy.Site,
        name="image_output",
    )

    output_scopes = input_scopes.output_after(
        snapshot,
        PathPlannerGroupScope.dynamic(Microscopy.Site),
        pattern,
    )

    assert output_scopes == PathPlannerComponentScopes(
        {
            Microscopy.Site: PathPlannerGroupScope.dynamic(Microscopy.Site),
        }
    )


def test_non_dict_group_by_namespaces_artifact_outputs_with_dynamic_component():
    planner = _artifact_planner_stub()
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=ArtifactSpec.output(
                    "segmentation_masks",
                    ObjectLabelsArtifactType,
                ),
                groups=(None,),
                invocation_keys=(),
            ),
        )
    )
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="single_callable_channel_artifacts",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        input_source=InputSource.PREVIOUS_STEP,
    )

    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        2,
        declarations,
        PathPlannerGroupScope.from_raw(
            (None,),
            component=Microscopy.Channel,
        ),
    )

    output_plan = maps.outputs[
        ArtifactSpec.output("segmentation_masks", ObjectLabelsArtifactType).ref()
    ]
    assert output_plan.group_keys == (None,)
    assert output_plan.group_component is Microscopy.Channel


def test_non_dict_group_by_uses_source_binding_identity_for_pipeline_start_scope():
    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="source_bound_channel_groups",
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias="OrigStain1",
                    component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
                ),
                NamedSourceBinding(
                    alias="OrigStain2",
                    component_identity=(ComponentSelector(Microscopy.Channel, "2"),),
                ),
            ),
        ),
        input_source=InputSource.PIPELINE_START,
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
    )

    assert scope == PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )


@pytest.mark.parametrize("stored_payload", (False, True))
def test_auxiliary_source_does_not_restrict_declared_payload_execution(stored_payload):
    payload = ArtifactSpec.input("ComposedImage", ImageArtifactType)
    prefix = ArtifactSpec.input("FilenameSource", ImageArtifactType)
    saved = ArtifactSpec.output(
        "SavedImage",
        ImageArtifactType,
        relations=(GroupLineageSourceRelation(source=payload.ref()),),
    )

    @artifact_inputs(payload, prefix)
    @artifact_outputs(saved)
    def save_declared_payload(image):
        return image

    planner = _artifact_planner_stub()
    bindings = [
        NamedSourceBinding(
            alias=prefix.name,
            component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
        )
    ]
    if stored_payload:
        _record_declared_output(
            planner,
            ArtifactOutputPlan(
                name=payload.name,
                path="/memory/composed.pkl",
                artifact_type=payload.artifact_type,
                group_keys=("1", "2", "3"),
                group_component=Microscopy.Site,
            ),
        )
    else:
        bindings.append(
            NamedSourceBinding(
                alias=payload.name,
                component_identity=(ComponentSelector(Microscopy.Channel, "3"),),
            )
        )
    snapshot = _resolved_step(
        is_function_step=True,
        func=save_declared_payload,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        source_bindings=StepSourceBindingsConfig(
            enabled=True, bindings=tuple(bindings)
        ),
        input_source=InputSource.PREVIOUS_STEP,
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
        contracts=(CallableContract.from_callable(save_declared_payload),),
    )

    expected = (
        PathPlannerGroupScope.dynamic(Microscopy.Channel)
        if stored_payload
        else PathPlannerGroupScope.from_raw(("3",), component=Microscopy.Channel)
    )
    assert scope == expected
    assert not scope.contains_runtime_key("1") or scope.is_dynamic


def test_main_flow_source_anchor_restricts_execution_to_its_exact_channel():
    planner = _artifact_planner_stub()
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(
            NamedSourceBinding(
                alias="BF_image",
                component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
            ),
            NamedSourceBinding(
                alias="DF_image",
                component_identity=(ComponentSelector(Microscopy.Channel, "2"),),
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
            ),
        ),
    )
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="bf_source_consumer",
        source_bindings=source_bindings,
        input_source=InputSource.PIPELINE_START,
    )
    source_contract = CallableContract.from_callable(lambda image: image)
    source_contract = replace(
        source_contract,
        metadata=replace(
            source_contract.metadata,
            artifact_inputs=(
                ArtifactSpec.input("BF_image", ImageArtifactType),
                ArtifactSpec.input("DF_image", ImageArtifactType),
            ),
        ),
    )

    contract_bindings = CompiledSourceBindingPlan.from_contracts(
        snapshot.source_bindings,
        (source_contract,),
        StepInputDependency.pipeline_start(),
        planner.artifact_context.available_artifacts,
    )
    source_anchor_specs = tuple(
        binding.input_spec() for binding in contract_bindings.primary_plane_bindings
    )
    execution_bindings = contract_bindings.for_artifact_specs(
        source_anchor_specs,
        planner.artifact_context.available_artifacts,
    )
    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
        source_bindings=execution_bindings,
    )

    assert tuple(binding.alias for binding in contract_bindings.bindings) == (
        "BF_image",
        "DF_image",
    )
    assert tuple(binding.alias for binding in execution_bindings.bindings) == (
        "BF_image",
    )
    assert scope == PathPlannerGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )


def test_site_execution_preserves_channel_grouped_producer_and_output_lineage():
    source = ArtifactSpec.input("CropBlue", ImageArtifactType)
    measurements = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
        relations=(
            GroupLineageSourceRelation(source.ref()),
            ImageMeasurementSubjectRelation(source.ref()),
        ),
    )

    @artifact_inputs(source)
    @artifact_outputs(measurements)
    def measure(image, CropBlue):
        del CropBlue
        return image

    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name=source.name,
            path="/memory/CropBlue.pkl",
            artifact_type=source.artifact_type,
            group_keys=("1", "2"),
            group_component=Microscopy.Channel,
            variable_components=(Microscopy.Site,),
            paths_by_group={
                "1": "/memory/CropBlue_channel_1.pkl",
                "2": "/memory/CropBlue_channel_2.pkl",
            },
            producer_step_index=2,
            producer_step_name="Crop",
        ),
    )
    snapshot = _resolved_step(
        name="Measure",
        func=measure,
        group_by=Microscopy.Site,
        variable_components=(Microscopy.Channel,),
    )
    execution_scope = PathPlannerGroupScope.from_raw(
        ("1", "2", "3"),
        component=Microscopy.Site,
    )
    declarations = extract_artifact_declarations(measure)

    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        3,
        declarations,
        execution_scope,
    )
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        3,
        True,
        measure,
        maps.inputs,
        maps.outputs,
        maps.relation_source_scopes,
        maps.group_scope,
        declarations=declarations,
    )

    assert maps.group_scope == execution_scope
    assert maps.inputs[source.ref()].producer_group_scope() == (
        ComponentGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Channel,
        )
    )
    assert PathPlannerGroupScope.from_output_plan(maps.outputs[measurements.ref()]) == (
        execution_scope
    )
    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    assert edge.projection.invocation_scope == ComponentGroupScope.dynamic(
        Microscopy.Site
    )
    assert edge.projection.producer_selection_scope == (
        maps.inputs[source.ref()].producer_group_scope()
    )


def test_execution_anchor_ignores_source_artifact_lineage():
    planner = _artifact_planner_stub()
    original_blue = ArtifactSpec.input("OrigBlue", ImageArtifactType)
    original_red = ArtifactSpec.input("OrigRed", ImageArtifactType)
    rgb_image = ArtifactSpec.input(
        "RGBImage",
        ImageArtifactType,
        relations=(InputGroupLineageSourceRelation(original_red.ref()),),
    )
    planner.artifact_context = replace(
        planner.artifact_context,
        available_artifacts=ArtifactSpecCollection(
            (original_blue, original_red, rgb_image)
        ),
    )
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(
            NamedSourceBinding(
                alias="OrigBlue",
                component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
            ),
            NamedSourceBinding(
                alias="OrigRed",
                component_identity=(ComponentSelector(Microscopy.Channel, "3"),),
                projection_role=SourceProjectionRole.SOURCE_ARTIFACT,
            ),
        ),
    )
    snapshot = _resolved_step(
        source_bindings=source_bindings, input_source=InputSource.PIPELINE_START
    )
    source_contract = CallableContract.from_callable(lambda image: image)
    source_contract = replace(
        source_contract,
        metadata=replace(
            source_contract.metadata,
            artifact_inputs=(original_blue, rgb_image),
        ),
    )

    contract_bindings = CompiledSourceBindingPlan.from_contracts(
        snapshot.source_bindings,
        (source_contract,),
        StepInputDependency.pipeline_start(),
        planner.artifact_context.available_artifacts,
    )
    source_anchor_specs = tuple(
        binding.input_spec() for binding in contract_bindings.primary_plane_bindings
    )
    execution_bindings = contract_bindings.for_artifact_specs(
        source_anchor_specs,
        planner.artifact_context.available_artifacts,
    )

    assert tuple(binding.alias for binding in contract_bindings.bindings) == (
        "OrigBlue",
        "OrigRed",
    )
    assert tuple(binding.alias for binding in execution_bindings.bindings) == (
        "OrigBlue",
    )


def test_runtime_artifact_input_plan_owns_relation_source_scope():
    planner = _artifact_planner_stub()
    original_red = ArtifactSpec.input("OrigRed", ImageArtifactType)
    rgb_image = ArtifactSpec.input(
        "RGBImage",
        ImageArtifactType,
        relations=(InputGroupLineageSourceRelation(original_red.ref()),),
    )
    planner.artifact_context = replace(
        planner.artifact_context,
        available_artifacts=ArtifactSpecCollection((original_red, rgb_image)),
    )
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(
            NamedSourceBinding(
                alias="OrigRed",
                component_identity=(ComponentSelector(Microscopy.Channel, "3"),),
            ),
        ),
    )
    artifact_input = ArtifactInputPlan(
        name=rgb_image.name,
        path="/memory/RGBImage.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2", "3"),
        group_component=Microscopy.Site,
        paths_by_group={
            "1": "/memory/RGBImage_site_1.pkl",
            "2": "/memory/RGBImage_site_2.pkl",
            "3": "/memory/RGBImage_site_3.pkl",
        },
    )
    declarations = ArtifactGraph(
        consumers=(
            ArtifactConsumer(
                spec=rgb_image,
                invocation_keys=(),
            ),
        ),
    )

    relation_scopes = planner.artifacts.relation_source_scopes_by_ref(
        declarations,
        {artifact_input.ref(): artifact_input},
        group_scope=PathPlannerGroupScope.from_raw(
            ("3",),
            component=Microscopy.Channel,
        ),
        source_bindings=source_bindings,
        group_by=Microscopy.Channel,
    )

    assert relation_scopes[rgb_image.ref()] == PathPlannerGroupScope.from_raw(
        ("1", "2", "3"),
        component=Microscopy.Site,
    )


def test_relation_source_scopes_rejects_malformed_exact_input_plan_maps():
    planner = _artifact_planner_stub()
    input_spec = ArtifactSpec.input("RGBImage", ImageArtifactType)
    input_plan = ArtifactInputPlan(
        name=input_spec.name,
        path="/memory/RGBImage.pkl",
        artifact_type=input_spec.artifact_type,
    )
    declarations = ArtifactGraph(
        consumers=(ArtifactConsumer(input_spec, invocation_keys=()),),
    )
    invalid_maps = (
        (
            {input_spec.name: input_plan},
            TypeError,
            "require ArtifactSpecRef keys",
        ),
        (
            {
                input_spec.ref(): ArtifactOutputPlan(
                    name=input_spec.name,
                    path=input_plan.path,
                    artifact_type=input_spec.artifact_type,
                )
            },
            TypeError,
            "require ArtifactInputPlan values",
        ),
        (
            {ArtifactSpec.input("OtherImage", ImageArtifactType).ref(): (input_plan)},
            ValueError,
            "conflicts with plan ref",
        ),
    )

    for artifact_inputs_by_ref, error_type, message in invalid_maps:
        with pytest.raises(error_type, match=message):
            planner.artifacts.relation_source_scopes_by_ref(
                declarations,
                artifact_inputs_by_ref,
                group_scope=PathPlannerGroupScope.ungrouped(),
                source_bindings=EMPTY_SOURCE_BINDINGS,
                group_by=None,
            )


def test_process_artifact_outputs_rejects_malformed_exact_maps():
    planner = _artifact_planner_stub()
    output_spec = ArtifactSpec.output("OutputImage", ImageArtifactType)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=output_spec,
                groups=(None,),
                invocation_keys=(),
            ),
        ),
    )
    input_plan = ArtifactInputPlan(
        name="InputImage",
        path="/memory/InputImage.pkl",
        artifact_type=ImageArtifactType,
    )
    call_kwargs = {
        "execution_scope": FunctionStepExecutionScope.AXIS,
        "source_bindings": EMPTY_SOURCE_BINDINGS,
        "variable_components": ComponentSet(),
    }

    with pytest.raises(TypeError, match="artifact input maps require ArtifactSpecRef"):
        planner.artifacts.process_artifact_outputs(
            declarations,
            3,
            artifact_inputs={input_plan.name: input_plan},
            **call_kwargs,
        )

    invalid_output_groups = (
        (
            {output_spec.name: PathPlannerGroupScope.ungrouped()},
            TypeError,
            "output-group maps require ArtifactSpecRef keys",
        ),
        (
            {output_spec.ref(): (None,)},
            TypeError,
            "output-group maps require PathPlannerGroupScope values",
        ),
        (
            {
                ArtifactSpec.output("OtherOutput", ImageArtifactType).ref(): (
                    PathPlannerGroupScope.ungrouped()
                )
            },
            ValueError,
            "is not an exact declared output",
        ),
    )
    for output_groups, error_type, message in invalid_output_groups:
        with pytest.raises(error_type, match=message):
            planner.artifacts.process_artifact_outputs(
                declarations,
                3,
                output_groups,
                artifact_inputs={},
                **call_kwargs,
            )


def test_artifact_graph_output_groups_validates_exact_partial_map() -> None:
    first = ArtifactSpec.output("First", ImageArtifactType)
    second = ArtifactSpec.output("Second", ObjectLabelsArtifactType)
    graph = ArtifactGraph(
        producers=(
            ArtifactProducer(first, ("first-old",), ()),
            ArtifactProducer(second, ("second-old",), ()),
        ),
    )

    updated = graph.with_output_groups({first.ref(): ("first-new", "first-new")})

    assert updated.producers[0].groups == ("first-new",)
    assert updated.producers[1].groups == ("second-old",)

    invalid_maps = (
        (
            {first.name: ("first-new",)},
            TypeError,
            "require ArtifactSpecRef keys",
        ),
        (
            {ArtifactSpec.output("Unknown", ImageArtifactType).ref(): ("unknown",)},
            ValueError,
            "is not an exact declared output",
        ),
        (
            {first.ref(): "first-new"},
            TypeError,
            "not a string",
        ),
        (
            {first.ref(): 1},
            TypeError,
            "must be iterable",
        ),
        (
            {first.ref(): ("first-new", 1)},
            TypeError,
            "require string or None keys",
        ),
    )
    for output_groups, error_type, message in invalid_maps:
        with pytest.raises(error_type, match=message):
            graph.with_output_groups(output_groups)


def test_non_dict_group_by_ignores_source_binding_identity_for_other_components():
    planner = _artifact_planner_stub()
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Site,
        variable_components=(Microscopy.Channel,),
        name="source_bound_site_groups",
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(
                NamedSourceBinding(
                    alias="OrigStain1",
                    component_identity=(ComponentSelector(Microscopy.Channel, "1"),),
                ),
                NamedSourceBinding(
                    alias="OrigStain2",
                    component_identity=(ComponentSelector(Microscopy.Channel, "2"),),
                ),
            ),
        ),
        input_source=InputSource.PIPELINE_START,
    )

    scope = planner.execution_groups.get_execution_groups(
        snapshot,
        PathPlannerComponentScopes.empty(),
    )

    assert scope == PathPlannerGroupScope.from_raw(
        (None,),
        component=Microscopy.Site,
    )


def test_compiled_group_by_preserves_dynamic_execution_scope():
    planner = _artifact_planner_stub()
    planner.cfg = PathConfigStub(sub_dir="images", output_dir_suffix="_generated")
    planner.plans[3].group_by = Microscopy.Channel
    planner.plans[3].variable_components = (Microscopy.Site,)
    snapshot = _resolved_step(
        is_function_step=True,
        func=lambda image: image,
        group_by=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        name="measure_after_channel_collapse",
        input_source=InputSource.PREVIOUS_STEP,
    )
    artifact_maps = ArtifactPlanMaps(
        declarations=ArtifactGraph.empty(),
        group_scope=PathPlannerGroupScope.dynamic(Microscopy.Channel),
        inputs={},
        outputs={},
        relation_source_scopes={},
        source_binding_plan=CompiledSourceBindingPlan.empty(),
        source_universe_plan=CompiledSourceUniversePlan.empty(),
    )

    planner.steps.update_core_step_plan(
        snapshot,
        3,
        StepInputDependency.step_output(
            source_step_index=2,
            source_step_scope_id="plate::functionstep_2",
        ),
        Path("/input"),
        Path("/output"),
        artifact_maps,
        None,
    )

    assert planner.plans[3].group_by is Microscopy.Channel
    assert planner.plans[3].execution_group_scope == PathPlannerGroupScope.dynamic(
        Microscopy.Channel
    )
    assert planner.plans[3].analysis_results_dir == "/data/plate1_generated/analysis"


def test_artifact_input_plan_requires_an_exact_producer_kind():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="nuclei",
            path="/memory/nuclei.pkl",
            artifact_type=ObjectLabelsArtifactType,
            producer_step_index=1,
            producer_step_name="identify",
        ),
    )

    with pytest.raises(MissingArtifactInputError, match="needs artifact input"):
        planner.artifacts.process_artifact_inputs(
            ArtifactGraph(
                consumers=(
                    ArtifactConsumer(
                        spec=ArtifactSpec.input("nuclei", MeasurementsArtifactType),
                        invocation_keys=(),
                    ),
                )
            ),
            consumer_scope=PathPlannerGroupScope.ungrouped(),
            sid=2,
            step_name="measure",
            source_bindings=EMPTY_SOURCE_BINDINGS,
            variable_components=ComponentSet(),
            execution_scope=FunctionStepExecutionScope.AXIS,
        )


def test_artifact_input_plan_rejects_corrupt_exact_producer_kind():
    planner = _artifact_planner_stub()
    input_spec = ArtifactSpec.input("nuclei", MeasurementsArtifactType)
    producer_ref = input_spec.ref().for_plan_type(ArtifactOutputPlan)
    planner.declared[producer_ref] = ArtifactOutputPlan(
        name="nuclei",
        path="/memory/nuclei.pkl",
        artifact_type=ObjectLabelsArtifactType,
        producer_step_index=1,
        producer_step_name="identify",
    )

    with pytest.raises(ValueError, match="expects measurements"):
        planner.artifacts.process_artifact_inputs(
            ArtifactGraph(
                consumers=(
                    ArtifactConsumer(
                        spec=input_spec,
                        invocation_keys=(),
                    ),
                )
            ),
            consumer_scope=PathPlannerGroupScope.ungrouped(),
            sid=2,
            step_name="measure",
            source_bindings=EMPTY_SOURCE_BINDINGS,
            variable_components=ComponentSet(),
            execution_scope=FunctionStepExecutionScope.AXIS,
        )


def test_same_name_source_and_output_use_exact_typed_graph_identity():
    planner = _artifact_planner_stub()
    invocation_key = FunctionInvocationKey("identify_primary_objects", "2", 0)
    image_input = ArtifactSpec.input("PH3", ImageArtifactType)
    object_output = ArtifactSpec.output("PH3", ObjectLabelsArtifactType)
    declarations = ArtifactGraph(
        producers=(
            ArtifactProducer(
                spec=object_output,
                groups=("2",),
                invocation_keys=(invocation_key,),
            ),
        ),
        consumers=(
            ArtifactConsumer(
                spec=image_input,
                invocation_keys=(invocation_key,),
            ),
        ),
    )
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(NamedSourceBinding(alias="PH3"),),
    )

    inputs = planner.artifacts.process_artifact_inputs(
        declarations,
        sid=2,
        consumer_scope=PathPlannerGroupScope.ungrouped(),
        source_bindings=source_bindings,
        variable_components=ComponentSet(),
        step_name="IdentifyPrimaryObjects",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )
    outputs = planner.artifacts.process_artifact_outputs(
        declarations,
        sid=2,
        artifact_inputs=inputs,
        source_bindings=source_bindings,
        variable_components=ComponentSet(),
        step_name="IdentifyPrimaryObjects",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    assert inputs == {}
    assert tuple(declarations.inputs) == (image_input.ref(),)
    assert tuple(declarations.outputs) == (object_output.ref(),)
    assert tuple(planner.declared) == (object_output.ref(),)

    matching_inputs = planner.artifacts.process_artifact_inputs(
        ArtifactGraph(
            consumers=(
                ArtifactConsumer(
                    spec=object_output.for_plan_type(ArtifactInputPlan),
                    invocation_keys=(invocation_key,),
                ),
            )
        ),
        sid=3,
        consumer_scope=PathPlannerGroupScope.ungrouped(),
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet(),
        step_name="ConsumePH3Objects",
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    object_input_ref = object_output.for_plan_type(ArtifactInputPlan).ref()
    assert (
        matching_inputs[object_input_ref].ref()
        == object_output.for_plan_type(ArtifactInputPlan).ref()
    )
    assert outputs[object_output.ref()].ref() == object_output.ref()


def test_artifact_input_plan_preserves_single_grouped_producer_scope():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="illumination",
            path="/memory/illumination.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1",),
            group_component=Microscopy.Channel,
            paths_by_group={"1": "/memory/illumination_channel_1.pkl"},
            producer_step_index=1,
            producer_step_name="calculate_illumination",
        ),
    )

    inputs = planner.artifacts.process_artifact_inputs(
        ArtifactGraph(
            consumers=(
                ArtifactConsumer(
                    spec=ArtifactSpec.input("illumination", ImageArtifactType),
                    invocation_keys=(),
                ),
            )
        ),
        consumer_scope=PathPlannerGroupScope.from_raw(
            ("2", "3"),
            component=Microscopy.Site,
        ),
        sid=2,
        step_name="apply_illumination",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet(),
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    illumination_ref = ArtifactSpec.input("illumination", ImageArtifactType).ref()
    plan = inputs[illumination_ref]
    assert plan.group_keys == ("1",)
    assert plan.group_component is Microscopy.Channel
    assert plan.path == "/memory/illumination_channel_1.pkl"
    assert plan.paths_by_group == {"1": "/memory/illumination_channel_1.pkl"}


@pytest.mark.parametrize(
    ("available", "required", "contains"),
    (
        (PathPlannerGroupScope.ungrouped(), PathPlannerGroupScope.ungrouped(), True),
        (
            PathPlannerGroupScope.dynamic(Microscopy.Channel),
            PathPlannerGroupScope.dynamic(Microscopy.Channel),
            True,
        ),
        (
            PathPlannerGroupScope.dynamic(Microscopy.Channel),
            PathPlannerGroupScope.from_raw(("1",), component=Microscopy.Channel),
            True,
        ),
        (
            PathPlannerGroupScope.from_raw(("1", "2"), component=Microscopy.Channel),
            PathPlannerGroupScope.from_raw(("2",), component=Microscopy.Channel),
            True,
        ),
        (
            PathPlannerGroupScope.from_raw(("1",), component=Microscopy.Channel),
            PathPlannerGroupScope.dynamic(Microscopy.Channel),
            False,
        ),
        (
            PathPlannerGroupScope.dynamic(Microscopy.Channel),
            PathPlannerGroupScope.dynamic(Microscopy.Site),
            False,
        ),
    ),
)
def test_component_group_scope_contains_exact_required_scope(
    available: PathPlannerGroupScope,
    required: PathPlannerGroupScope,
    contains: bool,
) -> None:
    assert available.contains_scope(required) is contains


def test_component_group_scope_selects_runtime_key_from_static_domain():
    scope = ComponentGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )

    assert scope.select_runtime_key("2") == "2"
    with pytest.raises(ValueError, match="do not contain runtime key"):
        scope.select_runtime_key("3")


def test_compilation_rejects_ambiguous_cross_component_artifact_selection():
    input_spec = ArtifactSpec.input("image", ImageArtifactType)

    @artifact_inputs(input_spec)
    def consume(main_image, image):
        del image
        return main_image

    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="image",
            path="/memory/image.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1", "2"),
            group_component=Microscopy.Channel,
            paths_by_group={
                "1": "/memory/image_channel_1.pkl",
                "2": "/memory/image_channel_2.pkl",
            },
            producer_step_index=1,
            producer_step_name="producer",
        ),
    )
    declarations = ArtifactGraph(
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("image", ImageArtifactType),
                invocation_keys=(
                    FunctionInvocationKey("consumer", DEFAULT_GROUP_KEY, 0),
                ),
            ),
        )
    )

    snapshot = _resolved_step(
        name="consumer",
        func=consume,
        group_by=Ungrouped,
        variable_components=(Microscopy.Site,),
    )
    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        3,
        declarations,
        PathPlannerGroupScope.ungrouped(),
    )

    with pytest.raises(ValueError, match="no exact relation-owned selection"):
        planner.artifacts.build_step_compiled_function_pattern(
            snapshot,
            3,
            True,
            consume,
            maps.inputs,
            maps.outputs,
            maps.relation_source_scopes,
            maps.group_scope,
            declarations=extract_artifact_declarations(consume, invocation_contract_provider=planner.invocation_contract_provider, step_context=planner.artifact_context),
        )


def test_compilation_selects_exact_singleton_cross_component_artifact():
    input_spec = ArtifactSpec.input("image", ImageArtifactType)

    @artifact_inputs(input_spec)
    def consume(main_image, image):
        del image
        return main_image

    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="image",
            path="/memory/image_channel_2.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("2",),
            group_component=Microscopy.Channel,
            paths_by_group={"2": "/memory/image_channel_2.pkl"},
            producer_step_index=1,
            producer_step_name="producer",
        ),
    )
    declarations = ArtifactGraph(
        consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("image", ImageArtifactType),
                invocation_keys=(
                    FunctionInvocationKey("consumer", DEFAULT_GROUP_KEY, 0),
                ),
            ),
        )
    )

    snapshot = _resolved_step(
        name="consumer",
        func=consume,
        group_by=Ungrouped,
        variable_components=(Microscopy.Site,),
    )
    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        3,
        declarations,
        PathPlannerGroupScope.ungrouped(),
    )

    producer_scope = maps.inputs[input_spec.ref()].producer_group_scope()
    assert producer_scope.keys == ("2",)
    assert producer_scope.component is Microscopy.Channel
    compiled = planner.artifacts.build_step_compiled_function_pattern(
        snapshot,
        3,
        True,
        consume,
        maps.inputs,
        maps.outputs,
        maps.relation_source_scopes,
        maps.group_scope,
        declarations=extract_artifact_declarations(consume, invocation_contract_provider=planner.invocation_contract_provider, step_context=planner.artifact_context),
    )

    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    assert edge.projection.producer_selection_scope == producer_scope


def test_compilation_accepts_exact_single_artifact_from_another_group():
    owner_spec = ArtifactSpec.input("relationship_owner", ImageArtifactType)
    input_spec = ArtifactSpec.input(
        "relationships",
        RelationshipsArtifactType,
        relations=(InputGroupLineageSourceRelation(owner_spec.ref()),),
    )

    @artifact_inputs(input_spec)
    def consume(main_image, relationships):
        del relationships
        return main_image

    input_plan = ArtifactInputPlan(
        name="relationships",
        path="/memory/relationships_channel_2.pkl",
        artifact_type=RelationshipsArtifactType,
        group_keys=("2",),
        group_component=Microscopy.Channel,
        paths_by_group={"2": "/memory/relationships_channel_2.pkl"},
    )
    compiled = compile_function_pattern(
        consume,
        {plan.ref(): plan for plan in (input_plan,)},
        {},
    )
    compiled = _artifact_planner_stub().artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes={
            input_spec.ref(): input_plan.producer_group_scope(),
            owner_spec.ref(): PathPlannerGroupScope.from_raw(
                ("2",),
                component=Microscopy.Channel,
            ),
        },
        execution_group_scope=PathPlannerGroupScope.ungrouped(),
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
    )
    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    assert edge.projection.invocation_scope.is_ungrouped
    assert edge.projection.producer_selection_scope == (
        input_plan.producer_group_scope()
    )


def test_realized_source_scopes_compile_cross_group_artifact_consumption():
    planner = _artifact_planner_stub()
    planner.plans[4] = CompiledStepPlan(
        step_index=4,
        step_scope_id="plate::functionstep_4",
        step_name="consume",
        axis_id="A01",
    )
    planner.session.realized_source_metadata = (
        {"source_alias": "Blue", "channel": "1"},
        {"source_alias": "Green", "channel": "2"},
    )
    broad_channel_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )

    def compile_source_producer(
        *,
        step_index: int,
        alias: str,
        output_name: str,
        expected_group: str,
    ) -> ArtifactSpec:
        source = ArtifactSpec.input(alias, ImageArtifactType)
        output = ArtifactSpec.output_inheriting_group_scope(
            output_name,
            ObjectLabelsArtifactType,
            source,
        )

        @artifact_inputs(source)
        @artifact_outputs(output)
        def produce(image, source_value):
            del source_value
            return image

        source_bindings = StepSourceBindingsConfig(
            enabled=True,
            bindings=(NamedSourceBinding(alias=alias),),
        )
        snapshot = _resolved_step(
            name=f"produce_{output_name}",
            func=produce,
            source_bindings=source_bindings,
            input_source=InputSource.PIPELINE_START,
        )
        execution_scope = planner.execution_groups.get_execution_groups(
            snapshot,
            PathPlannerComponentScopes.empty(),
            source_bindings=source_bindings,
        )
        declarations = (
            extract_artifact_declarations(produce)
        )
        maps = planner.artifacts.compile_plan_maps(
            snapshot,
            step_index,
            declarations,
            execution_scope,
            source_bindings=source_bindings,
        )

        assert maps.group_scope == PathPlannerGroupScope.from_raw(
            (expected_group,),
            component=Microscopy.Channel,
        )
        return output

    nuclei_output = compile_source_producer(
        step_index=2,
        alias="Blue",
        output_name="Nuclei",
        expected_group="1",
    )
    ph3_output = compile_source_producer(
        step_index=3,
        alias="Green",
        output_name="PH3",
        expected_group="2",
    )
    nuclei_input = nuclei_output.for_plan_type(ArtifactInputPlan)
    ph3_input = ph3_output.for_plan_type(ArtifactInputPlan)
    relationships = ArtifactSpec.output(
        "Nuclei_PH3_relationships",
        RelationshipsArtifactType,
        relations=(
            GroupLineageSourceRelation(nuclei_input.ref()),
            GroupLineageSourceRelation(ph3_input.ref()),
        ),
    )

    @artifact_inputs(nuclei_input, ph3_input)
    @artifact_outputs(relationships)
    def consume(image, Nuclei, PH3):
        del Nuclei, PH3
        return image

    snapshot = _resolved_step(name="consume", func=consume)
    declarations = extract_artifact_declarations(consume)
    maps = planner.artifacts.compile_plan_maps(
        snapshot,
        4,
        declarations,
        broad_channel_scope,
    )
    compiled = compile_function_pattern(consume, maps.inputs, maps.outputs)
    compiled = planner.artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs=maps.inputs,
        relation_source_scopes=maps.relation_source_scopes,
        execution_group_scope=maps.group_scope,
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
    )

    assert maps.group_scope == PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )
    edges = {
        edge.spec.name: edge
        for edge in next(compiled.iter_invocations()).artifact_input_edges
    }
    assert edges["Nuclei"].projection.producer_selection_scope.keys == ("1",)
    assert edges["PH3"].projection.producer_selection_scope.keys == ("2",)


def test_compilation_rejects_declared_lineage_from_multi_group_producer():
    source_spec = ArtifactSpec.input("site_source", ImageArtifactType)
    image_spec = ArtifactSpec.input(
        "image",
        ImageArtifactType,
        relations=(InputGroupLineageSourceRelation(source_spec.ref()),),
    )

    @artifact_inputs(image_spec, source_spec)
    def consume(main_image, image, site_source):
        del image, site_source
        return main_image

    image_plan = ArtifactInputPlan(
        name="image",
        path="/memory/image.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=Microscopy.Channel,
        paths_by_group={
            "1": "/memory/image_channel_1.pkl",
            "2": "/memory/image_channel_2.pkl",
        },
    )
    source_plan = ArtifactInputPlan(
        name="site_source",
        path="/memory/site_source.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=Microscopy.Site,
        paths_by_group={"1": "/memory/site_source_1.pkl"},
    )
    input_plans = {
        image_plan.ref(): image_plan,
        source_plan.ref(): source_plan,
    }
    compiled = compile_function_pattern(consume, input_plans, {})
    planner = _artifact_planner_stub()

    with pytest.raises(ValueError, match="no exact relation-owned selection"):
        planner.artifacts.compile_invocation_input_edges(
            compiled,
            artifact_inputs=input_plans,
            relation_source_scopes={
                image_spec.ref(): image_plan.producer_group_scope(),
                source_spec.ref(): source_plan.producer_group_scope(),
            },
            execution_group_scope=PathPlannerGroupScope.ungrouped(),
            consumer_variable_components=ComponentSet((Microscopy.Site,)),
        )


def test_artifact_plan_rejects_group_component_as_variable_axis():
    with pytest.raises(ValueError, match="cannot group by.*site.*variable component"):
        ArtifactInputPlan(
            name="objects",
            path="/memory/objects.pkl",
            artifact_type=ObjectLabelsArtifactType,
            group_keys=(None,),
            group_component=Microscopy.Site,
            variable_components=(Microscopy.Site,),
        )


def test_artifact_input_plan_preserves_multi_grouped_producer_across_components():
    planner = _artifact_planner_stub()
    _record_declared_output(
        planner,
        ArtifactOutputPlan(
            name="illumination",
            path="/memory/illumination_channel_1.pkl",
            artifact_type=ImageArtifactType,
            group_keys=("1", "2"),
            group_component=Microscopy.Channel,
            paths_by_group={
                "1": "/memory/illumination_channel_1.pkl",
                "2": "/memory/illumination_channel_2.pkl",
            },
            producer_step_index=1,
            producer_step_name="calculate_illumination",
        ),
    )

    inputs = planner.artifacts.process_artifact_inputs(
        ArtifactGraph(
            consumers=(
                ArtifactConsumer(
                    spec=ArtifactSpec.input("illumination", ImageArtifactType),
                    invocation_keys=(),
                ),
            )
        ),
        consumer_scope=PathPlannerGroupScope.from_raw(
            ("1", "2"),
            component=Microscopy.Site,
        ),
        sid=2,
        step_name="apply_illumination",
        source_bindings=EMPTY_SOURCE_BINDINGS,
        variable_components=ComponentSet(),
        execution_scope=FunctionStepExecutionScope.AXIS,
    )

    illumination_ref = ArtifactSpec.input("illumination", ImageArtifactType).ref()
    plan = inputs[illumination_ref]
    assert plan.group_keys == ("1", "2")
    assert plan.group_component is Microscopy.Channel
    assert plan.paths_by_group == {
        "1": "/memory/illumination_channel_1.pkl",
        "2": "/memory/illumination_channel_2.pkl",
    }


def test_realized_component_domain_does_not_replace_dynamic_projection_coordinate():
    source_spec = ArtifactSpec.input("source", ImageArtifactType)
    illumination_spec = ArtifactSpec.input(
        "illumination",
        ImageArtifactType,
        relations=(InputStackBroadcastSourceRelation(source_spec.ref()),),
    )

    @artifact_inputs(illumination_spec, source_spec)
    def apply(image, illumination):
        del illumination
        return image

    input_plan = ArtifactInputPlan(
        name="illumination",
        path="/memory/illumination_channel_1.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1", "2"),
        group_component=Microscopy.Channel,
        variable_components=(Microscopy.Site,),
        paths_by_group={
            "1": "/memory/illumination_channel_1.pkl",
            "2": "/memory/illumination_channel_2.pkl",
        },
    )
    compiled = compile_function_pattern(
        apply,
        {plan.ref(): plan for plan in (input_plan,)},
        {},
    )
    planner = _artifact_planner_stub()
    planner.session.realized_source_metadata = tuple(
        {"source_alias": "source", "site": str(site)} for site in range(1, 4)
    )
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(NamedSourceBinding(alias="source"),),
    )

    compiled = planner.artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes={
            illumination_spec.ref(): input_plan.producer_group_scope(),
            source_spec.ref(): PathPlannerGroupScope.dynamic(Microscopy.Site),
        },
        execution_group_scope=PathPlannerGroupScope.dynamic(Microscopy.Site),
        consumer_variable_components=ComponentSet((Microscopy.Channel,)),
        source_bindings=source_bindings,
        available_artifacts=ArtifactSpecCollection((source_spec, illumination_spec)),
    )
    edge = next(compiled.iter_invocations()).artifact_input_edges[0]

    assert edge.storage_plan.producer_group_scope() == input_plan.producer_group_scope()
    assert edge.projection.producer_selection_scope == (
        edge.storage_plan.producer_group_scope()
    )
    assert edge.projection.invocation_scope == ComponentGroupScope.dynamic(
        Microscopy.Site
    )
    assert edge.projection.component_scope(Microscopy.Site) == (
        ComponentGroupScope.dynamic(Microscopy.Site)
    )


def test_runtime_selects_inputs_from_exact_grouped_invocation_edges():
    planner = _artifact_planner_stub()
    first_spec = ArtifactSpec.input("IllumStain1", ImageArtifactType)
    second_spec = ArtifactSpec.input("IllumStain2", ImageArtifactType)

    @artifact_inputs(first_spec)
    def apply_first(image):
        return image

    @artifact_inputs(second_spec)
    def apply_second(image):
        return image

    first = ArtifactInputPlan(
        name="IllumStain1",
        path="/memory/IllumStain1.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("1",),
        group_component=Microscopy.Channel,
    )
    second = ArtifactInputPlan(
        name="IllumStain2",
        path="/memory/IllumStain2.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("2",),
        group_component=Microscopy.Channel,
    )
    execution_scope = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )
    storage = {first.ref(): first, second.ref(): second}
    compiled = compile_function_pattern(
        {"1": apply_first, "2": apply_second},
        storage,
        {},
    )
    compiled = planner.artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs=storage,
        relation_source_scopes={
            first_spec.ref(): first.producer_group_scope(),
            second_spec.ref(): second.producer_group_scope(),
        },
        execution_group_scope=execution_scope,
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
    )
    execution_plan = CompiledStepPlan(
        step_index=2,
        step_scope_id="plate::functionstep_2",
        step_name="CorrectIlluminationApply",
        axis_id="A01",
        artifact_inputs=storage,
        execution_group_scope=execution_scope,
        compiled_function_pattern=compiled,
    )
    invocations = tuple(compiled.iter_invocations())
    first_plans = invocations[0].select_inputs(storage)
    second_plans = invocations[1].select_inputs(storage)

    assert tuple(
        edge.storage_plan.name
        for edge in first_plans.values()
        if edge.storage_plan is not None
    ) == (first.name,)
    assert tuple(
        edge.storage_plan.name
        for edge in second_plans.values()
        if edge.storage_plan is not None
    ) == (second.name,)
    first_edge = next(iter(first_plans.values()))
    second_edge = next(iter(second_plans.values()))
    assert first_edge.projection is not None
    assert second_edge.projection is not None
    assert first_edge.projection.invocation_scope == (
        ComponentGroupScope.from_raw(
            ("1",),
            component=Microscopy.Channel,
        )
    )
    assert second_edge.projection.invocation_scope == (
        ComponentGroupScope.from_raw(
            ("2",),
            component=Microscopy.Channel,
        )
    )


def test_grouped_invocation_is_independent_of_source_artifact_domain():
    input_spec = ArtifactSpec.input("Objects1", ObjectLabelsArtifactType)

    @artifact_inputs(input_spec)
    def consume(image, Objects1):
        del Objects1
        return image

    input_plan = ArtifactInputPlan(
        name=input_spec.name,
        path="/memory/Objects1.pkl",
        artifact_type=input_spec.artifact_type,
        group_keys=("1",),
        group_component=Microscopy.Channel,
    )
    invocation_scope = PathPlannerGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )
    producer_domain = PathPlannerGroupScope.from_raw(
        ("3",),
        component=Microscopy.Channel,
    )
    invocation = next(
        compile_function_pattern(
            {"1": consume},
            {plan.ref(): plan for plan in (input_plan,)},
            {},
        ).iter_invocations()
    )

    component_scopes = PathPlannerArtifactStage.exact_component_scopes(
        (producer_domain,),
        (),
        component_domains=(producer_domain,),
        invocation_scope=invocation_scope,
        invocation=invocation,
        artifact_ref=input_spec.ref(),
    )

    assert component_scopes == (producer_domain,)


def test_fixed_producer_coordinate_precedes_consumer_group_lineage():
    input_spec = ArtifactSpec.input("Nuclei", ObjectLabelsArtifactType)

    @artifact_inputs(input_spec)
    def consume(image, Nuclei):
        del Nuclei
        return image

    input_plan = ArtifactInputPlan(
        name=input_spec.name,
        path="/memory/Nuclei.pkl",
        artifact_type=input_spec.artifact_type,
    )
    invocation = next(
        compile_function_pattern(
            {"2": consume},
            {plan.ref(): plan for plan in (input_plan,)},
            {},
        ).iter_invocations()
    )
    producer_channel = PathPlannerGroupScope.from_raw(
        ("1",),
        component=Microscopy.Channel,
    )
    consumer_channel = PathPlannerGroupScope.from_raw(
        ("2",),
        component=Microscopy.Channel,
    )

    component_scopes = PathPlannerArtifactStage.exact_component_scopes(
        (producer_channel,),
        (consumer_channel,),
        component_domains=(producer_channel,),
        invocation_scope=consumer_channel,
        invocation=invocation,
        artifact_ref=input_spec.ref(),
    )

    assert component_scopes == (producer_channel,)


def test_relation_selects_one_coordinate_from_multi_coordinate_producer_domain():
    input_spec = ArtifactSpec.input("Objects", ObjectLabelsArtifactType)

    @artifact_inputs(input_spec)
    def consume(image, Objects):
        del Objects
        return image

    input_plan = ArtifactInputPlan(
        name=input_spec.name,
        path="/memory/Objects.pkl",
        artifact_type=input_spec.artifact_type,
    )
    invocation = next(
        compile_function_pattern(
            {"2": consume},
            {plan.ref(): plan for plan in (input_plan,)},
            {},
        ).iter_invocations()
    )
    producer_domain = PathPlannerGroupScope.from_raw(
        ("1", "2"),
        component=Microscopy.Channel,
    )
    selected_channel = PathPlannerGroupScope.from_raw(
        ("2",),
        component=Microscopy.Channel,
    )

    component_scopes = PathPlannerArtifactStage.exact_component_scopes(
        (producer_domain,),
        (selected_channel,),
        component_domains=(producer_domain,),
        invocation_scope=selected_channel,
        invocation=invocation,
        artifact_ref=input_spec.ref(),
    )

    assert component_scopes == (selected_channel,)


def test_produced_artifact_projection_does_not_revalidate_source_binding_domain():
    source = ArtifactSpec.input("OrigMito", ImageArtifactType)
    consumed = ArtifactSpec.input(
        "Cells",
        ObjectLabelsArtifactType,
        relations=(InputGroupLineageSourceRelation(source.ref()),),
    )

    @artifact_inputs(consumed)
    def relate_objects(image, Cells):
        del Cells
        return image

    input_plan = ArtifactInputPlan(
        name=consumed.name,
        path="/memory/Cells.pkl",
        artifact_type=consumed.artifact_type,
        group_keys=("3",),
        group_component=Microscopy.Channel,
        source_step_id=4,
    )
    compiled = compile_function_pattern(
        {"5": relate_objects},
        {plan.ref(): plan for plan in (input_plan,)},
        {},
    )
    source_bindings = StepSourceBindingsConfig(
        enabled=True,
        bindings=(
            NamedSourceBinding(
                alias=source.name,
                component_identity=(ComponentSelector(Microscopy.Channel, "5"),),
            ),
        ),
    )

    compiled = _artifact_planner_stub().artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes={source.ref(): input_plan.producer_group_scope()},
        execution_group_scope=PathPlannerGroupScope.from_raw(
            ("5",),
            component=Microscopy.Channel,
        ),
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
        source_bindings=source_bindings,
        available_artifacts=ArtifactSpecCollection((source, consumed)),
    )

    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    assert edge.projection.component_scope(Microscopy.Channel) == (
        ComponentGroupScope.from_raw(("3",), component=Microscopy.Channel)
    )


def test_non_dict_artifact_input_uses_function_step_execution_scope():
    input_spec = ArtifactSpec.input("positions", SpecialArtifactType)

    @artifact_inputs(input_spec)
    def assemble(image, positions):
        del positions
        return image

    input_plan = ArtifactInputPlan(
        name="positions",
        path="/memory/positions.pkl",
        artifact_type=SpecialArtifactType,
        group_keys=(None,),
        group_component=Microscopy.Channel,
    )
    execution_scope = PathPlannerGroupScope.dynamic(Microscopy.Channel)
    compiled = compile_function_pattern(
        assemble,
        {plan.ref(): plan for plan in (input_plan,)},
        {},
    )

    compiled = _artifact_planner_stub().artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes={
            input_spec.ref(): input_plan.producer_group_scope(),
        },
        execution_group_scope=execution_scope,
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
    )

    edge = next(compiled.iter_invocations()).artifact_input_edges[0]
    expected_scope = ComponentGroupScope.dynamic(Microscopy.Channel)
    assert edge.projection.invocation_scope == expected_scope
    assert edge.projection.producer_selection_scope == expected_scope


def test_grouped_invocations_keep_distinct_edges_for_same_artifact_ref():
    planner = _artifact_planner_stub()
    mask_name = "CropBlue__crop_mask"
    mask_spec = ArtifactSpec.input(mask_name, ImageArtifactType)

    @artifact_inputs(mask_spec)
    def crop_green(image):
        return image

    @artifact_inputs(mask_spec)
    def crop_red(image):
        return image

    input_plan = ArtifactInputPlan(
        name=mask_name,
        path="/memory/crop_mask.pkl",
        artifact_type=ImageArtifactType,
        group_keys=("2", "3"),
        group_component=Microscopy.Channel,
        paths_by_group={
            "2": "/memory/crop_mask_2.pkl",
            "3": "/memory/crop_mask_3.pkl",
        },
    )
    compiled = compile_function_pattern(
        {"2": crop_green, "3": crop_red},
        {plan.ref(): plan for plan in (input_plan,)},
        {},
    )
    compiled = planner.artifacts.compile_invocation_input_edges(
        compiled,
        artifact_inputs={input_plan.ref(): input_plan},
        relation_source_scopes={
            mask_spec.ref(): input_plan.producer_group_scope(),
        },
        execution_group_scope=PathPlannerGroupScope.from_raw(
            ("2", "3"),
            component=Microscopy.Channel,
        ),
        consumer_variable_components=ComponentSet((Microscopy.Site,)),
    )
    edges = compiled.artifact_input_edges_by_key()

    assert len(edges) == 2
    assert tuple(
        edge.projection.producer_selection_scope.keys for edge in edges.values()
    ) == (("2",), ("3",))
    assert len({key.invocation_key for key in edges}) == 2
    assert {edge.spec.ref() for edge in edges.values()} == {mask_spec.ref()}


def test_main_input_dependency_uses_scope_identity_for_step_output_edges():
    planner = PathPlanner.__new__(PathPlanner)
    planner.artifact_context = ArtifactDeclarationStepContext.empty()
    planner.declared = {}
    planner.plans = {
        0: CompiledStepPlan(
            step_index=0,
            step_scope_id="plate::functionstep_0",
            step_name="load",
            axis_id="A01",
            output_dir=Path("/data/plate1_processed/images"),
        ),
        1: CompiledStepPlan(
            step_index=1,
            step_scope_id="plate::functionstep_1",
            step_name="measure",
            axis_id="A01",
        ),
    }
    snapshots_by_index = {
        0: _resolved_step(),
        1: _resolved_step(),
    }
    planner.session = SimpleNamespace(
        snapshot=lambda index: snapshots_by_index[index],
    )
    planner.steps = PathPlannerStepAssemblyStage(planner)

    dependency = planner.steps.main_input_dependency(
        _resolved_step(is_function_step=False),
        1,
    )

    assert dependency.kind is StepInputDependencyKind.STEP_OUTPUT
    assert dependency.source_step_index == 0
    assert dependency.source_step_scope_id == "plate::functionstep_0"

    input_dir, output_dir = planner.steps.step_io_dirs(dependency, 1)
    assert input_dir == Path("/data/plate1_processed/images")
    assert output_dir == Path("/data/plate1_processed/images")


def test_main_input_dependency_uses_declared_artifact_producer_not_previous_step():
    planner = PathPlanner.__new__(PathPlanner)
    planner.artifact_context = ArtifactDeclarationStepContext.empty()
    planner.declared = {}
    planner.plans = {
        index: CompiledStepPlan(
            step_index=index,
            step_scope_id=f"plate::functionstep_{index}",
            step_name=name,
            axis_id="A01",
        )
        for index, name in enumerate(("CropBlue", "CropRed", "Identify"))
    }
    planner.artifact_context = ArtifactDeclarationStepContext.empty()
    crop_blue = ArtifactOutputPlan(
        name="CropBlue",
        path="/memory/CropBlue.pkl",
        artifact_type=ImageArtifactType,
        producer_step_index=0,
        producer_step_scope_id="plate::functionstep_0",
    )
    crop_red = ArtifactOutputPlan(
        name="CropRed",
        path="/memory/CropRed.pkl",
        artifact_type=ImageArtifactType,
        producer_step_index=1,
        producer_step_scope_id="plate::functionstep_1",
    )
    planner.declared = {plan.ref(): plan for plan in (crop_blue, crop_red)}
    planner.steps = PathPlannerStepAssemblyStage(planner)
    declarations = ArtifactGraph(
        non_plan_consumers=(
            ArtifactConsumer(
                spec=ArtifactSpec.input("CropBlue", ImageArtifactType),
                invocation_keys=(),
            ),
        )
    )

    dependency = planner.steps.main_input_dependency(
        _resolved_step(
            input_source=InputSource.PREVIOUS_STEP,
            is_function_step=True,
            name="Identify",
        ),
        2,
        declarations=declarations,
    )

    assert dependency == StepInputDependency.step_output(
        source_step_index=0,
        source_step_scope_id="plate::functionstep_0",
    )


def test_main_input_dependency_skips_main_flow_preserving_steps():
    measurement_spec = ArtifactSpec.output(
        "Measurements",
        MeasurementsArtifactType,
    )

    @runtime_adapter(
        "runtime",
        lambda _request: object(),
        artifact_output_policy=AdapterRecordedArtifactOutputPolicy,
    )
    @artifact_outputs(measurement_spec)
    def measure(image, *, runtime):
        del runtime
        return image, object()

    compiled_contract = CallableContract.from_callable(measure)
    preserving_pattern = CompiledFunctionPattern(
        groups=(
            CompiledFunctionGroup(
                group_key="default",
                invocations=(
                    CompiledFunctionInvocation(
                        key=FunctionInvocationKey.from_contract(
                            compiled_contract,
                            "default",
                            0,
                        ),
                        contract=compiled_contract,
                    ),
                ),
            ),
        ),
        is_grouped=False,
    )
    source_dependency = StepInputDependency.step_output(
        source_step_index=0,
        source_step_scope_id="plate::functionstep_0",
    )
    planner = PathPlanner.__new__(PathPlanner)
    planner.artifact_context = ArtifactDeclarationStepContext.empty()
    planner.declared = {}
    planner.plans = {
        0: CompiledStepPlan(
            step_index=0,
            step_scope_id="plate::functionstep_0",
            step_name="load",
            axis_id="A01",
        ),
        1: CompiledStepPlan(
            step_index=1,
            step_scope_id="plate::functionstep_1",
            step_name="measure",
            axis_id="A01",
            main_input_dependency=source_dependency,
            compiled_function_pattern=preserving_pattern,
        ),
        2: CompiledStepPlan(
            step_index=2,
            step_scope_id="plate::functionstep_2",
            step_name="consume",
            axis_id="A01",
        ),
    }
    planner.session = SimpleNamespace(
        snapshot=lambda index: _resolved_step(),
    )
    planner.steps = PathPlannerStepAssemblyStage(planner)

    dependency = planner.steps.main_input_dependency(
        _resolved_step(is_function_step=False),
        2,
    )

    assert dependency == source_dependency


def test_main_input_dependency_preserves_pipeline_start_edges():
    planner = PathPlanner.__new__(PathPlanner)
    planner.artifact_context = ArtifactDeclarationStepContext.empty()
    planner.declared = {}
    planner.plans = {
        1: CompiledStepPlan(
            step_index=1,
            step_scope_id="plate::functionstep_1",
            step_name="qc",
            axis_id="A01",
        )
    }
    planner.initial_input = Path("/data/plate1/images")
    planner.session = SimpleNamespace(
        snapshot=lambda index: {1: _resolved_step()}[index],
    )
    planner.paths = SimpleNamespace(
        build_output_path=lambda *_args, **_kwargs: Path(
            "/data/plate1_processed/images"
        )
    )
    planner.steps = PathPlannerStepAssemblyStage(planner)

    dependency = planner.steps.main_input_dependency(
        _resolved_step(input_source=InputSource.PIPELINE_START, is_function_step=False),
        1,
    )

    assert dependency.kind is StepInputDependencyKind.PIPELINE_START
    input_dir, output_dir = planner.steps.step_io_dirs(dependency, 1)
    assert input_dir == Path("/data/plate1/images")
    assert output_dir == Path("/data/plate1_processed/images")
