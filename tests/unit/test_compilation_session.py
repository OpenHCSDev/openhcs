from openhcs.core.pipeline.compilation_session import ResolvedPipelineDefinition
from inspect import signature
from types import SimpleNamespace

import pytest
from objectstate.lazy_factory import ensure_global_config_context
from objectstate.object_state import ObjectState
from objectstate.object_state_registry import ObjectStateRegistry

from openhcs.constants.constants import AllComponents, GroupBy, VariableComponents
from openhcs.constants.input_source import InputSource
from openhcs.core.artifacts import ArtifactSpec, ImageArtifactType
from openhcs.core.callable_contract import CallableContract
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyNapariStreamingConfig,
    LazyProcessingConfig,
    LazySourceBindingsConfig,
    LazyStepSourceBindingsConfig,
    PipelineConfig,
    ProcessingConfig,
    StepMaterializationConfig,
)
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.function_patterns import (
    compile_function_pattern,
    inject_artifact_input_values,
    normalize_function_pattern,
)
from openhcs.core.invocation_artifacts import ArtifactDeclarationStepContext
from openhcs.core.pipeline.compilation_session import CompilationSession
from openhcs.core.pipeline.compiler import AxisCompilationRequest, PipelineCompiler
from openhcs.core.pipeline.function_contracts import artifact_inputs
from openhcs.core.pipeline.path_planner import (
    PathPlanner,
    PathPlannerArtifactStage,
    PathPlannerExecutionGroups,
)
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.source_bindings import (
    EMPTY_SOURCE_BINDINGS,
    ComponentSelector,
    MetadataExtractionRule,
    MetadataSource,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceSelector,
    StepSourceBindingsConfig,
)
from openhcs.core.step_dependencies import StepInputDependency
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.analysis.neurite_outgrowth import (
    neurite_outgrowth_metaxpress,
)


def _identity(image):
    return image


@pytest.mark.parametrize("pipeline_workers, expected_workers", [(None, 2), (3, 3)])
def test_compiler_captures_scoped_worker_count(pipeline_workers, expected_workers):
    ObjectStateRegistry.clear()
    global_config = GlobalPipelineConfig(num_workers=2)
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    global_state = ObjectState(global_config, scope_id="")
    pipeline_state = ObjectState(
        PipelineConfig(num_workers=pipeline_workers),
        scope_id="plate",
        parent_state=global_state,
    )
    try:
        ObjectStateRegistry.register(global_state, _skip_snapshot=True)
        ObjectStateRegistry.register(pipeline_state, _skip_snapshot=True)
        captured = pipeline_state.to_saved_resolved_object()
        assert captured.num_workers == expected_workers
        assignments = PipelineCompiler._calculate_worker_assignments(
            ["A", "B", "C", "D"], captured.num_workers
        )
        assert len(assignments) == expected_workers

        # The compiled snapshot must not resolve again in a different context.
        ensure_global_config_context(
            GlobalPipelineConfig, GlobalPipelineConfig(num_workers=4)
        )
        assert captured.num_workers == expected_workers
    finally:
        ObjectStateRegistry.clear()
        ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())


def test_axis_session_initialization_requires_pipeline_resolved_state() -> None:
    parameters = signature(
        PipelineCompiler.initialize_step_plans_for_context
    ).parameters

    assert "pipeline" in parameters
    assert "step_state_map" not in parameters
    assert "step_snapshots" not in parameters
    assert "steps_already_resolved" not in parameters
    assert "_resolve_steps_for_context" not in vars(PipelineCompiler)


def test_nonsequential_axis_compilation_finishes_its_initial_session(monkeypatch):
    """Do not plan the same axis a second time after checking sequential mode."""
    events: list[str] = []
    context = SimpleNamespace(
        pipeline_sequential_mode=False,
        pipeline_sequential_combinations=None,
        freeze=lambda: events.append("freeze"),
    )
    session = SimpleNamespace(context=context, global_config=GlobalPipelineConfig())
    request = SimpleNamespace(
        context_for=lambda axis_id: events.append(f"context:{axis_id}") or context,
        orchestrator=SimpleNamespace(),
        enable_visualizer_override=False,
    )
    monkeypatch.setattr(
        PipelineCompiler,
        "build_initialize_axis_session",
        lambda *_args: events.append("plan") or session,
    )
    monkeypatch.setattr(
        PipelineCompiler,
        "analyze_pipeline_sequential_mode",
        lambda *_args: events.append("analyze"),
    )
    monkeypatch.setattr(
        PipelineCompiler,
        "declare_zarr_stores",
        lambda planned: events.append("stores") if planned is session else None,
    )
    monkeypatch.setattr(
        PipelineCompiler,
        "plan_materialization_flags",
        lambda planned: (
            events.append("materialization") if planned is session else None
        ),
    )
    monkeypatch.setattr(
        PipelineCompiler,
        "_run_post_plan_compile_stages",
        lambda planned, **_kwargs: (
            events.append("post_plan") if planned is session else None
        ),
    )

    compiled = PipelineCompiler._compile_axis_value(
        request=request, axis_id="A01", metadata_writer=True
    )

    assert compiled == {"A01": context}
    assert events == [
        "context:A01",
        "plan",
        "analyze",
        "stores",
        "materialization",
        "post_plan",
        "freeze",
    ]


@artifact_inputs(
    ArtifactSpec.input(
        "DNA",
        ImageArtifactType,
        parameter_name="image",
    )
)
def _external_source_consumer(image):
    return image


@artifact_inputs(
    ArtifactSpec.input(
        "DNA",
        ImageArtifactType,
        parameter_name="dna",
    )
)
def _previous_step_and_external_source(image, dna):
    return image, dna


def _resolved_step(
    step: FunctionStep,
    variable_components=(VariableComponents.SITE,),
    source_bindings=EMPTY_SOURCE_BINDINGS,
    input_source: InputSource = InputSource.PREVIOUS_STEP,
) -> AbstractStep:
    step.source_bindings = source_bindings
    step.processing_config = ProcessingConfig(
        variable_components=list(variable_components),
        group_by=GroupBy.NONE,
        input_source=input_source,
    )
    step.step_materialization_config = StepMaterializationConfig(enabled=False)
    return step


def _context() -> SimpleNamespace:
    return SimpleNamespace(
        axis_id="A01",
        plate_path=None,
        current_sequential_combination=None,
        step_plans={
            0: CompiledStepPlan(
                step_index=0,
                step_name="step",
                step_type="FunctionStep",
                axis_id="A01",
            )
        },
    )


def _orchestrator(pipeline_config: PipelineConfig | None = None) -> SimpleNamespace:
    return SimpleNamespace(pipeline_config=pipeline_config or PipelineConfig())


def _compile_source_plans_for_contract(
    session: CompilationSession,
    snapshot: AbstractStep,
    func,
    main_input_dependency: StepInputDependency = StepInputDependency.pipeline_start(),
):
    planner = SimpleNamespace(
        session=session,
        artifact_context=ArtifactDeclarationStepContext.empty(),
    )
    stage = PathPlannerArtifactStage(planner)
    execution_bindings = stage.source_bindings_for_contracts(
        snapshot,
        (CallableContract.from_callable(func),),
        main_input_dependency,
    )
    return execution_bindings, stage.compile_source_plans(
        snapshot,
        execution_bindings,
    )


class _EffectiveConfigContextOrchestrator:
    def create_context(self, axis_id: str, *, resolved_config) -> ProcessingContext:
        return ProcessingContext(
            axis_id=axis_id,
            auto_add_output_plate_to_plate_manager=resolved_config.auto_add_output_plate_to_plate_manager,
        )


def test_axis_compilation_request_preserves_effective_auto_add_flag():
    request = AxisCompilationRequest(
        orchestrator=_EffectiveConfigContextOrchestrator(),
        global_config=GlobalPipelineConfig(auto_add_output_plate_to_plate_manager=True),
        pipeline=SimpleNamespace(),
        path_resolver=SimpleNamespace(),
        global_step_axis_filters={},
        enable_visualizer_override=False,
        is_zmq_execution=True,
    )

    context = request.context_for("A01")

    assert context.auto_add_output_plate_to_plate_manager is True
    assert context.source_image_set_identity_policy.plane_member_components == (
        frozenset((AllComponents.CHANNEL,))
    )


def test_compilation_session_shares_resolved_pipeline_and_owns_axis_plans():
    step = FunctionStep(func=_identity, name="step")
    step_state = SimpleNamespace(scope_id="plate::functionstep_0")
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(_resolved_step(step),),
            step_scope_ids={0: step_state.scope_id},
            step_provenance={0: {}},
        ),
    )

    assert session.axis_id == "A01"
    assert session.pipeline.steps[0] is not step
    assert step.func is _identity
    captured = session.pipeline.steps[0].func
    assert normalize_function_pattern(captured) is captured
    assert next(captured.iter_items()).func is _identity
    assert session.pipeline.step_scope_ids[0] == step_state.scope_id
    assert session.pipeline.steps[0].name == "step"
    assert session.plan(0).step_name == "step"


def test_resolved_declarations_reuse_contracts_but_keep_axis_and_author_epochs(monkeypatch):
    from openhcs.core.pipeline.artifact_planning import extract_artifact_declarations
    from openhcs.core.invocation_artifacts import InvocationContractPlan

    @artifact_inputs("grid_dimensions")
    def needs_grid(image, grid_dimensions, *, sigma=1):
        return image

    kwargs = {"grid_dimensions": None, "sigma": 2}
    authored = FunctionStep(
        func={1: [(needs_grid, kwargs), (_identity, {"enabled": False})]},
        name="Grid",
    )
    definition = [authored]
    state = SimpleNamespace(scope_id="plate::functionstep_0")
    from_callable = CallableContract.from_callable.__func__
    calls = []

    def count_contracts(cls, func):
        calls.append(func)
        return from_callable(cls, func)

    monkeypatch.setattr(CallableContract, "from_callable", classmethod(count_contracts))
    pipeline = PipelineCompiler._filter_enabled_steps(definition, {0: state})
    captured = pipeline.steps[0].func
    (item,) = tuple(captured.iter_items())
    assert definition == [authored] and definition[0].func[1][0][1] is kwargs
    assert captured.source_group_keys == (1,)
    assert calls == [needs_grid]
    assert normalize_function_pattern(captured) is captured
    extract_artifact_declarations(captured)
    injected = inject_artifact_input_values(captured, {"grid_dimensions": (3, 4)})
    other_axis = inject_artifact_input_values(captured, {"grid_dimensions": (8, 9)})
    compiled = compile_function_pattern(injected, {}, {})
    assert calls == [needs_grid]
    assert next(injected.iter_items()).contract is item.contract
    assert next(other_axis.iter_items()).contract is item.contract
    assert next(compiled.iter_invocations()).contract is item.contract
    assert next(injected.iter_items()).kwargs_dict["grid_dimensions"] == (3, 4)
    assert next(other_axis.iter_items()).kwargs_dict["grid_dimensions"] == (8, 9)
    assert item.kwargs_dict == {"grid_dimensions": None, "sigma": 2}

    replacement = from_callable(CallableContract, needs_grid)
    provider_compiled = compile_function_pattern(
        injected,
        {},
        {},
        invocation_contract_provider=lambda _item, _context: InvocationContractPlan(
            replacement
        ),
    )
    assert next(provider_compiled.iter_invocations()).contract is replacement
    kwargs["sigma"] = 7
    assert item.kwargs_dict["sigma"] == 2
    recaptured = ResolvedPipelineDefinition(
        definition, {0: state.scope_id}, step_provenance={0: {}}
    )
    assert next(recaptured.steps[0].func.iter_items()).kwargs_dict["sigma"] == 7
    assert calls == [needs_grid, needs_grid]


def test_compiler_keeps_variable_components_as_stack_source():
    step = FunctionStep(func=_identity, name="step")
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(
                _resolved_step(step, variable_components=(VariableComponents.CHANNEL,)),
            ),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )

    PipelineCompiler._supplement_step_plans(session)

    assert session.plan(0).variable_components == [VariableComponents.CHANNEL]


def test_path_planner_source_binding_plan_comes_from_objectstate_snapshot():
    ObjectStateRegistry.clear()
    metadata_rule = MetadataExtractionRule(
        source=MetadataSource.FILE_NAME,
        pattern=r"(?P<well>[A-H]\d{2})\.tif",
    )
    match_plan = SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER)
    binding = NamedSourceBinding(
        alias="DNA",
        selector=SourceSelector(
            components=(ComponentSelector(AllComponents.CHANNEL, "1"),)
        ),
    )
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    pipeline_state = ObjectState(
        PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig(
                metadata_rules=(metadata_rule,),
                match_plan=match_plan,
            ),
        ),
        scope_id="plate",
    )

    try:
        ObjectStateRegistry.register(pipeline_state, _skip_snapshot=True)
        step = FunctionStep(
            func=_external_source_consumer,
            name="source-bound",
            source_bindings=LazyStepSourceBindingsConfig(
                bindings=(binding,),
                enabled=True,
            ),
        )
        step_state = ObjectState(
            step,
            scope_id="plate::functionstep_0",
            parent_state=pipeline_state,
            exclude_params=["func"],
        )
        ObjectStateRegistry.register(step_state, _skip_snapshot=True)
        resolved_step = step_state.to_saved_resolved_object()
        snapshot = resolved_step
        session = CompilationSession.from_context(
            context=_context(),
            orchestrator=_orchestrator(pipeline_state.to_object()),
            global_config=GlobalPipelineConfig(),
            pipeline=ResolvedPipelineDefinition(
                steps=(snapshot,),
                step_scope_ids={0: step_state.scope_id},
                step_provenance={0: {}},
            ),
        )

        execution_bindings, (source_binding_plan, _source_universe_plan) = (
            _compile_source_plans_for_contract(
                session,
                snapshot,
                _external_source_consumer,
            )
        )
    finally:
        ObjectStateRegistry.clear()

    assert snapshot.source_bindings.bindings == (binding,)
    assert snapshot.source_bindings.metadata_rules == (metadata_rule,)
    assert snapshot.source_bindings.match_plan == match_plan
    assert execution_bindings.bindings == (binding,)
    assert source_binding_plan.bindings == (binding,)
    assert source_binding_plan.metadata_rules == (metadata_rule,)
    assert source_binding_plan.match_plan == match_plan


def test_compiler_streaming_config_snapshot_preserves_inherited_port():
    ObjectStateRegistry.clear()
    global_config = GlobalPipelineConfig(
        napari_streaming_config=LazyNapariStreamingConfig(
            enabled=True,
            persistent=False,
        ),
    )
    ensure_global_config_context(GlobalPipelineConfig, global_config)
    global_state = ObjectState(global_config, scope_id="")
    pipeline_state = ObjectState(
        PipelineConfig(),
        scope_id="plate",
        parent_state=global_state,
    )

    try:
        ObjectStateRegistry.register(global_state, _skip_snapshot=True)
        ObjectStateRegistry.register(pipeline_state, _skip_snapshot=True)
        step = FunctionStep(func=_identity, name="streamed")
        step_state = ObjectState(
            step,
            scope_id="plate::functionstep_0",
            parent_state=pipeline_state,
            exclude_params=["func"],
        )
        ObjectStateRegistry.register(step_state, _skip_snapshot=True)
        resolved_step = step_state.to_saved_resolved_object()
        snapshot = resolved_step
        context = _context()
        context.required_visualizers = []
        session = CompilationSession.from_context(
            context=context,
            orchestrator=_orchestrator(pipeline_state.to_object()),
            global_config=global_config,
            pipeline=ResolvedPipelineDefinition(
                steps=(snapshot,),
                step_scope_ids={0: step_state.scope_id},
                step_provenance={0: {}},
            ),
        )

        PipelineCompiler._collect_streaming_configs(session)
    finally:
        ObjectStateRegistry.clear()

    assert context.required_visualizers
    required = context.required_visualizers[0]
    assert required.config.enabled is True
    assert required.config.persistent is False
    assert required.config.port == 5555
    assert session.plan(0).streaming_configs["napari_streaming_config"].port == 5555


def test_compiler_disabled_source_bindings_stay_inert_without_contract_requirement():
    binding = NamedSourceBinding(alias="DNA")
    step = FunctionStep(func=_identity, name="source-bound")
    snapshot = _resolved_step(
        step, source_bindings=StepSourceBindingsConfig(bindings=(binding,))
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )

    PipelineCompiler._supplement_step_plans(session)

    assert session.plan(0).source_binding_plan.is_empty


def test_path_planner_activates_declared_source_binding_for_pipeline_start():
    binding = NamedSourceBinding(alias="DNA")
    step = FunctionStep(func=_external_source_consumer, name="source-bound")
    snapshot = _resolved_step(
        step,
        source_bindings=StepSourceBindingsConfig(bindings=(binding,)),
        input_source=InputSource.PIPELINE_START,
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )

    _execution_bindings, (source_binding_plan, _source_universe_plan) = (
        _compile_source_plans_for_contract(
            session,
            snapshot,
            _external_source_consumer,
        )
    )

    assert source_binding_plan.bindings == (binding,)


def test_plate_export_contract_construction_projects_inputs_to_runtime_batch():
    from openhcs.interop.cellprofiler.compile_time_contracts import (
        CellProfilerInvocationContractProviderFactory,
    )
    from openhcs.processing.backends.cellprofiler import export_to_database

    binding = NamedSourceBinding(alias="DNA")
    step = FunctionStep(func=export_to_database, name="ExportToDatabase")
    snapshot = _resolved_step(
        step,
        variable_components=(),
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=(binding,),
        ),
        input_source=InputSource.PIPELINE_START,
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )
    dependency_before_provider = session.plan(0).main_input_dependency

    provider = CellProfilerInvocationContractProviderFactory.provider_for_session(
        session
    )
    invocation = next(normalize_function_pattern(step.func).iter_items())
    assert provider is not None
    plan = provider(
        invocation,
        ArtifactDeclarationStepContext(
            step_name=step.name,
            step_index=0,
            source_bindings=step.source_bindings,
            group_by=step.processing_config.group_by,
            input_source=step.processing_config.input_source,
        ),
    )

    assert plan is not None
    assert dependency_before_provider == StepInputDependency.unresolved()
    assert session.plan(0).main_input_dependency == dependency_before_provider
    assert plan.contract.artifact_inputs.names() == ("DNA",)


def test_path_planner_preserves_pipeline_start_bindings_for_implicit_main_flow():
    binding = NamedSourceBinding(alias="DNA")
    step = FunctionStep(func=_identity, name="source-bound measurement")
    snapshot = _resolved_step(
        step,
        source_bindings=StepSourceBindingsConfig(bindings=(binding,)),
        input_source=InputSource.PIPELINE_START,
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )
    execution_bindings, (source_binding_plan, source_universe_plan) = (
        _compile_source_plans_for_contract(session, snapshot, _identity)
    )

    assert execution_bindings.bindings == (binding,)
    assert source_binding_plan.bindings == (binding,)
    assert source_universe_plan == source_universe_plan.empty()


def test_path_planner_step_output_projects_only_exact_source_artifacts() -> None:
    dna = NamedSourceBinding(alias="DNA")
    unrelated = NamedSourceBinding(alias="OrigRed")
    step = FunctionStep(
        func=_previous_step_and_external_source,
        name="previous-step plus exact source",
    )
    snapshot = _resolved_step(
        step, source_bindings=StepSourceBindingsConfig(bindings=(dna, unrelated))
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )

    execution_bindings, (source_binding_plan, _source_universe_plan) = (
        _compile_source_plans_for_contract(
            session,
            snapshot,
            _previous_step_and_external_source,
            StepInputDependency.step_output(
                source_step_index=0,
                source_step_scope_id="plate::functionstep_0",
            ),
        )
    )

    assert execution_bindings.bindings == (dna,)
    assert source_binding_plan.bindings == (dna,)


def test_path_planner_preserves_metaxpress_primary_source_order() -> None:
    pipeline_bindings = (
        NamedSourceBinding(alias="Hoechst"),
        NamedSourceBinding(alias="MAP2"),
        NamedSourceBinding(alias="SMI312"),
    )
    selected_bindings = (
        NamedSourceBinding(alias="SMI312"),
        NamedSourceBinding(alias="Hoechst"),
    )
    step = FunctionStep(func=neurite_outgrowth_metaxpress, name="neurite")
    snapshot = _resolved_step(
        step,
        variable_components=(VariableComponents.CHANNEL,),
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=selected_bindings,
        ),
        input_source=InputSource.PIPELINE_START,
    )
    pipeline_config = PipelineConfig(
        source_bindings_config=LazySourceBindingsConfig(bindings=pipeline_bindings)
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(pipeline_config),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )
    contract = CallableContract.from_callable(neurite_outgrowth_metaxpress)

    execution_bindings, (source_binding_plan, _source_universe_plan) = (
        _compile_source_plans_for_contract(
            session,
            snapshot,
            neurite_outgrowth_metaxpress,
        )
    )

    assert contract.accepts_implicit_main_flow_input is True
    assert contract.artifact_inputs.names() == ("pixel_size",)
    assert tuple(binding.alias for binding in pipeline_bindings) == (
        "Hoechst",
        "MAP2",
        "SMI312",
    )
    assert tuple(binding.alias for binding in execution_bindings.bindings) == (
        "SMI312",
        "Hoechst",
    )
    assert source_binding_plan.bindings == execution_bindings.bindings


def test_path_planner_execution_groups_use_resolved_source_bindings():
    step = FunctionStep(func=_identity, name="source-bound")
    bindings = (
        NamedSourceBinding(
            alias="OrigStain1",
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "1"),),
        ),
        NamedSourceBinding(
            alias="OrigStain2",
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "2"),),
        ),
    )
    snapshot = _resolved_step(
        step,
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=bindings,
        ),
    )
    planner = PathPlanner.__new__(PathPlanner)
    planner.session = SimpleNamespace(realized_source_metadata=None)

    scope = PathPlannerExecutionGroups(planner).source_binding_scope_for_group_by(
        snapshot,
        GroupBy.CHANNEL,
        source_bindings=snapshot.source_bindings,
    )

    assert scope.keys == ("1", "2")
    assert scope.component is AllComponents.CHANNEL


def test_path_planner_execution_groups_preserve_declared_component_identity() -> None:
    step = FunctionStep(func=_identity, name="source-bound")
    bindings = (
        NamedSourceBinding(
            alias="MCP_DNA",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "1"),),
            ),
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "MCP_DNA"),),
        ),
        NamedSourceBinding(
            alias="MCP_AGP",
            selector=SourceSelector(
                components=(ComponentSelector(AllComponents.CHANNEL, "2"),),
            ),
            component_identity=(ComponentSelector(AllComponents.CHANNEL, "MCP_AGP"),),
        ),
    )
    snapshot = _resolved_step(
        step,
        source_bindings=StepSourceBindingsConfig(
            enabled=True,
            bindings=bindings,
        ),
    )
    planner = PathPlanner.__new__(PathPlanner)
    planner.session = SimpleNamespace(
        realized_source_metadata=(
            {"channel": 1},
            {"channel": 2},
        )
    )

    scope = PathPlannerExecutionGroups(planner).source_binding_scope_for_group_by(
        snapshot,
        GroupBy.CHANNEL,
        source_bindings=snapshot.source_bindings,
    )

    assert scope.keys == ("MCP_DNA", "MCP_AGP")
    assert scope.component is AllComponents.CHANNEL


def test_path_planner_freezes_only_contract_selected_source_bindings():
    binding = NamedSourceBinding(alias="DNA")
    unused_binding = NamedSourceBinding(alias="Unused")
    step = FunctionStep(func=_external_source_consumer, name="source-bound")
    snapshot = _resolved_step(
        step,
        source_bindings=StepSourceBindingsConfig(
            bindings=(binding, unused_binding),
            enabled=True,
        ),
    )
    session = CompilationSession.from_context(
        context=_context(),
        orchestrator=_orchestrator(),
        global_config=GlobalPipelineConfig(),
        pipeline=ResolvedPipelineDefinition(
            steps=(snapshot,),
            step_scope_ids={0: "plate::functionstep_0"},
            step_provenance={0: {}},
        ),
    )
    execution_bindings, (source_binding_plan, _source_universe_plan) = (
        _compile_source_plans_for_contract(
            session,
            snapshot,
            _external_source_consumer,
        )
    )

    assert execution_bindings.bindings == (binding,)
    assert source_binding_plan.bindings == (binding,)


def test_compiler_pipeline_scope_prevents_cross_pipeline_source_binding_inheritance(
    tmp_path,
):
    ObjectStateRegistry.clear()
    binding = NamedSourceBinding(alias="DNA")
    plate_path = tmp_path / "plate"
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())

    first_orchestrator = SimpleNamespace(
        plate_path=plate_path,
        pipeline_config=PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig(bindings=(binding,)),
        ),
    )
    second_orchestrator = SimpleNamespace(
        plate_path=plate_path,
        pipeline_config=PipelineConfig(),
    )
    first_pipeline = [FunctionStep(func=_identity, name="first")]
    second_pipeline = [FunctionStep(func=_identity, name="second")]
    first_resolved = PipelineCompiler._resolve_pipeline_once(
        first_orchestrator, first_pipeline
    )
    second_resolved = PipelineCompiler._resolve_pipeline_once(
        second_orchestrator, second_pipeline
    )
    first_scope = first_resolved.step_scope_ids[0]
    second_scope = second_resolved.step_scope_ids[0]

    assert first_scope != second_scope
    assert first_resolved.steps[0].source_bindings.bindings == (binding,)
    assert second_resolved.steps[0].source_bindings.is_empty


def test_headless_resolution_preserves_saved_ui_ancestors_and_registrations(tmp_path):
    ObjectStateRegistry.clear()
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    plate_path = tmp_path / "plate"
    saved_binding = NamedSourceBinding(alias="DNA")
    live_binding = NamedSourceBinding(alias="Memb")
    ui_state = ObjectState(
        PipelineConfig(
            source_bindings_config=LazySourceBindingsConfig(bindings=(saved_binding,)),
            processing_config=LazyProcessingConfig(
                variable_components=[VariableComponents.SITE],
            ),
        ),
        scope_id=str(plate_path),
    )
    ObjectStateRegistry.register(ui_state, _skip_snapshot=True)
    ui_state.update_parameter("source_bindings_config.bindings", (live_binding,))
    original_states = ObjectStateRegistry.get_all()
    original_parameters = dict(ui_state.parameters)
    observed_registrations = []

    def record_registration(scope, state):
        observed_registrations.append((scope, state))

    subscription = ObjectStateRegistry.add_register_callback(record_registration)
    authored = [
        FunctionStep(func=_identity, name="disabled", enabled=False),
        FunctionStep(func=_identity, name="enabled"),
    ]
    enabled_token = authored[1]._scope_token or "step_1"
    try:
        resolved = PipelineCompiler._resolve_pipeline_once(
            SimpleNamespace(plate_path=plate_path, pipeline_config=PipelineConfig()),
            authored,
        )
        assert len(resolved.steps) == 1
        assert resolved.steps[0].source_bindings.bindings == (saved_binding,)
        assert resolved.step_scope_ids[0].endswith(f"::{enabled_token}")
        source_scope, _source_type = resolved.step_provenance[0][
            "source_bindings.bindings"
        ]
        assert source_scope == str(plate_path)
        assert ObjectStateRegistry.get_all() == original_states
        assert ui_state.parameters == original_parameters
        assert observed_registrations == []
        assert ui_state.get_resolved_value("source_bindings_config.bindings") == (
            live_binding,
        )
        saved_components = object.__getattribute__(
            ui_state.object_instance.processing_config, "variable_components"
        )
        saved_components.append(VariableComponents.Z_INDEX)
        assert resolved.steps[0].processing_config.variable_components == [
            VariableComponents.SITE
        ]
    finally:
        subscription.release()
        ObjectStateRegistry.clear()
