"""The dataset list renders the session; its work and documents go through it."""

from __future__ import annotations

import ast
import asyncio
import threading
import time
from pathlib import Path
from types import SimpleNamespace

import pytest
from objectstate.object_state import ObjectState, ObjectStateRegistry
from PyQt6.QtCore import Qt
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

import openhcs.processing.backends.cellprofiler as cellprofiler_backend
from openhcs.agent.dto.ui_bridge import (
    UiBridgeConfirmationRequirement,
    UiCodeDocumentApplyRequest,
    UiCodeDocumentId,
    UiCodeDocumentRequest,
    UiCodeDocumentSelectionMode,
    UiStateSurfaceId,
    UiStateSurfaceRequest,
    UiWindowNavigateRequest,
)
from openhcs.agent.ui_bridge_identities import PipelineEditorWidgetIdentity
from openhcs.authoring.session.dataset_document import (
    AllDatasetDocumentScope,
    SelectedDatasetDocumentScope,
    apply_dataset_document,
    authored_pipeline_config,
    live_global_config,
    render_dataset_document,
)
from openhcs.authoring.session.operations.datasets import (
    CompileDatasets,
    DeleteDatasets,
    EditDatasetConfig,
    InitializeDatasets,
    ShowDatasetCode,
    ShowDatasetImages,
    StopExecution,
)
from openhcs.authoring.session.operations.pipelines import (
    AddPipelineStep,
    DeletePipelineSteps,
    EditPipelineStep,
    LoadExamplePipeline,
    ShowPipelineCode,
)
from openhcs.authoring.session.pipelines import PipelineObjectStateBinding
from openhcs.authoring.session.views import DatasetListView
from openhcs.constants.constants import OrchestratorState
from openhcs.core.config import (
    GlobalPipelineConfig,
    LazyFijiStreamingConfig,
    LazyNapariStreamingConfig,
    LazySourceBindingsConfig,
    PipelineConfig,
    WellFilterConfig,
)
from openhcs.core.dataset_sources.openhcs_format import OpenHCSDatasetSource
from openhcs.core.dataset_sources.source_bindings_source import SourceBindingsSource
from openhcs.core.debug import DebugTerminalSummary
from openhcs.core.execution_state import (
    ExecutionCompletionPayload,
    ExecutionOutputPlateSummary,
    ManagerExecutionState,
    TerminalExecutionStatus,
)
from openhcs.core.input_workspace import InputWorkspacePreparationResult
from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.progress import (
    ProgressEvent,
    ProgressIdentity,
    ProgressPhase,
    ProgressStatus,
)
from openhcs.core.selection import SelectedAllSelectionMode
from openhcs.core.source_bindings import (
    LazyStepSourceBindingsConfig,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceSelector,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.desktop.update import (
    DesktopRestartSession,
    DesktopRestartSucceeded,
    DesktopRestartUiState,
)
from openhcs.interop.cellprofiler.dataset_scope import CellProfilerPipelineScope
from openhcs.processing.backends.processors.numpy_processor import (
    percentile_normalize,
)
from openhcs.pyqt_gui.services.main_window_workflows import (
    MainWindowDockPane,
    MainWindowEmbeddedWidgets,
    MainWindowPipelineActions,
)
from openhcs.pyqt_gui.services.ui_agent_bridge import UiAgentBridgeService
from openhcs.pyqt_gui.services.ui_bridge_object_state import (
    ObjectStateBridgeProviderSet,
)
from openhcs.pyqt_gui.services.ui_bridge_plate_manager import (
    PlateManagerBridgeProviderSet,
)
from openhcs.pyqt_gui.services.ui_bridge_windows import UiWindowProjectionService
from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId
from openhcs.ui.shared.plate_manager_code_document import (
    PlateManagerCodeDocumentAuthority,
)
from tests.unit.pyqt_gui.session_harness import (
    add_datasets,
    caller_session,
    session_gui,
)


class InlineUiThreadDispatcher:
    """Execute UI bridge work inline for widgets owned by this thread."""

    def call(self, callback, *, timeout_ms: int = 5000):
        del timeout_ms
        return callback()

    def post(self, callback) -> None:
        callback()


def _ready(session, *scope_ids: str) -> None:
    for scope_id in scope_ids:
        session.set_dataset_state(scope_id, OrchestratorState.READY)


def _running(session, scope_id: str, execution_id: str) -> None:
    session.batch.begin_batch((scope_id,))
    session.batch.record_execution(scope_id, execution_id)
    session.execution_state = ManagerExecutionState.RUNNING


def _connected(monkeypatch, session) -> None:
    monkeypatch.setattr(
        session,
        "endpoint_status",
        lambda: EndpointStartupStatus(EndpointStartupPhase.CONNECTED, "test"),
    )


def _names(steps) -> list[str]:
    return [step.name for step in steps]


def _workspace(steps, pipeline_config: PipelineConfig | None = None):
    return InputWorkspacePreparationResult(
        original_source_root=Path("/source"),
        execution_plate_path=Path("/execution"),
        pipeline_path=Path("/source/pipeline.cppipe"),
        pipeline_steps=list(steps),
        pipeline_config=pipeline_config or PipelineConfig(),
    )


def _bridge(manager) -> UiAgentBridgeService:
    return UiAgentBridgeService(
        provider_set=PlateManagerBridgeProviderSet(manager),
        dispatcher=InlineUiThreadDispatcher(),
    )


def _apply(bridge, source: str, *, selection_mode=UiCodeDocumentSelectionMode.ALL):
    document = bridge.get_document(
        UiCodeDocumentRequest(
            document_id=UiCodeDocumentId.PLATE_MANAGER_ORCHESTRATOR.value,
            selection_mode=selection_mode.value,
        )
    )
    return bridge.apply_document(
        UiCodeDocumentApplyRequest(
            document_id=document.summary.identity.document_id,
            source=source,
            base_revision_token=document.current_revision_token,
            selection_mode=document.selection_mode,
            selected_scope_ids=document.selected_scope_ids,
            confirmation_requirement=UiBridgeConfirmationRequirement.from_flag(False),
        )
    )


def _document_source(session, scope_ids, steps_by_scope, global_config=None) -> str:
    """A dataset document as an agent would submit it.

    Steps carry no function: the bridge source policy admits imported names
    only, and functions render as registry lookups.
    """

    return PlateManagerCodeDocumentAuthority.render(
        PlateManagerCodeDocumentAuthority.from_values(
            plate_paths=list(scope_ids),
            global_pipeline_config=global_config or live_global_config(session),
            per_plate_configs={
                scope_id: authored_pipeline_config(scope_id) for scope_id in scope_ids
            },
            pipeline_data=steps_by_scope,
        )
    )


# ---------------------------------------------------------------------------
# Admission: work on one dataset leaves the others editable
# ---------------------------------------------------------------------------


def test_object_scope_mutations_are_authorized_by_their_owning_dataset(
    tmp_path, monkeypatch
) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        calls: list[str | None] = []
        monkeypatch.setattr(
            session,
            "require_definition_mutation_allowed",
            lambda scope=None: calls.append(scope),
        )

        session.require_definition_mutation_allowed_for_object_scope(
            f"{scope_id}::pipeline::functionstep_0"
        )
        session.require_definition_mutation_allowed_for_object_scope("")
        session.require_definition_mutation_allowed_for_object_scope("ui_config")

        assert calls == [scope_id, None]


@pytest.mark.parametrize("work", ("run", "compile", "init"))
def test_work_guards_are_dataset_local_and_views_stay_available(
    tmp_path, monkeypatch, work
) -> None:
    with session_gui() as gui:
        session = gui.session
        _connected(monkeypatch, session)
        active, other = add_datasets(session, tmp_path, "active", "other")
        _ready(session, active, other)
        step = FunctionStep(func=percentile_normalize, name="Editable step")
        for scope_id in (active, other):
            session.set_pipeline(scope_id, [step])
        if work == "run":
            _running(session, active, "owned-run")
        elif work == "compile":
            session.mark_compile_pending((active,))
        else:
            session.init_pending.add(active)
            session.refresh()
        manager, editor = gui.plate_manager, gui.pipeline_editor

        session.require_definition_mutation_allowed(other)
        for scope in (None, active):
            if work == "run":
                session.require_definition_mutation_allowed(scope)
            else:
                with pytest.raises(RuntimeError, match="affected dataset"):
                    session.require_definition_mutation_allowed(scope)

        for scope_id, allowed in ((active, False), (other, True)):
            session.select((scope_id,))
            gui.settle()
            editor.item_list.item(0).setSelected(True)
            gui.settle()
            manager.update_button_states()
            editor.update_button_states()
            for operation in (DeleteDatasets, InitializeDatasets, CompileDatasets):
                assert manager.buttons[operation.operation_id].isEnabled() is allowed
            definition_allowed = allowed or work == "run"
            assert (
                manager.buttons[EditDatasetConfig.operation_id].isEnabled()
                is definition_allowed
            )
            assert manager.buttons[ShowDatasetCode.operation_id].isEnabled()
            assert manager.buttons[ShowDatasetImages.operation_id].isEnabled()
            for operation in (
                AddPipelineStep,
                LoadExamplePipeline,
                DeletePipelineSteps,
                EditPipelineStep,
            ):
                assert (
                    editor.buttons[operation.operation_id].isEnabled()
                    is definition_allowed
                ), operation
            assert editor.buttons[ShowPipelineCode.operation_id].isEnabled()

        session.select((active,))
        gui.settle()
        if work == "run":
            MainWindowPipelineActions(None, editor).new_pipeline()
            assert session.pipeline_steps(active) == []
        else:
            with pytest.raises(RuntimeError, match="affected dataset"):
                MainWindowPipelineActions(None, editor).new_pipeline()
            assert _names(session.pipeline_steps(active)) == ["Editable step"]
        session.select((other,))
        gui.settle()
        MainWindowPipelineActions(None, editor).new_pipeline()
        assert session.pipeline_steps(other) == []
        if work == "run":
            session.invalidate_compilation(active)
            assert session.batch.execution_id(active) == "owned-run"
            assert session.batch.active_plates == (active,)


# ---------------------------------------------------------------------------
# Initialization imports a workspace's pipeline and config
# ---------------------------------------------------------------------------


def _cellprofiler_dataset(tmp_path, name="import", pipeline="pipeline.cppipe"):
    root = tmp_path / name
    root.mkdir(exist_ok=True)
    (root / pipeline).write_text("Version:5", encoding="utf-8")
    return root, CellProfilerPipelineScope.scope_for(root, root / pipeline).scope_id


@pytest.mark.parametrize("already_initialized", (False, True))
def test_initialization_publishes_the_workspace_config_while_another_dataset_runs(
    tmp_path, monkeypatch, already_initialized
) -> None:
    with caller_session() as session:
        root, scope_id = _cellprofiler_dataset(tmp_path)
        (running,) = add_datasets(session, tmp_path, "running")
        session.add_dataset_roots((root,))
        workspace = InputWorkspacePreparationResult(
            original_source_root=root,
            execution_plate_path=root,
            pipeline_path=root / "pipeline.cppipe",
            pipeline_steps=[FunctionStep(func=percentile_normalize, name="Imported")],
            pipeline_config=PipelineConfig(num_workers=3),
        )
        monkeypatch.setattr(
            CellProfilerPipelineScope,
            "prepare_input_workspace",
            classmethod(lambda cls, scope: workspace),
        )
        orchestrator = session.orchestrator(scope_id)

        def complete_initialization():
            assert scope_id in session.init_pending
            orchestrator._state = OrchestratorState.READY

        monkeypatch.setattr(orchestrator, "initialize", complete_initialization)
        if already_initialized:
            orchestrator.bind_input_workspace(workspace)
            orchestrator._state = OrchestratorState.READY
        _running(session, running, "owned")

        asyncio.run(session.initialize_datasets((scope_id,)))

        assert not session.init_pending
        assert orchestrator.state is OrchestratorState.READY
        assert (
            ObjectStateRegistry.get_by_scope(scope_id).get_saved_resolved_value(
                "num_workers"
            )
            == 3
        )
        assert _names(session.pipeline_steps(scope_id)) == ["Imported"]
        assert session.batch.execution_id(running) == "owned"


def test_initialization_imports_steps_before_announcing_the_selection(
    tmp_path, monkeypatch
) -> None:
    root, scope_id = _cellprofiler_dataset(tmp_path, pipeline="second.cppipe")
    with session_gui() as gui:
        gui.session.add_dataset_roots((root,))
        gui.settle()
        monkeypatch.setattr(
            CellProfilerPipelineScope,
            "prepare_input_workspace",
            classmethod(
                lambda cls, scope: _workspace(
                    [FunctionStep(func=percentile_normalize, name="Second")]
                )
            ),
        )
        orchestrator = gui.session.orchestrator(scope_id)
        monkeypatch.setattr(
            orchestrator,
            "initialize",
            lambda: setattr(orchestrator, "_state", OrchestratorState.READY),
        )
        observed = []
        gui.plate_manager.plate_selected.connect(
            lambda selected: observed.append(
                (selected, _names(gui.session.pipeline_steps(scope_id)))
            )
        )

        asyncio.run(gui.session.initialize_datasets((scope_id,)))
        gui.settle()

        assert observed == [(scope_id, ["Second"])]
        assert _names(gui.pipeline_editor.displayed_steps) == ["Second"]


def test_workspace_import_replaces_steps_keeps_public_functions_and_applies_config(
    tmp_path,
) -> None:
    root, scope_id = _cellprofiler_dataset(tmp_path, "CropExample", "crop.cppipe")
    match_plan = SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER)
    pipeline_config = PipelineConfig(
        source_bindings_config=LazySourceBindingsConfig(match_plan=match_plan),
    )
    crop = FunctionStep(
        func=(
            cellprofiler_backend.crop,
            {
                "crop_shape": "Rectangle",
                "select_the_input_image": "OrigBlue",
                "name_the_output_image": "CropBlue",
            },
        ),
        name="Crop",
        source_bindings=LazyStepSourceBindingsConfig(
            enabled=False,
            bindings=(
                NamedSourceBinding(
                    alias="OrigDNA",
                    selector=SourceSelector(
                        metadata=(MetadataSelector(field="ChannelNumber", value="1"),)
                    ),
                ),
            ),
        ),
    )
    with caller_session() as session:
        session.add_dataset_roots((root,))
        session.set_pipeline(scope_id, [FunctionStep(func=percentile_normalize, name="Existing")])

        session.import_workspace_pipeline(scope_id, _workspace([crop], pipeline_config))

        (stored,) = session.pipeline_steps(scope_id)
        stored_func, stored_kwargs = stored.func
        assert stored_func is cellprofiler_backend.crop
        assert stored_kwargs["crop_shape"] == "Rectangle"
        assert stored_kwargs["select_the_input_image"] == "OrigBlue"
        assert stored_kwargs["name_the_output_image"] == "CropBlue"
        dataset_state = ObjectStateRegistry.get_by_scope(scope_id)
        assert authored_pipeline_config(scope_id) == pipeline_config
        assert (
            dataset_state.get_saved_resolved_value("source_bindings_config.match_plan")
            == match_plan
        )
        [step_scope_id] = PipelineObjectStateBinding.editor_state_for_plate(
            scope_id
        ).step_scope_ids
        snapshot = ObjectStateRegistry.get_by_scope(
            step_scope_id
        ).to_saved_resolved_object()
        assert snapshot.source_bindings.match_plan == match_plan

        session.set_pipeline(
            scope_id, [FunctionStep(func=(cellprofiler_backend.crop, {}), name="Crop")]
        )
        assert session.pipeline_steps(scope_id)[0].func[0] is cellprofiler_backend.crop


def test_selection_does_not_reseed_a_dirty_imported_config(tmp_path) -> None:
    imported_config = PipelineConfig(
        source_bindings_config=LazySourceBindingsConfig(
            match_plan=SourceBindingMatchPlan(method=SourceBindingMatchMethod.ORDER),
        ),
    )
    with session_gui() as gui:
        session = gui.session
        scope_id, other = add_datasets(session, tmp_path, "plate", "other")
        orchestrator = session.orchestrator(scope_id)
        workspace = _workspace(
            [FunctionStep(func=percentile_normalize, name="Imported")], imported_config
        )
        orchestrator.bind_input_workspace(workspace)
        session.import_workspace_pipeline(scope_id, workspace)
        state = ObjectStateRegistry.get_by_scope(scope_id)
        state.update_parameter(
            "source_bindings_config.match_plan.method",
            SourceBindingMatchMethod.METADATA,
        )

        session.select((other,))
        session.select((scope_id,))
        gui.settle()

        assert (
            state.parameters["source_bindings_config.match_plan.method"]
            is SourceBindingMatchMethod.METADATA
        )
        assert "source_bindings_config.match_plan.method" in state.dirty_fields
        assert _names(session.pipeline_steps(scope_id)) == ["Imported"]


def test_workspace_import_never_writes_into_the_displayed_dataset(tmp_path) -> None:
    root = tmp_path / "AdvancedSegmentation"
    root.mkdir()
    for name in ("BBBC022_Analysis_Start.cppipe", "BBBC022_Analysis_Final.cppipe"):
        (root / name).write_text("Version:5", encoding="utf-8")
    start_scope = CellProfilerPipelineScope.scope_for(
        root, root / "BBBC022_Analysis_Start.cppipe"
    ).scope_id
    final_scope = CellProfilerPipelineScope.scope_for(
        root, root / "BBBC022_Analysis_Final.cppipe"
    ).scope_id
    with session_gui() as gui:
        session = gui.session
        session.add_dataset_roots((root,))
        session.set_pipeline(
            start_scope, [FunctionStep(func=percentile_normalize, name="StartOnly")]
        )
        session.select((start_scope,))
        gui.settle()

        session.import_workspace_pipeline(
            final_scope,
            _workspace([FunctionStep(func=percentile_normalize, name="FinalOnly")]),
        )
        gui.settle()

        assert _names(session.pipeline_steps(start_scope)) == ["StartOnly"]
        assert _names(session.pipeline_steps(final_scope)) == ["FinalOnly"]
        assert gui.pipeline_editor.current_plate == start_scope
        assert _names(gui.pipeline_editor.displayed_steps) == ["StartOnly"]


@pytest.mark.parametrize("state", (OrchestratorState.READY, OrchestratorState.EXECUTING))
def test_source_binding_context_projects_the_current_orchestrator_config(
    tmp_path, state
) -> None:
    with caller_session():
        source_root = tmp_path / "source"
        execution_root = tmp_path / "execution"
        source_root.mkdir()
        execution_root.mkdir()
        logical_scope = "/logical/plate"
        orchestrator = PipelineOrchestrator(
            source_root,
            pipeline_config=PipelineConfig(
                source_bindings_config=LazySourceBindingsConfig(
                    bindings=(NamedSourceBinding(alias="Before"),),
                ),
            ),
        )
        orchestrator.bind_input_workspace(
            InputWorkspacePreparationResult(
                original_source_root=source_root,
                execution_plate_path=execution_root,
                pipeline_steps=[],
                pipeline_config=orchestrator.pipeline_config,
            )
        )
        ObjectStateRegistry.register(
            ObjectState(orchestrator, scope_id=logical_scope), _skip_snapshot=True
        )

        before = orchestrator.source_binding_context(logical_scope)
        assert before is not None
        assert before.logical_plate_id == logical_scope
        assert before.display_plate_root == source_root
        assert before.execution_plate_path == execution_root
        assert tuple(b.alias for b in before.source_bindings.bindings) == ("Before",)

        orchestrator._state = state
        orchestrator.apply_pipeline_config(
            PipelineConfig(
                source_bindings_config=LazySourceBindingsConfig(
                    bindings=(NamedSourceBinding(alias="After"),),
                ),
            )
        )
        after = orchestrator.source_binding_context(logical_scope)
        assert tuple(b.alias for b in after.source_bindings.bindings) == ("After",)
        assert tuple(b.alias for b in before.source_bindings.bindings) == ("Before",)
        assert orchestrator.state is OrchestratorState.CREATED


def test_compile_needs_an_initialized_dataset(tmp_path) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.set_pipeline(scope_id, [FunctionStep(func=percentile_normalize, name="Defined")])

        error = CompileDatasets.available(
            session, CompileDatasets.request_for_selection(session, (scope_id,))
        )

        assert error.code == "dataset_not_initialized"
        assert InitializeDatasets.operation_id in error.hint


def test_live_results_show_the_source_orchestrator_for_source_and_output_rows(
    tmp_path,
) -> None:
    with session_gui() as gui:
        source, output = add_datasets(
            gui.session, tmp_path, "source_plate", "source_plate_openhcs"
        )
        gui.session.set_dataset_state(source, OrchestratorState.COMPLETED)
        source_orchestrator = gui.session.orchestrator(source)

        assert gui.plate_manager.results_orchestrator(source) is source_orchestrator
        assert gui.plate_manager.results_orchestrator(output) is source_orchestrator


# ---------------------------------------------------------------------------
# The dataset list widget
# ---------------------------------------------------------------------------


def test_embedded_manager_navigation_selects_the_exact_live_row(tmp_path) -> None:
    from PyQt6.QtWidgets import QMainWindow

    with session_gui() as gui:
        manager = gui.plate_manager
        main_window = QMainWindow()
        main_window.embedded_widgets = MainWindowEmbeddedWidgets()
        main_window.window_specs = {}
        main_window.embedded_widgets.register(
            MainWindowDockPane.create(
                main_window=main_window,
                window_id=OpenHCSUiWindowId.plate_manager,
                title="Plate Manager",
                widget=manager,
            )
        )
        paths = add_datasets(gui.session, tmp_path, "first", "second")
        gui.settle()
        selected = []
        manager.plate_selected.connect(selected.append)
        projection = UiWindowProjectionService(main_window)

        def navigate(item_id, field_path=None):
            result = projection.navigate(
                UiWindowNavigateRequest.from_fields(
                    window_id=OpenHCSUiWindowId.plate_manager,
                    item_id=item_id,
                    field_path=field_path,
                )
            )
            gui.settle()
            return result

        try:
            for path in reversed(paths):
                result = navigate(path)
                assert result.focused and result.navigated and not result.errors
                assert manager.selection_scope_ids() == (path,)
                assert gui.session.current_scope_id == path
                assert selected[-1] == path

            for item_id, field_path in (
                (str(tmp_path / "missing"), None),
                (paths[0], "not_a_list_target"),
                (None, "not_a_list_target"),
            ):
                result = navigate(item_id, field_path)
                assert result.focused and not result.navigated
                assert result.errors[0].code == "ui_window_navigation_target_unsupported"
                assert gui.session.current_scope_id == paths[0]
            assert selected == list(reversed(paths))

            gui.session.sync_datasets(())
            gui.settle()
            result = navigate(paths[0])
            assert not result.navigated
            assert not manager.get_selected_items()
        finally:
            main_window.close()


def test_restart_selection_stays_aligned_after_a_list_refresh(tmp_path) -> None:
    with session_gui() as gui:
        manager = gui.plate_manager
        paths = add_datasets(gui.session, tmp_path, "P002", "P001")
        gui.session.select((paths[0],))
        gui.settle()
        assert manager.selection_scope_ids() == (paths[0],)
        selected = []
        manager.plate_selected.connect(selected.append)

        DesktopRestartUiState(paths[1]).restore(gui.session, plate_paths=paths)
        manager.update_item_list()
        gui.settle()

        assert gui.session.current_scope_id == paths[1]
        assert manager.selection_scope_ids() == (paths[1],)
        assert selected == [paths[1]]


def test_restart_restores_a_missing_dataset_without_initializing_it(tmp_path) -> None:
    restart = DesktopRestartSession(tmp_path / "pending")
    restart.directory.mkdir()
    scope_id = str(tmp_path / "unavailable-plate")
    payload = PlateManagerCodeDocumentAuthority.from_values(
        plate_paths=(scope_id,),
        global_pipeline_config=GlobalPipelineConfig(),
        per_plate_configs={scope_id: PipelineConfig(dataset_source=OpenHCSDatasetSource)},
        pipeline_data={scope_id: []},
    )
    restart.session_document.write_text(
        PlateManagerCodeDocumentAuthority.render(payload), encoding="utf-8"
    )
    with session_gui() as gui:
        ObjectStateRegistry.save_history_to_file(str(restart.history_document))
        history_refreshes: list[None] = []
        main_window = SimpleNamespace(
            session=gui.session,
            embedded_widgets=SimpleNamespace(
                require_plate_manager=lambda: gui.plate_manager
            ),
            time_travel_widget=SimpleNamespace(
                refresh=lambda: history_refreshes.append(None)
            ),
        )

        consumed = restart.consume()
        outcome = consumed.restore(main_window)

        orchestrator = gui.session.orchestrator(scope_id)
        assert isinstance(outcome, DesktopRestartSucceeded)
        assert orchestrator.state is OrchestratorState.CREATED
        assert not orchestrator.is_initialized()
        restored = gui.plate_manager.dataset_document(SelectedAllSelectionMode.ALL)
        assert restored.payload.plate_paths == (scope_id,)
        assert restored.payload.per_plate_configs == payload.per_plate_configs
        assert restored.payload.pipeline_data == payload.pipeline_data
        assert history_refreshes == [None]
        assert not restart.directory.exists()
        assert not consumed.directory.exists()


def test_a_missing_dataset_declaration_stays_editable_until_initialization(
    tmp_path,
) -> None:
    scope_id = str(tmp_path / "unavailable-plate")
    with caller_session() as session:
        payload = PlateManagerCodeDocumentAuthority.from_values(
            plate_paths=(scope_id,),
            global_pipeline_config=session.global_config,
            per_plate_configs={
                scope_id: PipelineConfig(dataset_source=OpenHCSDatasetSource)
            },
            pipeline_data={scope_id: []},
        )

        apply_dataset_document(session, payload, AllDatasetDocumentScope())

        orchestrator = session.orchestrator(scope_id)
        assert orchestrator.state is OrchestratorState.CREATED
        assert not orchestrator.is_initialized()
        rendered = render_dataset_document(
            session, (scope_id,), selection_mode=SelectedAllSelectionMode.ALL
        )
        assert rendered.payload.plate_paths == (scope_id,)
        with pytest.raises(FileNotFoundError, match="unavailable-plate"):
            orchestrator.initialize()
        assert orchestrator.state is OrchestratorState.INIT_FAILED


def test_drag_reorder_persists_the_dataset_order(tmp_path) -> None:
    with session_gui() as gui:
        scope_ids = list(add_datasets(gui.session, tmp_path, "plate-a", "plate-b"))
        gui.settle()
        item_list = gui.plate_manager.item_list

        item_list.insertItem(1, item_list.takeItem(0))
        gui.plate_manager._handle_items_reordered(0, 1)
        gui.settle()

        assert gui.session.dataset_scope_ids() == list(reversed(scope_ids))
        assert [row.scope_id for row in gui.plate_manager.plates] == list(
            reversed(scope_ids)
        )
        assert [
            item_list.item(index).data(Qt.ItemDataRole.UserRole)
            for index in range(item_list.count())
        ] == list(reversed(scope_ids))


def test_list_refresh_never_resolves_path_configs_and_the_view_resolves_each_once(
    tmp_path, monkeypatch
) -> None:
    with session_gui() as gui:
        names = [f"plate-{index}" for index in range(18)]
        add_datasets(gui.session, tmp_path, *names)
        gui.settle()
        original = PipelineOrchestrator.get_effective_config
        resolutions = []

        def counted(orchestrator, **kwargs):
            resolutions.append(orchestrator.plate_path)
            return original(orchestrator, **kwargs)

        monkeypatch.setattr(PipelineOrchestrator, "get_effective_config", counted)
        gui.plate_manager.update_item_list()
        assert gui.plate_manager.item_list.count() == 18
        assert resolutions == []

        view = DatasetListView.state_of(gui.session)
        assert len(resolutions) == 18
        for row, row_state in zip(gui.plate_manager.plates, view.rows):
            rendered = gui.plate_manager._format_item_content(row, 0, None)
            assert rendered.layout.status_prefix == row_state.status_prefix
            assert row_state.output_root is not None
        assert len(resolutions) == 18


def test_progress_from_a_worker_thread_reaches_the_live_row(tmp_path) -> None:
    from pyqt_reactive.services.ui_thread_dispatch import UiThreadDispatcher

    from openhcs.authoring.session.session import DispatcherThread

    dispatcher = UiThreadDispatcher()
    try:
        with session_gui(main_thread=DispatcherThread(dispatcher)) as gui:
            (scope_id,) = add_datasets(gui.session, tmp_path, "plate")
            orchestrator = gui.session.orchestrator(scope_id)
            orchestrator._initialized = True
            orchestrator._state = OrchestratorState.EXECUTING
            gui.session.batch.begin_batch((scope_id,))
            gui.session.batch.record_execution(scope_id, "execution-1")
            gui.settle()
            (row,) = gui.plate_manager.plates
            pending = gui.plate_manager._format_item_content(row, 0, None)
            assert "Pending" in pending.layout.status_prefix

            event = ProgressEvent(
                identity=ProgressIdentity(
                    execution_id="execution-1",
                    plate_id=scope_id,
                    axis_id="A01",
                    step_name="Segment",
                ),
                phase=ProgressPhase.STEP_STARTED,
                status=ProgressStatus.RUNNING,
                percent=25.0,
                completed=1,
                total=4,
                timestamp=1.0,
                pid=1234,
            )
            worker = threading.Thread(
                target=gui.session.progress.on_progress, args=(event.to_dict(),)
            )
            worker.start()
            worker.join(timeout=2)
            assert not worker.is_alive()

            deadline = time.monotonic() + 5
            while (
                gui.session.runtime_projection.get_plate(scope_id, "execution-1")
                is None
            ):
                gui.settle()
                assert time.monotonic() < deadline, "progress never reached the UI"
                time.sleep(0.01)

            live = gui.plate_manager._format_item_content(row, 0, None)
            assert "Executing 25.0%" in live.layout.status_prefix
    finally:
        dispatcher.close()


# ---------------------------------------------------------------------------
# Dataset code documents
# ---------------------------------------------------------------------------


def test_code_document_config_refreshes_the_saved_baseline(tmp_path) -> None:
    from openhcs.pyqt_gui.widgets.shared.services.plate_manager_workflows import (
        PlateManagerCodeWorkflow,
    )

    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        config = PipelineConfig(
            napari_streaming_config=LazyNapariStreamingConfig(enabled=True, port=5557),
        )

        applied = PlateManagerCodeWorkflow(session).apply_namespace(
            {
                "plate_paths": [scope_id],
                "global_config": session.global_config,
                "per_plate_configs": {scope_id: config},
                "pipeline_data": {scope_id: []},
            }
        )

        state = ObjectStateRegistry.get_by_scope(scope_id)
        assert applied is True
        assert state.get_resolved_value("napari_streaming_config.port") == 5557
        assert state.get_saved_resolved_value("napari_streaming_config.port") == 5557
        assert state.dirty_fields == set()
        diff = {"napari_streaming_config.enabled", "napari_streaming_config.port"}
        assert diff <= state.signature_diff_fields
        state.update_parameter("napari_streaming_config.port", 5558)
        assert state.dirty_fields == {"napari_streaming_config.port"}
        state.update_parameter("napari_streaming_config.port", 5557)
        assert state.dirty_fields == set()
        assert diff <= state.signature_diff_fields


def _global_state(session, **draft) -> ObjectState:
    state = ObjectStateRegistry.get_by_scope("")
    if state is None:
        state = ObjectState(session.global_config, scope_id="")
        ObjectStateRegistry.register(state)
    for field, value in draft.items():
        state.update_parameter(field, value)
    return state


@pytest.mark.parametrize(
    "other_running,global_draft", ((False, False), (True, False), (True, True))
)
def test_selected_code_document_replaces_only_the_selected_pipeline(
    tmp_path, other_running, global_draft
) -> None:
    with session_gui() as gui:
        session = gui.session
        selected, unselected = add_datasets(session, tmp_path, "selected", "unselected")
        global_state = _global_state(session)
        saved_workers = global_state.get_saved_resolved_value("num_workers")
        if global_draft:
            global_state.update_parameter("num_workers", 37)
        session.set_pipeline(
            selected, [FunctionStep(func=percentile_normalize, name="Old selected")]
        )
        session.set_pipeline(
            unselected, [FunctionStep(func=percentile_normalize, name="Unselected")]
        )
        session.select((selected,))
        gui.settle()
        unselected_editor_state = PipelineObjectStateBinding.editor_state_for_plate(
            unselected
        )
        if other_running:
            _running(session, unselected, "untouched-run")

        result = _apply(
            _bridge(gui.plate_manager),
            _document_source(
                session,
                [selected],
                {selected: [FunctionStep(name="New selected")]},
            ),
            selection_mode=UiCodeDocumentSelectionMode.SELECTED,
        )

        assert result.applied
        if global_draft:
            assert global_state.get_resolved_value("num_workers") == 37
            assert global_state.get_saved_resolved_value("num_workers") == saved_workers
            assert global_state.dirty_fields == {"num_workers"}
        assert session.dataset_scope_ids() == [selected, unselected]
        assert _names(session.pipeline_steps(selected)) == ["New selected"]
        assert _names(session.pipeline_steps(unselected)) == ["Unselected"]
        assert (
            PipelineObjectStateBinding.editor_state_for_plate(unselected)
            == unselected_editor_state
        )
        if other_running:
            assert session.batch.active_plates == (unselected,)
            assert session.batch.execution_id(unselected) == "untouched-run"
            apply_dataset_document(
                session,
                PlateManagerCodeDocumentAuthority.from_values(
                    plate_paths=[selected],
                    global_pipeline_config=GlobalPipelineConfig(num_workers=47),
                    per_plate_configs={selected: authored_pipeline_config(selected)},
                    pipeline_data={selected: session.pipeline_steps(selected)},
                ),
                SelectedDatasetDocumentScope(selected_scope_ids=(selected,)),
            )
            assert session.batch.is_active(unselected)
            assert session.batch.execution_id(unselected) == "untouched-run"


def test_all_dataset_document_commits_an_unchanged_global_draft() -> None:
    with caller_session() as session:
        global_state = _global_state(session, num_workers=37)

        apply_dataset_document(
            session,
            PlateManagerCodeDocumentAuthority.from_values(
                plate_paths=[],
                global_pipeline_config=live_global_config(session),
                per_plate_configs={},
                pipeline_data={},
            ),
            AllDatasetDocumentScope(),
        )

        assert global_state.get_saved_resolved_value("num_workers") == 37
        assert not global_state.dirty_fields
        assert session.global_config.num_workers == 37


def test_adopting_a_global_config_preserves_a_dirty_dataset_override(tmp_path) -> None:
    with session_gui(global_config=GlobalPipelineConfig(num_workers=1)) as gui:
        session = gui.session
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        global_state = _global_state(session)
        dataset_state = ObjectStateRegistry.get_by_scope(scope_id)
        orchestrator = session.orchestrator(scope_id)
        emitted = []
        gui.plate_manager.orchestrator_config_changed.connect(
            lambda emitted_scope, config: emitted.append(
                (emitted_scope, config.num_workers)
            )
        )

        dataset_state.update_parameter("num_workers", 3)
        assert dataset_state.get_resolved_value("num_workers") == 3
        assert dataset_state.get_saved_resolved_value("num_workers") == 1
        assert dataset_state.dirty_fields == {"num_workers"}

        global_state.update_parameter("num_workers", 7)
        session.adopt_global_config(global_state.to_object(update_delegate=False))
        gui.settle()

        assert object.__getattribute__(orchestrator.pipeline_config, "num_workers") is None
        assert dataset_state.parameters["num_workers"] == 3
        assert dataset_state._saved_parameters["num_workers"] is None
        assert dataset_state.get_resolved_value("num_workers") == 3
        assert dataset_state.get_saved_resolved_value("num_workers") == 1
        assert dataset_state.dirty_fields == {"num_workers"}
        assert emitted == [(scope_id, 7)]

        global_state.mark_saved()

        assert dataset_state.parameters["num_workers"] == 3
        assert dataset_state.get_resolved_value("num_workers") == 3
        assert dataset_state.get_saved_resolved_value("num_workers") == 7
        assert dataset_state.dirty_fields == {"num_workers"}


def _render(session, *scope_ids):
    return render_dataset_document(
        session, tuple(scope_ids), selection_mode=SelectedAllSelectionMode.ALL
    )


def test_code_document_renders_each_dataset_config_once(tmp_path) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")

        document = _render(session, scope_id)

        config_source = document.source.split("per_plate_configs = {", 1)[1].split(
            "pipeline_data = {", 1
        )[0]
        assert "path_1" in config_source
        assert document.source.count(repr(scope_id)) == 1
        assert "PipelineConfig(" in config_source
        assert tuple(document.payload.per_plate_configs) == (scope_id,)
        assert isinstance(document.payload.per_plate_configs[scope_id], PipelineConfig)


def test_clean_code_document_emits_only_the_authored_fiji_override(tmp_path) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.apply_dataset_configs(
            {
                scope_id: PipelineConfig(
                    fiji_streaming_config=LazyFijiStreamingConfig(
                        well_filter="333", enabled=False
                    ),
                )
            }
        )

        source = _render(session, scope_id).source
        restored = PlateManagerCodeDocumentAuthority.from_source(source)
        imported_config_names = {
            alias.name
            for node in ast.parse(source).body
            if isinstance(node, ast.ImportFrom) and node.module == "openhcs.core.config"
            for alias in node.names
        }

        assert imported_config_names == {
            "GlobalPipelineConfig",
            "LazyFijiStreamingConfig",
            "PipelineConfig",
        }
        assert "from openhcs.core.source_bindings import" not in source
        assert "fiji_streaming_config=LazyFijiStreamingConfig(" in source
        assert "well_filter='333'" in source
        assert "enabled=False" in source
        for absent in (
            "napari_streaming_config=",
            "path_planning_config=",
            "step_materialization_config=",
        ):
            assert absent not in source
        fiji = object.__getattribute__(
            restored.per_plate_configs[scope_id], "fiji_streaming_config"
        )
        assert object.__getattribute__(fiji, "well_filter") == "333"
        assert object.__getattribute__(fiji, "enabled") is False


def test_code_document_factors_the_common_root_once(tmp_path) -> None:
    with caller_session() as session:
        screen = tmp_path / "screen"
        scope_ids = add_datasets(session, screen, "plate_A", "plate_B")

        source = _render(session, *scope_ids).source

        assert f"path_root = Path({str(screen)!r})" in source
        assert source.count(str(screen)) == 1
        assert "path_1 = path_root / 'plate_A'" in source
        assert "path_2 = path_root / 'plate_B'" in source


def test_code_document_renders_pipelines_as_function_step_lists(tmp_path) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.set_pipeline(
            scope_id, [FunctionStep(func=cellprofiler_backend.crop, name="Crop")]
        )

        document = _render(session, scope_id)

        assert "from openhcs.core.pipeline import Pipeline" not in document.source
        assert "Pipeline(" not in document.source
        assert "FunctionStep(" in document.source
        assert isinstance(document.payload.pipeline_data[scope_id], list)


def test_code_document_keeps_an_authored_dataset_override(tmp_path) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        state = ObjectStateRegistry.get_by_scope(scope_id)
        state.update_parameter("napari_streaming_config.port", 5557)

        document = _render(session, scope_id)

        assert "PipelineConfig(" in document.source
        assert "port=5557" in document.source
        assert document.payload.per_plate_configs == {
            scope_id: authored_pipeline_config(scope_id)
        }


def test_code_document_reads_the_global_config_from_object_state() -> None:
    initial = GlobalPipelineConfig(well_filter_config=WellFilterConfig(well_filter="A01"))
    with caller_session(global_config=initial) as session:
        global_state = _global_state(session)
        global_state.update_parameter("well_filter_config.well_filter", "A02")

        document = _render(session)

        assert "well_filter='A02'" in document.source
        assert "well_filter='A01'" not in document.source
        assert (
            object.__getattribute__(
                document.payload.global_pipeline_config.well_filter_config,
                "well_filter",
            )
            == "A02"
        )
        assert (
            object.__getattribute__(session.global_config.well_filter_config, "well_filter")
            == "A01"
        )


def test_a_pipeline_change_clears_stale_compilation_and_terminal_tracking(
    tmp_path,
) -> None:
    from openhcs.authoring.session.compilation import CompiledDataset
    from openhcs.core.artifact_inspection import CompiledArtifactInspection

    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.orchestrator(scope_id)._state = OrchestratorState.COMPLETED
        session.set_compiled(
            scope_id,
            CompiledDataset(
                compile_artifact_id="compile-1",
                steps=(),
                inspection=CompiledArtifactInspection(
                    compile_artifact_id="compile-1", plate_id=scope_id, steps=()
                ),
            ),
        )
        session.batch.begin_batch((scope_id,))
        session.batch.record_execution(scope_id, "execution-1")
        session.batch.mark_terminal(scope_id, TerminalExecutionStatus.COMPLETE)

        apply_dataset_document(
            session,
            PlateManagerCodeDocumentAuthority.from_values(
                plate_paths=[scope_id],
                global_pipeline_config=live_global_config(session),
                per_plate_configs={scope_id: authored_pipeline_config(scope_id)},
                pipeline_data={
                    scope_id: [FunctionStep(func=percentile_normalize, name="Replacement")]
                },
            ),
            AllDatasetDocumentScope(),
        )

        assert scope_id not in session.compiled
        assert session.batch.execution_id(scope_id) is None
        assert session.batch.terminal_status(scope_id) is None
        assert session.orchestrator(scope_id).state is OrchestratorState.READY
        assert _names(session.pipeline_steps(scope_id)) == ["Replacement"]


def _failed(execution_id: str, detail: str) -> ExecutionCompletionPayload:
    return TerminalExecutionStatus.FAILED.completion_payload(
        execution_id=execution_id,
        execution_payload={
            "status": TerminalExecutionStatus.FAILED.value,
            "error": detail,
        },
    )


def _executing_dataset(gui, tmp_path) -> str:
    session = gui.session
    (scope_id,) = add_datasets(session, tmp_path, "plate")
    session.set_pipeline(scope_id, [FunctionStep(func=percentile_normalize, name="Failing")])
    orchestrator = session.orchestrator(scope_id)
    orchestrator._initialized = True
    orchestrator._state = OrchestratorState.EXECUTING
    session.compiled[scope_id] = object()
    _running(session, scope_id, "execution-1")
    gui.settle()
    return scope_id


def test_dataset_document_edits_during_a_run_and_recovers_after_its_failure(
    tmp_path,
) -> None:
    with session_gui() as gui:
        session = gui.session
        scope_id = _executing_dataset(gui, tmp_path)
        bridge = _bridge(gui.plate_manager)
        replacement = _document_source(
            session,
            [scope_id],
            {scope_id: [FunctionStep(name="Replacement")]},
        )

        during = _apply(bridge, replacement.replace("Replacement", "Edited during run"))
        assert during.applied
        assert session.batch.execution_id(scope_id) == "execution-1"
        assert _names(session.pipeline_steps(scope_id)) == ["Edited during run"]

        session.finish_dataset_execution(_failed("execution-1", "expected"), scope_id)
        gui.settle()
        assert session.execution_state is ManagerExecutionState.IDLE
        assert session.orchestrator(scope_id).state is OrchestratorState.EXEC_FAILED
        assert session.batch.execution_id(scope_id) is None

        result = _apply(bridge, replacement)
        state = bridge.get_state_surface(
            UiStateSurfaceRequest(
                surface_id=UiStateSurfaceId.PLATE_MANAGER.value,
                selection_mode=UiCodeDocumentSelectionMode.ALL.value,
            )
        )

        (row,) = state.payload["rows"]
        assert result.applied
        assert row["orchestrator_state"] == OrchestratorState.READY.value
        assert row["compiled"] is False
        assert row["execution_active"] is False
        assert row["execution_id"] is None
        assert row["terminal_status"] is None
        assert _names(session.pipeline_steps(scope_id)) == ["Replacement"]


def test_a_failure_is_presented_only_after_the_run_finalizes(tmp_path) -> None:
    from pyqt_reactive.services.window_manager import WindowManager

    with session_gui() as gui:
        session = gui.session
        scope_id = _executing_dataset(gui, tmp_path)
        editor = gui.pipeline_editor
        presented = []
        gui.services.show_error_dialog = lambda _message: presented.append(
            (session.execution_state, session.batch.execution_id(scope_id))
        )
        window_id = PipelineEditorWidgetIdentity.require_value()
        WindowManager.register(
            window_id, editor, code_document_driver=editor.code_document_driver()
        )
        bridge = UiAgentBridgeService(
            provider_set=ObjectStateBridgeProviderSet(),
            dispatcher=InlineUiThreadDispatcher(),
        )
        replacement = PipelineDocumentCodec.render(
            PipelineDocumentCodec.from_values(
                pipeline_config=PipelineConfig(),
                pipeline_steps=[FunctionStep(func=percentile_normalize, name="Replacement")],
            )
        )

        def apply(source):
            document = bridge.get_document(
                UiCodeDocumentRequest(
                    document_id="window_code_document:pipeline_editor",
                    selection_mode=UiCodeDocumentSelectionMode.SELECTED.value,
                )
            )
            return bridge.apply_document(
                UiCodeDocumentApplyRequest(
                    document_id=document.summary.identity.document_id,
                    source=source,
                    base_revision_token=document.current_revision_token,
                    confirmation_requirement=(
                        UiBridgeConfirmationRequirement.from_flag(False)
                    ),
                )
            )

        try:
            assert apply(replacement.replace("Replacement", "Edited during run")).applied
            assert session.batch.is_active(scope_id)
            assert session.batch.execution_id(scope_id) == "execution-1"
            assert _names(session.pipeline_steps(scope_id)) == ["Edited during run"]

            worker = threading.Thread(
                target=session.finish_dataset_execution,
                args=(_failed("execution-1", "expected asynchronous failure"), scope_id),
            )
            worker.start()
            worker.join(timeout=5)
            deadline = time.monotonic() + 5
            while not presented:
                gui.settle()
                assert time.monotonic() < deadline, "failure was never presented"
                time.sleep(0.01)

            assert presented == [(ManagerExecutionState.IDLE, None)]
            assert session.orchestrator(scope_id).state is OrchestratorState.EXEC_FAILED
            assert apply(replacement).applied
            assert _names(session.pipeline_steps(scope_id)) == ["Replacement"]
            assert session.orchestrator(scope_id).state is OrchestratorState.READY
            assert scope_id not in session.compiled
        finally:
            WindowManager.unregister(window_id, editor)


# ---------------------------------------------------------------------------
# Stop and execution state
# ---------------------------------------------------------------------------


def test_stop_completion_resets_the_force_kill_state(tmp_path, monkeypatch) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        monkeypatch.setattr(session.execution_control, "stop", lambda force: None)
        _running(session, scope_id, "execution-1")
        session.stop_execution()
        assert session.execution_state is ManagerExecutionState.FORCE_KILL_READY

        session.finish_dataset_execution(
            TerminalExecutionStatus.CANCELLED.completion_payload(
                execution_id="execution-1", execution_payload={}
            ),
            scope_id,
        )

        assert session.execution_state is ManagerExecutionState.IDLE


def test_stop_follows_the_execution_state_not_the_button_text(
    tmp_path, monkeypatch
) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        forces: list[bool] = []
        monkeypatch.setattr(
            session.execution_control, "stop", lambda force: forces.append(force)
        )
        _running(session, scope_id, "execution-1")

        assert session.invoke(StopExecution, StopExecution.request()).accepted
        assert session.execution_state is ManagerExecutionState.FORCE_KILL_READY
        assert forces == [False]

        assert session.invoke(StopExecution, StopExecution.request()).accepted
        assert session.execution_state is ManagerExecutionState.STOPPING
        assert forces == [False, True]


def test_an_idle_session_rejects_stop() -> None:
    with pytest.raises(RuntimeError, match="does not accept Stop"):
        ManagerExecutionState.IDLE.stop_request()
    with caller_session() as session:
        assert (
            StopExecution.available(session, StopExecution.request()).code
            == "no_execution_running"
        )


def test_execution_state_rejects_its_text_representation() -> None:
    with caller_session() as session:
        with pytest.raises(TypeError, match="must be ManagerExecutionState"):
            session.execution_state = ManagerExecutionState.RUNNING.value
        assert session.execution_state is ManagerExecutionState.IDLE


def test_a_produced_output_dataset_selects_prepared_replay_once(
    tmp_path,
) -> None:
    from objectstate.lazy_factory import replace_raw

    global_config = GlobalPipelineConfig(dataset_source=SourceBindingsSource)
    with caller_session(global_config=global_config) as session:
        (source,) = add_datasets(session, tmp_path, "source")
        output_root = str(tmp_path / "produced")
        completion = ExecutionCompletionPayload(
            status=TerminalExecutionStatus.COMPLETE,
            execution_id="produced",
            results={},
            output_plate=ExecutionOutputPlateSummary(
                output_plate_root=output_root,
                auto_add_output_plate_to_plate_manager=True,
            ),
            traceback_text="",
            message="",
        )
        _running(session, source, "produced")

        session.finish_dataset_execution(completion, source)

        assert output_root in session.dataset_scope_ids()
        orchestrator = session.orchestrator(output_root)
        assert orchestrator.get_effective_config().dataset_source is OpenHCSDatasetSource

        orchestrator.apply_pipeline_config(
            replace_raw(orchestrator.pipeline_config, dataset_source=SourceBindingsSource)
        )
        _running(session, source, "produced-again")
        session.finish_dataset_execution(
            ExecutionCompletionPayload(
                status=TerminalExecutionStatus.COMPLETE,
                execution_id="produced-again",
                results={},
                output_plate=completion.output_plate,
                traceback_text="",
                message="",
            ),
            source,
        )

        assert session.orchestrator(output_root) is orchestrator
        assert orchestrator.get_effective_config().dataset_source is SourceBindingsSource


def test_a_standard_run_retires_only_its_targets_debug_summaries(
    tmp_path, monkeypatch
) -> None:
    with caller_session() as session:
        target, other = add_datasets(session, tmp_path, "target", "other")
        for scope_id, status in ((target, "failed"), (other, "complete")):
            session.debug_terminal_summaries[scope_id] = DebugTerminalSummary(
                debug_session_id=f"debug-{Path(scope_id).name}",
                plate_id=scope_id,
                terminal_status=status,
            )

        async def connect():
            return object()

        async def compile_before_execution(requests, config_params={}):
            raise RuntimeError("stop after admission")

        monkeypatch.setattr(session, "connect_client", connect)
        monkeypatch.setattr(
            session.compile_batch, "compile_before_execution", compile_before_execution
        )
        _ready(session, target)

        asyncio.run(session.run_datasets((target,)))

        assert target not in session.debug_terminal_summaries
        assert session.debug_terminal_summaries[other].debug_session_id == "debug-other"
