from __future__ import annotations

import asyncio
from contextlib import contextmanager
from dataclasses import dataclass

from objectstate.lazy_factory import PREVIEW_LABEL_REGISTRY
from PyQt6.QtWidgets import QApplication
from pyqt_reactive.theming import ColorScheme

from openhcs.core.artifacts import MeasurementsArtifactType
from openhcs.core.config import NapariStreamingConfig
from openhcs.core.debug import (
    DebugArtifactRef,
    DebugCommand,
    DebugCommandType,
    DebugCursor,
    DebugEventType,
    DebugProgressContext,
    DebugReplayMode,
    DebugSession,
    DebugTerminalSummary,
    FileManagerDebugSnapshotStore,
)
from openhcs.core.debug_views import DebugViewModel
from openhcs.authoring.session.progress_notifications import (
    DebugSnapshotAvailableNotification,
)
from openhcs.core.execution_state import ManagerExecutionState, TerminalExecutionStatus
from openhcs.core.progress import (
    ProgressEvent,
    ProgressIdentity,
    ProgressPhase,
    ProgressStatus,
)
from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.widgets.debug_toolbar import DebugToolbarWidget
from openhcs.pyqt_gui.widgets.pipeline_editor import PipelineEditorWidget
from openhcs.pyqt_gui.widgets.shared.services.debug_session_projection import (
    PipelineDebugPauseBoundaryState,
    PipelineDebugSessionContext,
    PipelineDebugTargetState,
)
from openhcs.pyqt_gui.widgets.shared.services.pipeline_debug_actions import (
    PipelineDebugActionDeclarationBase,
    PipelineDebugCommandActionDeclaration,
)
from openhcs.pyqt_gui.windows.debug_inspector_window import (
    DebugArtifactMaterializeRequest,
)
from tests.unit.pyqt_gui.session_harness import (
    release_widgets,
    GuiServiceStub,
    add_datasets,
    caller_session,
    qt_app,
)


class QtApplicationHarness:
    """Nominal owner for the QApplication singleton used by GUI smoke tests."""

    app_instance: QApplication | None = None

    @classmethod
    def app(cls) -> QApplication:
        cls.app_instance = QApplication.instance() or QApplication([])
        return cls.app_instance


def debug_toolbar_context(
    *,
    initialized: bool = True,
    compiled: bool = True,
    session: DebugSession | None = None,
    terminal_summary: DebugTerminalSummary | None = None,
    manager_execution_state: ManagerExecutionState = ManagerExecutionState.IDLE,
    pause_step_indices: tuple[int, ...] = (1,),
) -> PipelineDebugSessionContext:
    return PipelineDebugSessionContext(
        target=PipelineDebugTargetState(
            current_plate_scope_id="plate",
            pipeline_scope_id="plate::pipeline",
            initialized=initialized,
            compiled=compiled,
        ),
        session=session,
        terminal_summary=terminal_summary,
        pause_boundaries=PipelineDebugPauseBoundaryState(pause_step_indices),
        manager_execution_state=manager_execution_state,
    )


def active_debug_session() -> DebugSession:
    return DebugSession.create(plate_id="plate")


def test_debug_toolbar_emits_typed_command() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    toolbar.set_debug_session_context(debug_toolbar_context())
    commands: list[DebugCommand] = []
    toolbar.command_requested.connect(commands.append)

    toolbar.buttons[DebugCommandType.STEP].click()

    assert commands == [DebugCommand(DebugCommandType.STEP)]


def test_debug_toolbar_debug_button_runs_debug_execution() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    toolbar.set_debug_session_context(debug_toolbar_context())
    commands: list[DebugCommand] = []
    toolbar.command_requested.connect(commands.append)

    toolbar.buttons[DebugCommandType.RUN].click()

    assert toolbar.buttons[DebugCommandType.RUN].text() == "Start Debug"
    assert toolbar.phase_label.text() == "Ready"
    assert commands == [DebugCommand(DebugCommandType.RUN)]


def test_debug_toolbar_renders_secondary_commands_as_session_buttons() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    toolbar.set_debug_session_context(debug_toolbar_context())
    commands: list[DebugCommand] = []
    toolbar.command_requested.connect(commands.append)

    assert DebugCommandType.TOGGLE not in toolbar.buttons
    assert DebugCommandType.CHOOSE_SOURCE_GROUP in toolbar.buttons
    assert DebugCommandType.RANDOM_SOURCE_GROUP not in toolbar.buttons
    assert DebugCommandType.STOP in toolbar.buttons

    toolbar.buttons[DebugCommandType.CHOOSE_SOURCE_GROUP].click()
    toolbar.set_debug_session_context(
        debug_toolbar_context(session=active_debug_session())
    )
    toolbar.buttons[DebugCommandType.STOP].click()

    assert commands == [
        DebugCommand(DebugCommandType.CHOOSE_SOURCE_GROUP),
        DebugCommand(DebugCommandType.STOP),
    ]


def test_debug_toolbar_runtime_inspection_action_emits_separate_signal() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    requests = []
    toolbar.runtime_inspection_requested.connect(lambda: requests.append("runtime"))

    assert toolbar.runtime_inspection_button is not None
    toolbar.set_debug_session_context(
        debug_toolbar_context(session=active_debug_session())
    )
    toolbar.runtime_inspection_button.click()

    assert requests == ["runtime"]


def test_debug_toolbar_enables_controls_together() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()

    assert all(not button.isEnabled() for button in toolbar.buttons.values())
    assert toolbar.runtime_inspection_button is not None
    assert not toolbar.runtime_inspection_button.isEnabled()


def test_debug_toolbar_session_only_controls_follow_active_session() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    toolbar.set_debug_session_context(debug_toolbar_context())

    assert toolbar.buttons[DebugCommandType.RUN].isEnabled()
    assert toolbar.buttons[DebugCommandType.STEP].isEnabled()
    assert toolbar.buttons[DebugCommandType.CHOOSE_SOURCE_GROUP].isEnabled()
    assert not toolbar.buttons[DebugCommandType.RESTART].isEnabled()
    assert not toolbar.buttons[DebugCommandType.STOP].isEnabled()
    assert toolbar.runtime_inspection_button is not None
    assert not toolbar.runtime_inspection_button.isEnabled()

    toolbar.set_debug_session_context(
        debug_toolbar_context(session=active_debug_session())
    )

    assert toolbar.phase_label.text() == "Debug Active"
    assert toolbar.buttons[DebugCommandType.RUN].text() == "Continue"
    assert toolbar.buttons[DebugCommandType.RESTART].isEnabled()
    assert toolbar.buttons[DebugCommandType.STOP].isEnabled()
    assert toolbar.runtime_inspection_button.isEnabled()


def test_debug_toolbar_terminal_summary_retire_matching_local_session() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    session = active_debug_session()
    cursor = DebugCursor(
        step_index=0,
        step_scope_id="step-0",
        group_key="default",
        invocation_key="default:0:correct_illumination_apply",
    )
    session = session.with_cursor(cursor).with_command(DebugCommandType.STEP)
    terminal_summary = DebugTerminalSummary(
        debug_session_id=session.debug_session_id,
        plate_id="plate",
        terminal_status="complete",
        cursor=cursor,
        command_type=DebugCommandType.STEP,
        axis_id=session.axis_id,
        snapshot_id="snapshot-1",
        snapshot_store_ref="/debug",
    )

    toolbar.set_debug_session_context(
        debug_toolbar_context(
            session=session,
            terminal_summary=terminal_summary,
        )
    )

    assert toolbar.phase_label.text() == "Debug Complete"
    assert toolbar.buttons[DebugCommandType.RUN].text() == "Start Debug"
    assert not toolbar.buttons[DebugCommandType.RESTART].isEnabled()
    assert not toolbar.buttons[DebugCommandType.STOP].isEnabled()
    assert toolbar.runtime_inspection_button is not None
    assert not toolbar.runtime_inspection_button.isEnabled()


def test_debug_toolbar_projects_pending_execution_state() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()
    toolbar.set_debug_session_context(
        debug_toolbar_context(
            manager_execution_state=ManagerExecutionState.RUNNING,
        )
    )

    assert not toolbar.buttons[DebugCommandType.RUN].isEnabled()
    assert not toolbar.buttons[DebugCommandType.STEP].isEnabled()
    assert not toolbar.buttons[DebugCommandType.RESTART].isEnabled()
    assert not toolbar.buttons[DebugCommandType.CHOOSE_SOURCE_GROUP].isEnabled()
    assert toolbar.buttons[DebugCommandType.STOP].isEnabled()
    assert toolbar.runtime_inspection_button is not None
    assert not toolbar.runtime_inspection_button.isEnabled()


def test_debug_toolbar_omits_random_source_group_action() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()

    assert DebugCommandType.RANDOM_SOURCE_GROUP not in toolbar.buttons


def test_debug_toolbar_uses_shared_button_panel_styling() -> None:
    QtApplicationHarness.app()
    color_scheme = ColorScheme(button_text=(255, 0, 0))

    toolbar = DebugToolbarWidget(color_scheme=color_scheme)

    assert toolbar.button_panel is not None
    assert "color: #ff0000" in toolbar.buttons[DebugCommandType.STEP].styleSheet()


def test_debug_toolbar_disables_run_to_pause_without_pause_boundary() -> None:
    QtApplicationHarness.app()
    toolbar = DebugToolbarWidget()

    toolbar.set_debug_session_context(debug_toolbar_context(pause_step_indices=()))

    assert not toolbar.buttons[DebugCommandType.RUN_TO_PAUSE].isEnabled()
    assert (
        "debug-pause step" in toolbar.buttons[DebugCommandType.RUN_TO_PAUSE].toolTip()
    )


class DebugInspectorRecorder:
    """Recorder replacing the heavy Qt inspector in route tests."""

    def __init__(self, parent=None) -> None:
        del parent
        self.snapshots = []
        self.local_loads = []
        self.store_loads = []
        self.show_calls = 0
        self.raise_calls = 0
        self.inspection_view_models = []
        self.artifact_export_requested = SignalConnectRecorder()
        self.artifact_open_requested = SignalConnectRecorder()

    def set_inspection_view_model(self, view_model) -> None:
        self.inspection_view_models.append(view_model)

    def set_snapshot(self, snapshot) -> None:
        self.snapshots.append(snapshot)

    def load_snapshot(self, **kwargs) -> None:
        self.local_loads.append(kwargs)

    def load_snapshot_from_store(self, *, store, snapshot_id) -> None:
        self.store_loads.append((store, snapshot_id))

    def show(self) -> None:
        self.show_calls += 1

    def raise_(self) -> None:
        self.raise_calls += 1


class SignalConnectRecorder:
    """Signal-like object that records connected callables."""

    def __init__(self) -> None:
        self.connected = []

    def connect(self, callback) -> None:
        self.connected.append(callback)


@dataclass
class DebugEditor:
    """A pipeline editor over a session with one dataset whose work is recorded."""

    session: object
    scope_id: str
    editor: PipelineEditorWidget
    started: list
    messages: list[str]

    @property
    def workflow(self):
        return self.editor.debug_workflow

    def debug_runs(self) -> list[dict]:
        return [
            {"scope_id": args[0], **kwargs}
            for work, args, kwargs in self.started
            if work == self.session.run_debug
        ]


@contextmanager
def debug_editor(tmp_path, monkeypatch, *, run_started_work: bool = False):
    app = qt_app()
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        orchestrator = session.orchestrator(scope_id)
        orchestrator._state = type(orchestrator.state).READY
        session.set_pipeline(
            scope_id,
            [
                FunctionStep(func=_identity, name="first"),
                FunctionStep(func=_identity, name="paused", debug_pause=True),
                FunctionStep(func=_identity, name="last"),
            ],
        )
        started = []

        def start(work, *args, **kwargs):
            started.append((work, args, kwargs))
            if run_started_work:
                asyncio.run(work(*args, **kwargs))

        monkeypatch.setattr(session, "start", start)
        editor = PipelineEditorWidget(GuiServiceStub(file_manager=object()), session)
        messages: list[str] = []
        editor.status_message.connect(messages.append)
        app.processEvents()
        try:
            yield DebugEditor(session, scope_id, editor, started, messages)
        finally:
            editor.close()
            release_widgets(qt_app(), editor)


def _identity(image):
    return image


def segment(image):
    return image


def finish(image):
    return image


def _cursor(step_index: int, invocation: str) -> DebugCursor:
    return DebugCursor(
        step_index=step_index,
        step_scope_id=f"step-{step_index}",
        group_key="default",
        invocation_key=f"default:0:{invocation}",
    )


def test_pipeline_editor_routes_stop_debug_command_to_the_session(
    tmp_path, monkeypatch
) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        stops = []
        monkeypatch.setattr(harness.session, "stop_execution", stops.append)

        harness.workflow.handle_command(DebugCommand(DebugCommandType.STOP))

        assert stops == [True]
        assert harness.messages[-1] == "Requested debug execution stop."


def test_pipeline_editor_has_route_for_every_debug_command() -> None:
    command_types = {
        declaration.command_type()
        for declaration in PipelineDebugActionDeclarationBase.__registry__.values()
        if issubclass(declaration, PipelineDebugCommandActionDeclaration)
    }
    assert command_types == set(DebugCommandType)


def test_streaming_preview_label_is_declared_on_config_class() -> None:
    assert PREVIEW_LABEL_REGISTRY[NapariStreamingConfig] == "NAP"


def test_pipeline_editor_dispatches_pause_step_indices(tmp_path, monkeypatch) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        assert harness.workflow.pause_step_indices() == (1,)

        harness.workflow.run_command(DebugCommandType.RUN_TO_PAUSE)

        assert harness.debug_runs() == [
            {
                "scope_id": harness.scope_id,
                "command_type": DebugCommandType.RUN_TO_PAUSE,
                "pause_step_indices": (1,),
                "start_step_index": 0,
                "start_after_invocation_key": None,
            }
        ]
        assert "Submitting debug run to pause" in harness.messages[-1]


def test_pipeline_editor_step_advances_from_the_current_invocation(
    tmp_path, monkeypatch
) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = DebugSession.create(
            plate_id=harness.scope_id
        ).with_cursor(_cursor(1, "segment"))

        harness.workflow.handle_command(DebugCommand(DebugCommandType.STEP))

        (run,) = harness.debug_runs()
        assert run["command_type"] is DebugCommandType.STEP
        assert run["start_step_index"] == 1
        assert run["start_after_invocation_key"] == "default:0:segment"


def test_pipeline_editor_restarts_from_the_dirty_debug_cursor(
    tmp_path, monkeypatch
) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = (
            DebugSession.create(plate_id=harness.scope_id)
            .with_cursor(_cursor(1, "segment"))
            .mark_dirty_from_cursor()
        )

        harness.workflow.run_command(DebugCommandType.RESTART)

        (run,) = harness.debug_runs()
        assert run["start_step_index"] == 1


def test_pipeline_editor_step_replays_from_terminal_debug_cursor(
    tmp_path, monkeypatch
) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_terminal_summaries[harness.scope_id] = (
            DebugTerminalSummary(
                debug_session_id="debug-terminal",
                plate_id=harness.scope_id,
                terminal_status="complete",
                cursor=_cursor(2, "measure"),
                command_type=DebugCommandType.STEP,
                axis_id="A01",
            )
        )

        harness.workflow.run_command(DebugCommandType.STEP)

        assert harness.debug_runs() == [
            {
                "scope_id": harness.scope_id,
                "command_type": DebugCommandType.STEP,
                "pause_step_indices": (1,),
                "start_step_index": 2,
                "start_after_invocation_key": "default:0:measure",
            }
        ]
        assert harness.scope_id not in harness.session.debug_terminal_summaries


def test_debug_context_prefers_terminal_state_over_a_stale_inspected_session(
    tmp_path, monkeypatch
) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.compiled[harness.scope_id] = object()
        harness.session.inspected_debug_sessions[harness.scope_id] = (
            DebugSession.create(
                plate_id=harness.scope_id, execution_id="old-exec", axis_id="A01"
            ).with_cursor(_cursor(0, "first"))
        )
        summary = DebugTerminalSummary(
            debug_session_id="debug-terminal",
            plate_id=harness.scope_id,
            terminal_status="complete",
            cursor=_cursor(2, "measure"),
            command_type=DebugCommandType.STEP,
            axis_id="A01",
        )
        harness.session.debug_terminal_summaries[harness.scope_id] = summary

        context = harness.editor.debug_session_context()

        assert context.active_session is None
        assert context.phase.value == "terminal_complete"
        assert context.terminal_summary is summary


def test_runtime_inspection_renders_the_active_session(tmp_path, monkeypatch) -> None:
    from openhcs.pyqt_gui.widgets.shared.services import pipeline_editor_workflows

    monkeypatch.setattr(
        pipeline_editor_workflows, "DebugInspectorWindow", DebugInspectorRecorder
    )
    with debug_editor(tmp_path, monkeypatch, run_started_work=True) as harness:
        session = DebugSession.create(
            plate_id=harness.scope_id, execution_id="exec-1", axis_id="A01"
        )
        harness.session.debug_sessions[harness.scope_id] = session
        inspected = []

        async def inspect_runtime(*, debug_session_id):
            inspected.append(debug_session_id)
            return DebugViewModel(title=f"Runtime {debug_session_id}", sections=())

        monkeypatch.setattr(
            harness.session.debug_runs, "inspect_runtime", inspect_runtime
        )

        harness.workflow.show_runtime_inspection()

        inspector = harness.editor.debug_inspector_window
        assert inspected == [session.debug_session_id]
        assert inspector.inspection_view_models == [
            DebugViewModel(title=f"Runtime {session.debug_session_id}", sections=())
        ]
        assert inspector.show_calls == 1
        assert inspector.raise_calls == 1


def test_runtime_inspection_requires_an_active_session(tmp_path, monkeypatch) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.workflow.show_runtime_inspection()

        assert harness.started == []
        assert harness.messages[-1] == (
            "Runtime inspection requires an active debug session."
        )


def test_pipeline_change_marks_the_debug_session_dirty(tmp_path, monkeypatch) -> None:
    from openhcs.authoring.session.events import StatusReported

    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = DebugSession.create(
            plate_id=harness.scope_id
        ).with_cursor(_cursor(1, "segment"))
        statuses = []
        harness.session.subscribe(
            lambda record: statuses.append(record.event.text)
            if isinstance(record.event, StatusReported)
            else None
        )

        harness.session.set_pipeline(
            harness.scope_id, [FunctionStep(func=_identity, name="changed")]
        )

        assert [
            step.name for step in harness.session.pipeline_steps(harness.scope_id)
        ] == ["changed"]
        assert (
            harness.session.debug_sessions[harness.scope_id].dirty_from_cursor
            is not None
        )
        assert statuses == [
            "Debug snapshots downstream of the current cursor are dirty."
        ]


def test_invocation_badges_mark_the_cursor_row_and_dirty_replay_start(
    tmp_path, monkeypatch
) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = (
            DebugSession.create(plate_id=harness.scope_id)
            .with_cursor(_cursor(1, "segment"))
            .mark_dirty_from_cursor()
        )
        presentation = harness.editor.function_presentation

        def texts(step_index=None):
            return tuple(
                badge.text
                for badge in presentation.invocation_badges(
                    [segment, finish], step_index=step_index
                )
            )

        assert texts() == ("default[0] segment", "default[1] finish")
        assert texts(0) == ("default[0] segment", "default[1] finish")
        assert texts(1) == ("▶ default[0] segment *", "default[1] finish")


def test_badge_provider_uses_the_rendered_step_index(tmp_path, monkeypatch) -> None:
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = DebugSession.create(
            plate_id=harness.scope_id
        ).with_cursor(_cursor(1, "segment"))
        presentation = harness.editor.function_presentation
        first = FunctionStep(func=segment, name="first")
        second = FunctionStep(func=segment, name="second")

        first_badges = presentation.badge_provider(first, step_index=0)
        second_badges = presentation.badge_provider(second, step_index=1)

        assert first_badges("default", 0, segment) is None
        assert second_badges("default", 0, segment) == "▶ default[0] segment"


def test_inactive_invocation_badges_stay_out_of_titles(tmp_path, monkeypatch) -> None:
    def crop(image):
        return image

    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = DebugSession.create(
            plate_id=harness.scope_id
        ).with_cursor(_cursor(1, "segment"))
        presentation = harness.editor.function_presentation

        badges = presentation.badge_provider(FunctionStep(func=crop), step_index=0)

        assert badges("default", 0, crop) is None
        assert presentation.format_func_preview(crop) == "func=crop"


def debug_snapshot_notification(
    scope_id: str,
    *,
    snapshot_store_backend: str | None,
) -> DebugSnapshotAvailableNotification:
    debug_context = DebugProgressContext(
        debug_session_id="debug-1",
        snapshot_id="snap-1",
        cursor=_cursor(1, "segment"),
        event_type=DebugEventType.AFTER_INVOCATION,
        snapshot_store_ref="/debug",
        snapshot_store_backend=snapshot_store_backend,
    )
    return DebugSnapshotAvailableNotification(
        progress_event=ProgressEvent(
            identity=ProgressIdentity(
                execution_id="exec-1",
                plate_id=scope_id,
                axis_id="A01",
                step_name="step",
            ),
            phase=ProgressPhase.PATTERN_GROUP,
            status=ProgressStatus.SUCCESS,
            percent=100,
            completed=1,
            total=1,
            timestamp=1.0,
            pid=123,
            context=debug_context.to_progress_context(),
        ),
        debug_context=debug_context,
    )


def test_snapshot_loads_from_the_vfs_store_and_moves_the_displayed_cursor(
    tmp_path, monkeypatch
) -> None:
    from openhcs.pyqt_gui.widgets.shared.services import pipeline_editor_workflows

    monkeypatch.setattr(
        pipeline_editor_workflows, "DebugInspectorWindow", DebugInspectorRecorder
    )
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.workflow.show_snapshot(
            debug_snapshot_notification(
                harness.scope_id, snapshot_store_backend="memory"
            )
        )

        inspector = harness.editor.debug_inspector_window
        assert inspector.local_loads == []
        ((store, snapshot_id),) = inspector.store_loads
        assert isinstance(store, FileManagerDebugSnapshotStore)
        assert store.filemanager is harness.editor.service_adapter.get_file_manager()
        assert store.backend == "memory"
        assert snapshot_id == "snap-1"
        displayed = harness.session.displayed_debug_session(harness.scope_id)
        assert displayed.debug_session_id == "debug-1"
        assert displayed.cursor == _cursor(1, "segment")
        assert inspector.artifact_export_requested.connected == [
            harness.workflow.handle_artifact_export_request
        ]
        assert inspector.artifact_open_requested.connected == [
            harness.workflow.handle_artifact_open_request
        ]


def test_debug_artifact_export_runs_through_the_session(tmp_path, monkeypatch) -> None:
    from openhcs.pyqt_gui.widgets.shared.services import pipeline_editor_workflows

    monkeypatch.setattr(
        pipeline_editor_workflows.QFileDialog,
        "getExistingDirectory",
        lambda *_args, **_kwargs: "/tmp/debug-export",
    )
    with debug_editor(tmp_path, monkeypatch) as harness:
        harness.session.debug_sessions[harness.scope_id] = DebugSession(
            debug_session_id="debug-1",
            plate_id=harness.scope_id,
            snapshot_store_ref="/debug",
            snapshot_store_backend="memory",
        )
        artifact_ref = DebugArtifactRef(
            kind=MeasurementsArtifactType,
            name="Measurements",
            cursor=DebugCursor(0, "scope", "default", "default:0:measure"),
            storage_ref="/debug/measurements.csv",
            storage_backend="memory",
        )

        harness.workflow.handle_artifact_export_request(
            DebugArtifactMaterializeRequest(artifact_ref=artifact_ref)
        )

        assert harness.started == [
            (
                harness.session.debug_runs.export_artifact,
                (),
                {
                    "debug_session_id": "debug-1",
                    "artifact_ref": artifact_ref,
                    "export_root": "/tmp/debug-export",
                    "snapshot_store_ref": "/debug",
                    "snapshot_store_backend": "memory",
                },
            )
        ]


def test_session_reuses_the_persistent_paused_worker_across_commands(
    tmp_path, monkeypatch
) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        orchestrator = session.orchestrator(scope_id)
        orchestrator._state = type(orchestrator.state).READY
        compiled, submitted, worker_commands = [], [], []

        async def connect():
            return object()

        async def compile_artifact_id(request, debug_request):
            compiled.append(debug_request)
            return "debug-compile"

        async def submit(request, *, compile_artifact_id, debug_request):
            submitted.append((request.scope_id, compile_artifact_id))

        async def send_worker_command(*, debug_session_id, command_type):
            worker_commands.append((debug_session_id, command_type))

        monkeypatch.setattr(session, "connect_client", connect)
        monkeypatch.setattr(
            session.debug_runs, "compile_artifact_id", compile_artifact_id
        )
        monkeypatch.setattr(session.debug_runs, "submit", submit)
        monkeypatch.setattr(
            session.debug_runs, "send_worker_command", send_worker_command
        )

        asyncio.run(
            session.run_debug(
                scope_id,
                command_type=DebugCommandType.RUN_TO_PAUSE,
                pause_step_indices=(1,),
            )
        )
        debug_session = session.debug_sessions[scope_id]
        for command in (
            DebugCommandType.STEP,
            DebugCommandType.RUN,
            DebugCommandType.STOP,
        ):
            asyncio.run(session.run_debug(scope_id, command_type=command))

        (debug_request,) = compiled
        assert debug_request.debug_session_id == debug_session.debug_session_id
        assert debug_request.snapshot_store_ref == str(
            tmp_path / "plate" / ".openhcs_debug"
        )
        assert debug_request.snapshot_store_backend is None
        assert debug_request.command_type is DebugCommandType.RUN_TO_PAUSE
        assert debug_request.selected_source_group is None
        assert debug_request.pause_step_indices == (1,)
        assert debug_request.start_step_index == 0
        assert debug_request.start_after_invocation_key is None
        assert debug_request.replay_mode is DebugReplayMode.PERSISTENT_PAUSED_WORKER
        assert submitted == [(scope_id, "debug-compile")]
        assert worker_commands == [
            (debug_session.debug_session_id, DebugCommandType.STEP),
            (debug_session.debug_session_id, DebugCommandType.RUN),
            (debug_session.debug_session_id, DebugCommandType.STOP),
        ]
        assert scope_id not in session.debug_sessions


def test_dataset_completion_retires_its_debug_session(tmp_path) -> None:
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        debug_session = DebugSession.create(plate_id=scope_id)
        session.debug_sessions[scope_id] = debug_session
        session.batch.begin_batch((scope_id,))
        session.batch.record_execution(scope_id, "exec-1")
        session.execution_state = ManagerExecutionState.RUNNING

        session.finish_dataset_execution(
            TerminalExecutionStatus.FAILED.completion_payload(
                execution_id="exec-1", execution_payload={}
            ),
            scope_id,
        )

        assert scope_id not in session.debug_sessions
        summary = session.debug_terminal_summaries[scope_id]
        assert summary.debug_session_id == debug_session.debug_session_id
        assert summary.terminal_status == TerminalExecutionStatus.FAILED.value
