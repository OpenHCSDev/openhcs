"""The compile and run buttons follow the session's endpoint and execution state."""

from __future__ import annotations

import pytest
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.authoring.session.operations.datasets import (
    CompileDatasets,
    ConnectServer,
    RunDatasets,
    StopExecution,
    WaitForServer,
)
from openhcs.authoring.session.views import DatasetListView
from openhcs.core.execution_state import ManagerExecutionState
from openhcs.core.steps.function_step import FunctionStep
from openhcs.pyqt_gui.config import get_default_ui_config
from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
from tests.unit.pyqt_gui.session_harness import (
    release_widgets,
    GuiServiceStub,
    add_datasets,
    caller_session,
    qt_app,
)


def _endpoint(monkeypatch, session, phase: EndpointStartupPhase) -> None:
    monkeypatch.setattr(
        session, "endpoint_status", lambda: EndpointStartupStatus(phase, "test")
    )


@pytest.mark.parametrize(
    "phase, expected",
    [
        (EndpointStartupPhase.DISCONNECTED, ConnectServer),
        (EndpointStartupPhase.FAILED, ConnectServer),
        (EndpointStartupPhase.CONNECTED, CompileDatasets),
        *[
            (phase, WaitForServer)
            for phase in EndpointStartupPhase
            if phase
            not in {
                EndpointStartupPhase.DISCONNECTED,
                EndpointStartupPhase.FAILED,
                EndpointStartupPhase.CONNECTED,
            }
        ],
    ],
)
def test_endpoint_phase_resolves_the_compile_slot(monkeypatch, phase, expected):
    with caller_session() as session:
        _endpoint(monkeypatch, session, phase)
        assert CompileDatasets.resolved(session) is expected


def test_connect_needs_no_dataset_and_startup_is_never_available(tmp_path):
    with caller_session() as session:
        (scope_id,) = add_datasets(session, tmp_path, "plate")
        session.orchestrator(scope_id)._state = (
            session.orchestrator(scope_id)._state.READY
        )
        session.set_pipeline(scope_id, [FunctionStep(name="Step")])
        assert ConnectServer.available(session, ConnectServer.request()) is None
        for selection in ((), (scope_id,)):
            assert (
                WaitForServer.available(
                    session, WaitForServer.request_for_selection(session, selection)
                ).code
                == "execution_server_starting"
            )
        assert CompileDatasets.available(
            session, CompileDatasets.request_for_selection(session, ())
        )
        assert (
            CompileDatasets.available(
                session, CompileDatasets.request_for_selection(session, (scope_id,))
            )
            is None
        )


def test_connection_variants_share_the_compile_button():
    assert len(PlateManagerWidget.BUTTON_CONFIGS) == len(DatasetListView.operations)
    assert ConnectServer not in DatasetListView.operations
    assert WaitForServer not in DatasetListView.operations
    assert StopExecution not in DatasetListView.operations


@pytest.mark.parametrize("phase", EndpointStartupPhase)
@pytest.mark.parametrize("compiled", [False, True])
@pytest.mark.parametrize("compile_pending", [False, True])
@pytest.mark.parametrize("execution_state", ManagerExecutionState)
def test_run_button_uses_endpoint_readiness_without_disabling_stop(
    tmp_path, monkeypatch, phase, compiled, compile_pending, execution_state
):
    app = qt_app()
    with caller_session() as session:
        manager = PlateManagerWidget(
            GuiServiceStub(), session, gui_config=get_default_ui_config()
        )
        try:
            (scope_id,) = add_datasets(session, tmp_path, "plate")
            _endpoint(monkeypatch, session, phase)
            if compiled:
                session.compiled[scope_id] = object()
            if compile_pending:
                session.compile_pending.add(scope_id)
            session.execution_state = execution_state
            app.processEvents()
            assert manager.selection_scope_ids() == (scope_id,)
            manager.update_button_states()
            expected = {
                ManagerExecutionState.IDLE: compiled
                and not compile_pending
                and phase is EndpointStartupPhase.CONNECTED,
                ManagerExecutionState.RUNNING: True,
                ManagerExecutionState.STOPPING: False,
                ManagerExecutionState.FORCE_KILL_READY: True,
            }[execution_state]
            run_button = manager.buttons[RunDatasets.operation_id]
            assert run_button.isEnabled() is expected
            assert run_button.text() == execution_state.run_button_text
        finally:
            manager.cleanup()
            manager.close()
            release_widgets(qt_app(), manager)
