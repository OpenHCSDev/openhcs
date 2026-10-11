"""One dataset through the session, driven through the Qt widgets.

The same SessionOperation classes as the headless MCP journey in
tests/integration/test_session_journey.py run here through the plate manager
on a real execution server; only the client differs.
"""

from __future__ import annotations

import time
from pathlib import Path

import pytest
from objectstate.object_state import ObjectStateRegistry
from PyQt6.QtWidgets import QApplication
from pyqt_reactive.services.ui_thread_dispatch import UiThreadDispatcher

from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    CompileDatasets,
    InitializeDatasets,
    RunDatasets,
)
from openhcs.authoring.session.session import DispatcherThread, Session
from openhcs.authoring.session.views import DatasetListView
from openhcs.core.config import GlobalPipelineConfig
from openhcs.pyqt_gui.config import get_default_ui_config
from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
from openhcs.runtime.zmq_config import OpenHCSZMQConfig
from tests.integration.test_session_journey import (
    STAGE_TIMEOUT_SECONDS,
    _port,
    _synthetic_dataset,
)
from tests.unit.pyqt_gui.session_harness import GuiServiceStub, release_widgets


@pytest.fixture(autouse=True)
def fresh_object_state_registry():
    """The session starts from an empty dataset list."""

    ObjectStateRegistry.clear()
    yield
    ObjectStateRegistry.clear()


def test_gui_journey_runs_the_same_operations_through_the_widgets(
    tmp_path: Path,
) -> None:
    application = QApplication.instance() or QApplication([])
    root, source = _synthetic_dataset(tmp_path)
    dispatcher = UiThreadDispatcher()
    session = Session(
        transport_config=OpenHCSZMQConfig(default_port=_port(1), persistent=False),
        global_config=GlobalPipelineConfig(),
        main_thread=DispatcherThread(dispatcher),
    )
    services = GuiServiceStub()
    manager = PlateManagerWidget(
        services, session, gui_config=get_default_ui_config()
    )
    try:
        assert session.invoke(AddDatasets, AddDatasets.request(roots=(str(root),))).accepted
        (scope_id,) = session.dataset_scope_ids()
        session.set_pipeline_source(scope_id, source)
        application.processEvents()
        assert [row.scope_id for row in manager.plates] == [scope_id]
        manager.item_list.setCurrentRow(0)
        application.processEvents()
        assert manager.selection_scope_ids() == (scope_id,)

        def wait_until(condition, label) -> None:
            deadline = time.monotonic() + STAGE_TIMEOUT_SECONDS
            while not condition():
                application.processEvents()
                assert time.monotonic() < deadline, label
                time.sleep(0.05)

        for operation, finished in (
            (InitializeDatasets, lambda row: row.initialized and not row.init_pending),
            (CompileDatasets, lambda row: row.compiled and not row.compile_pending),
            (
                RunDatasets,
                lambda row: row.terminal_status is not None and not row.execution_active,
            ),
        ):
            if operation is CompileDatasets:
                # Disconnected, the compile button is Connect; connect first.
                assert manager.buttons[operation.operation_id].text() == "Connect"
                manager.handle_button_action(operation.operation_id)
                wait_until(
                    lambda: CompileDatasets.resolved(session) is CompileDatasets,
                    "connect",
                )
                manager.update_button_states()
            assert manager.buttons[operation.operation_id].isEnabled(), operation
            manager.handle_button_action(operation.operation_id)
            deadline = time.monotonic() + STAGE_TIMEOUT_SECONDS
            while True:
                application.processEvents()
                (row,) = DatasetListView.state_of(session).rows
                if finished(row):
                    break
                assert time.monotonic() < deadline, (operation, row)
                time.sleep(0.05)
        assert row.terminal_status == "complete", row
        wait_until(lambda: not session.execution_state.busy, "batch finished")
        application.processEvents()
        assert manager.buttons[RunDatasets.operation_id].text() == "Run"
    finally:
        manager.cleanup()
        manager.close()
        release_widgets(application, manager)
        session.close()
        dispatcher.close()
