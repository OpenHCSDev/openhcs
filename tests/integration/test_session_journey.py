"""One dataset through the session, headless over MCP and in the Qt GUI.

Both journeys add a synthetic dataset, give it a pipeline, initialize, compile
and run it on a real execution server, following the session's events. They
use the same SessionOperation classes; only the client differs.
"""

from __future__ import annotations

import asyncio
import os
import time
from pathlib import Path

import pytest
from objectstate.object_state import ObjectStateRegistry

from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    CompileDatasets,
    InitializeDatasets,
    RunDatasets,
)
from openhcs.authoring.session.session import CallerThread
from openhcs.authoring.session.views import DatasetListView
from openhcs.core.config import PipelineConfig
from openhcs.core.pipeline_document import PipelineDocumentCodec
from openhcs.core.steps import FunctionStep
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.processing.backends.processors.numpy_processor import gaussian_blur
from openhcs.runtime.zmq_config import OpenHCSZMQConfig

STAGE_TIMEOUT_SECONDS = 300.0


@pytest.fixture(autouse=True)
def fresh_object_state_registry():
    """Each journey's session starts from an empty dataset list."""

    ObjectStateRegistry.clear()
    yield
    ObjectStateRegistry.clear()


def _synthetic_dataset(tmp_path: Path) -> tuple[Path, str]:
    root = tmp_path / "plate"
    SyntheticMicroscopyGenerator(
        output_dir=str(root),
        grid_size=(1, 1),
        tile_size=(32, 32),
        wavelengths=1,
        z_stack_levels=1,
        num_cells=2,
        wells=["A01"],
        format="ImageXpress",
        random_seed=7,
    ).generate_dataset()
    source = PipelineDocumentCodec.render(
        PipelineDocumentCodec.from_values(
            pipeline_config=PipelineConfig(),
            pipeline_steps=[
                FunctionStep(name="Blur", func=(gaussian_blur, {"sigma": 1.0}))
            ],
        )
    )
    return root, source


def _port(offset: int) -> int:
    return 24000 + offset + os.getpid() % 10000


def _call(server, name: str, arguments: dict):
    """One MCP tool call; return its structured payload."""

    content, structured = asyncio.run(server.call_tool(name, arguments))
    del content
    return structured


def test_headless_mcp_journey_adds_compiles_and_runs_a_dataset(tmp_path: Path) -> None:
    from openhcs.mcp import server as mcp_server
    from openhcs.mcp.context import OpenHCSAgentContext

    root, source = _synthetic_dataset(tmp_path)
    context = OpenHCSAgentContext(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=(tmp_path,)
        ),
        session_transport_config=OpenHCSZMQConfig(
            default_port=_port(0), persistent=False
        ),
    )
    built = mcp_server.build_server(context)
    context.bind_main_thread(CallerThread())
    try:
        added = _call(built, "openhcs_add_datasets", {"roots": [str(root)]})
        assert added["status"] == "completed", added
        (scope_id,) = added["target_scope_ids"]
        piped = _call(
            built,
            "openhcs_set_dataset_pipeline",
            {"scope_id": scope_id, "pipeline_source": source},
        )
        assert piped["status"] == "completed", piped

        for tool, finished in (
            ("openhcs_initialize_datasets", lambda row: row["initialized"]),
            ("openhcs_compile_datasets", lambda row: row["compiled"]),
            (
                "openhcs_run_datasets",
                lambda row: row["terminal_status"] is not None
                and not row["execution_active"],
            ),
        ):
            started = _call(built, tool, {"scope_ids": [scope_id]})
            assert started["status"] == "accepted", started
            sequence = started["event_sequence"]
            deadline = time.monotonic() + STAGE_TIMEOUT_SECONDS
            while True:
                (row,) = _call(built, "openhcs_session_datasets", {})["rows"]
                if finished(row):
                    break
                assert time.monotonic() < deadline, (tool, row)
                events = _call(
                    built,
                    "openhcs_session_events",
                    {"after_sequence": sequence, "timeout_seconds": 5.0},
                )
                sequence = events["last_sequence"]

        assert row["terminal_status"] == "complete", row
        output_root = Path(row["output_root"])
        assert any(path.is_file() for path in output_root.rglob("*")), output_root
        kinds = {
            event["kind"]
            for event in _call(
                built,
                "openhcs_session_events",
                {"after_sequence": 0, "timeout_seconds": 0.0},
            )["events"]
        }
        assert {"DatasetsChanged", "CompiledStateChanged", "DatasetExecutionFinished"} <= kinds
    finally:
        context.session.close()


def test_gui_journey_runs_the_same_operations_through_the_widgets(
    tmp_path: Path,
) -> None:
    pytest.importorskip("PyQt6")
    from PyQt6.QtWidgets import QApplication
    from pyqt_reactive.services.ui_thread_dispatch import UiThreadDispatcher

    from openhcs.authoring.session.session import DispatcherThread, Session
    from openhcs.core.config import GlobalPipelineConfig
    from openhcs.pyqt_gui.config import get_default_ui_config
    from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
    from tests.unit.pyqt_gui.session_harness import GuiServiceStub

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
            (InitializeDatasets, lambda row: row.initialized),
            (CompileDatasets, lambda row: row.compiled),
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
        session.close()
        dispatcher.close()
