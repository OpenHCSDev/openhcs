"""One dataset through the session, headless over MCP.

The journey adds a synthetic dataset, gives it a pipeline, initializes,
compiles and runs it on a real execution server, following the session's
events. tests/pyqt_gui/test_session_gui_journey.py runs the same
SessionOperation classes through the Qt widgets.
"""

from __future__ import annotations

import asyncio
import os
import time
from pathlib import Path

import pytest

from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    InitializeDatasets,
)
from openhcs.authoring.session.session import CallerThread, Session
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

    yield


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
            (
                "openhcs_initialize_datasets",
                lambda row: row["initialized"] and not row["init_pending"],
            ),
            (
                "openhcs_compile_datasets",
                lambda row: row["compiled"] and not row["compile_pending"],
            ),
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
        context.close()


def test_read_only_dataset_initializes_in_a_mirrored_workspace(tmp_path: Path) -> None:
    """Initialization never writes into a source it may not write."""


    from openhcs.core.config import GlobalPipelineConfig

    from tests.integration.test_measured_cli_session import (
        _set_writable,
        _source_state,
    )

    root, _source = _synthetic_dataset(tmp_path)
    _set_writable(root, False)
    before = _source_state(root)
    workspaces = tmp_path / "workspaces"
    session = Session(
        transport_config=OpenHCSZMQConfig(default_port=_port(2), persistent=False),
        global_config=GlobalPipelineConfig(),
        main_thread=CallerThread(),
        workspace_root=workspaces,
    )
    try:
        assert session.invoke(AddDatasets, AddDatasets.request(roots=(str(root),))).accepted
        (scope_id,) = session.dataset_scope_ids()
        started = session.invoke(
            InitializeDatasets, InitializeDatasets.request(scope_ids=(scope_id,))
        )
        assert started.accepted, started.errors
        deadline = time.monotonic() + STAGE_TIMEOUT_SECONDS
        while not session.is_initialized(scope_id) or scope_id in session.init_pending:
            failures = [
                record.event
                for record in session.events_after(0)
                if type(record.event).__name__ == "InitializationFailed"
            ]
            assert not failures, failures
            assert time.monotonic() < deadline
            time.sleep(0.05)
        assert session.orchestrator(scope_id).dataset_root.is_relative_to(workspaces)
        assert _source_state(root) == before
    finally:
        session.close()
        _set_writable(root, True)
