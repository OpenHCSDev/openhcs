import asyncio
from pathlib import Path

import pytest
from objectstate import ObjectState, ObjectStateRegistry
from objectstate.lazy_factory import ensure_global_config_context

from openhcs.core.artifact_inspection import CompiledArtifactInspection
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.execution_state import ManagerExecutionState, TerminalExecutionStatus
from openhcs.core.orchestrator.orchestrator import (
    OrchestratorState,
    PipelineOrchestrator,
)
from openhcs.core.progress.projection import ExecutionRuntimeProjection
from openhcs.pyqt_gui.services.plate_manager_row import PlateManagerRow
from openhcs.pyqt_gui.services.plate_manager_state_projection import (
    PlateRowActivityProjection,
)
from openhcs.pyqt_gui.widgets.shared.services.compile_batch_workflow_service import (
    CompileBatchWorkflowService,
)
from tests.unit.pyqt_gui.test_batch_workflow_compile_engine import (
    ClientServiceHarness,
    CompilePlateRowHostHarness,
    RecordingPlateRequestBuilder,
    _context,
)


class TerminalCompileHost(CompilePlateRowHostHarness):
    runtime_progress_projection = ExecutionRuntimeProjection()

    def debug_session_for_plate(self, plate_path):
        return None

    def debug_terminal_summary_for_plate(self, plate_path):
        return None


@pytest.mark.parametrize(
    "terminal", (TerminalExecutionStatus.COMPLETE, TerminalExecutionStatus.FAILED)
)
@pytest.mark.parametrize("compile_fails", (False, True))
def test_recompile_supersedes_row_activity_without_erasing_batch_outcome(
    terminal, compile_fails
):
    ObjectStateRegistry.clear()
    ensure_global_config_context(GlobalPipelineConfig, GlobalPipelineConfig())
    host = TerminalCompileHost()
    host.execution_state = ManagerExecutionState.RUNNING
    batch = host.plate_terminal_activity_status
    batch.begin_batch(("/A", "/B"))
    batch.record_execution("/A", "active-A")
    batch.record_execution("/B", "finished-B")
    batch.mark_terminal("/B", terminal)
    outcome_before = batch.terminal_items()
    orchestrator = PipelineOrchestrator(plate_path=Path("/B"))
    orchestrator._state = terminal.orchestrator_state
    ObjectStateRegistry.register(ObjectState(orchestrator, scope_id="/B"))
    row = PlateManagerRow.from_scope("/B")
    activity = PlateRowActivityProjection(host, row)

    async def connect():
        assert batch.terminal_status("/B") is None
        assert batch.execution_id("/B") is None
        assert batch.terminal_items() == outcome_before
        assert batch.active_plates == ("/A",)
        assert activity.status_prefix == "⏳ Compile"
        return object()

    class ControlledCompile:
        async def submit_compile_job(self, **kwargs):
            return "new-compile-B"

        async def wait_compile_job(self, **kwargs):
            if compile_fails:
                raise RuntimeError("controlled recompile failure")
            return CompiledArtifactInspection(
                compile_artifact_id="new-compile-B", plate_id="/B", steps=()
            )

    service = CompileBatchWorkflowService(
        host=host,
        context=_context(ClientServiceHarness(), connect_progress_client=connect),
        plate_request_builder=RecordingPlateRequestBuilder(),
        compile_workflow=ControlledCompile(),
    )
    try:
        asyncio.run(service.compile_plates([row]))
        expected = (
            OrchestratorState.COMPILE_FAILED
            if compile_fails
            else OrchestratorState.COMPILED
        )
        assert orchestrator.state is expected
        assert activity.orchestrator_state is expected
        assert activity.status_prefix == expected.status_prefix
        assert batch.terminal_items() == outcome_before
        assert batch.execution_id("/A") == "active-A"
        assert batch.active_plates == ("/A",)
        batch.mark_terminal("/A", TerminalExecutionStatus.COMPLETE)
        assert batch.terminal_counts() == (
            (2, 0) if terminal is TerminalExecutionStatus.COMPLETE else (1, 1)
        )
    finally:
        ObjectStateRegistry.clear()


def test_active_batch_member_cannot_be_superseded():
    batch = TerminalCompileHost().plate_terminal_activity_status
    batch.begin_batch(("/A",))
    batch.record_execution("/A", "active-A")
    with pytest.raises(RuntimeError, match="active execution"):
        batch.supersede_terminal("/A")
    assert batch.execution_id("/A") == "active-A"
    assert batch.active_plates == ("/A",)
