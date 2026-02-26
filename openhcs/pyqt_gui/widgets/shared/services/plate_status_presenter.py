"""Plate list status presenter for Plate Manager rows."""

from __future__ import annotations

from typing import Optional

from openhcs.core.orchestrator.orchestrator import OrchestratorState
from openhcs.core.progress.projection import PlateRuntimeProjection, PlateRuntimeState
from openhcs.pyqt_gui.widgets.shared.services.execution_state import (
    TerminalExecutionStatus,
)


class PlateStatusPresenter:
    """Render deterministic plate status text from execution + orchestrator signals."""

    TERMINAL_LABELS = {
        TerminalExecutionStatus.CANCELLED: "✗ Cancelled",
        TerminalExecutionStatus.FAILED: "❌ Exec Failed",
        TerminalExecutionStatus.COMPLETE: "✅ Complete",
    }
    ORCHESTRATOR_LABELS = {
        OrchestratorState.READY: "✓ Init",
        OrchestratorState.COMPILED: "✓ Compiled",
        OrchestratorState.COMPLETED: "✅ Complete",
        OrchestratorState.INIT_FAILED: "❌ Init Failed",
        OrchestratorState.COMPILE_FAILED: "❌ Compile Failed",
        OrchestratorState.EXEC_FAILED: "❌ Exec Failed",
        OrchestratorState.EXECUTING: "🔄 Executing",
    }
    RUNTIME_STATE_LABELS = {
        PlateRuntimeState.COMPILING: "⏳ Compiling",
        PlateRuntimeState.COMPILED: "✅ Compiled",
        PlateRuntimeState.FAILED: "❌ Failed",
        PlateRuntimeState.COMPLETE: "✅ Complete",
        PlateRuntimeState.EXECUTING: "⚙️ Executing",
    }

    @classmethod
    def build_status_prefix(
        cls,
        *,
        orchestrator_state: Optional[OrchestratorState],
        is_init_pending: bool,
        is_compile_pending: bool,
        is_execution_active: bool,
        terminal_status: Optional[TerminalExecutionStatus],
        queue_position: Optional[int],
        runtime_projection: Optional[PlateRuntimeProjection],
    ) -> str:
        # Runtime projection is canonical whenever present.
        if runtime_projection is not None:
            return cls._format_runtime_plate_status(runtime_projection)

        if queue_position is not None:
            return f"⏳ Queued 0.0% (q#{queue_position})"

        if is_execution_active:
            return "⏳ Pending"

        if is_init_pending:
            return "⏳ Init"
        if is_compile_pending:
            return "⏳ Compile"

        if terminal_status is not None:
            terminal_label = cls.TERMINAL_LABELS.get(terminal_status)
            if terminal_label is not None:
                return terminal_label

        if orchestrator_state is None:
            return ""
        return cls.ORCHESTRATOR_LABELS.get(orchestrator_state, "")

    @staticmethod
    def _format_runtime_plate_status(plate: PlateRuntimeProjection) -> str:
        label = PlateStatusPresenter.RUNTIME_STATE_LABELS.get(plate.state)
        if label is None:
            return ""
        return f"{label} {plate.percent:.1f}%"
