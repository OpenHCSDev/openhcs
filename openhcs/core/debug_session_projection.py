"""Core debugger session projection semantics."""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import ClassVar

from metaclass_registry import AutoRegisterMeta

from openhcs.core.debug import DebugSession, DebugSnapshot, DebugTerminalSummary
from openhcs.core.execution_state import (
    ManagerExecutionState,
    TerminalExecutionStatus,
    parse_terminal_status,
)


@dataclass(frozen=True, slots=True)
class DebugSessionTargetState:
    """Current plate/pipeline target state required by debug controls."""

    current_plate_scope_id: str
    pipeline_scope_id: str
    initialized: bool
    compiled: bool
    terminal_status: str | None = None


@dataclass(frozen=True, slots=True)
class DebugPauseBoundaryState:
    """Debug-pause markers visible to action projection and command dispatch."""

    pause_step_indices: tuple[int, ...] = ()

    @property
    def has_pause_boundaries(self) -> bool:
        return bool(self.pause_step_indices)


@dataclass(frozen=True, slots=True)
class DebugSessionProjectionContext:
    """Complete target/session state needed to project debugger availability."""

    target: DebugSessionTargetState | None
    session: DebugSession | None
    manager_execution_state: ManagerExecutionState
    terminal_summary: DebugTerminalSummary | None = None
    pause_boundaries: DebugPauseBoundaryState = DebugPauseBoundaryState()
    snapshots: tuple[DebugSnapshot, ...] = ()

    @property
    def terminal_summary_matches_session(self) -> bool:
        if self.session is None or self.terminal_summary is None:
            return False
        return self.session.debug_session_id == self.terminal_summary.debug_session_id

    @property
    def active_session(self) -> DebugSession | None:
        if self.terminal_summary_matches_session:
            return None
        return self.session

    def snapshot_for_id(self, snapshot_id: str | None) -> DebugSnapshot | None:
        if snapshot_id is None:
            return None
        for snapshot in self.snapshots:
            if snapshot.snapshot_id == snapshot_id:
                return snapshot
        return None

    @property
    def phase(self) -> type[DebugSessionPhase]:
        return DebugSessionPhase.for_context(self)


class DebugSessionPhase(ABC, metaclass=AutoRegisterMeta):
    """One debugger session phase; ``name`` is its spelling for UI and MCP."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["DebugSessionPhase"]]] = {}

    name: ClassVar[str | None] = None
    priority: ClassVar[int]
    title: ClassVar[str]
    detail: ClassVar[str]
    status_prefix: ClassVar[str] = ""
    is_terminal: ClassVar[bool] = False

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        raise NotImplementedError

    @classmethod
    def for_context(
        cls,
        context: DebugSessionProjectionContext,
    ) -> type["DebugSessionPhase"]:
        for declaration in sorted(
            cls.__registry__.values(),
            key=lambda candidate: candidate.priority,
        ):
            if declaration.matches(context):
                return declaration
        raise ValueError("No debugger session phase matched the projection context.")


class NoPlateDebugSessionPhase(DebugSessionPhase):
    name = "no_plate"
    priority = 0
    title = "No Plate"
    detail = "Select a plate to debug."

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        return context.target is None


class NeedsInitializationDebugSessionPhase(DebugSessionPhase):
    name = "needs_initialization"
    priority = 10
    title = "Needs Init"
    detail = "Initialize the selected plate before debugging."

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        return context.target is not None and not context.target.initialized


class NeedsCompileDebugSessionPhase(DebugSessionPhase):
    name = "needs_compile"
    priority = 20
    title = "Needs Compile"
    detail = "Compile the selected plate before debugging."

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        return (
            context.target is not None
            and context.target.initialized
            and not context.target.compiled
        )


class PendingExecutionDebugSessionPhase(DebugSessionPhase):
    name = "pending_execution"
    priority = 30
    title = "Debug Starting"
    detail = "Debug execution is queued or starting."
    status_prefix = "Debug starting"

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        return (
            context.target is not None
            and context.target.initialized
            and context.target.compiled
            and context.active_session is None
            and context.manager_execution_state.busy
        )


class ActiveDebugSessionPhase(DebugSessionPhase):
    name = "active_session"
    priority = 40
    title = "Debug Active"
    detail = "Debug session has an active cursor or paused worker."
    status_prefix = "Debug paused"

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        return (
            context.target is not None
            and context.target.initialized
            and context.target.compiled
            and context.active_session is not None
        )


class TerminalDebugSessionPhase(DebugSessionPhase):
    """Shared terminal debugger phase matching a terminal execution status."""

    terminal_status: ClassVar[TerminalExecutionStatus | None] = None
    is_terminal = True

    @classmethod
    def require_terminal_status(cls) -> TerminalExecutionStatus:
        if cls.terminal_status is None:
            raise TypeError(f"{cls.__name__} does not declare a terminal status.")
        return cls.terminal_status

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        if (
            context.target is None
            or not context.target.initialized
            or not context.target.compiled
            or context.active_session is not None
            or context.terminal_summary is None
        ):
            return False
        return (
            parse_terminal_status(context.terminal_summary.terminal_status)
            is cls.require_terminal_status()
        )


class TerminalCompleteDebugSessionPhase(TerminalDebugSessionPhase):
    name = "terminal_complete"
    priority = 50
    title = "Debug Complete"
    detail = "Last debug command completed."
    status_prefix = "Debug complete"
    terminal_status = TerminalExecutionStatus.COMPLETE


class TerminalFailedDebugSessionPhase(TerminalDebugSessionPhase):
    name = "terminal_failed"
    priority = 51
    title = "Debug Failed"
    detail = "Last debug command failed."
    status_prefix = "Debug failed"
    terminal_status = TerminalExecutionStatus.FAILED


class TerminalCancelledDebugSessionPhase(TerminalDebugSessionPhase):
    name = "terminal_cancelled"
    priority = 52
    title = "Debug Cancelled"
    detail = "Last debug command was cancelled."
    status_prefix = "Debug cancelled"
    terminal_status = TerminalExecutionStatus.CANCELLED


class ReadyDebugSessionPhase(DebugSessionPhase):
    name = "ready"
    priority = 100
    title = "Ready"
    detail = "Debug controls are ready."

    @classmethod
    def matches(cls, context: DebugSessionProjectionContext) -> bool:
        return (
            context.target is not None
            and context.target.initialized
            and context.target.compiled
            and context.active_session is None
            and context.terminal_summary is None
            and not context.manager_execution_state.busy
        )
