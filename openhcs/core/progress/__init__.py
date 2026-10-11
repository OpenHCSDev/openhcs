"""Progress events: declaration, emission and the per-process registry.

A runtime emits through the execution it reports on::

    ProgressExecutionContext(execution_id="exec-1", subject_id="/data/set").emit(
        axis_id="A01",
        step_name="compilation",
        phase=ProgressPhase.COMPILE,
        status=ProgressStatus.RUNNING,
        percent=50.0,
        completed=1,
        total=2,
    )

and a viewer listens on the registry::

    registry().add_listener(lambda execution_id, event: ...)
"""

from .exceptions import ProgressError
from .registry import registry
from .types import (
    ProgressChannel,
    ProgressChannelDeclarationBase,
    ProgressChannelRole,
    ProgressEvent,
    ProgressExecutionContext,
    ProgressIdentity,
    ProgressPhase,
    ProgressPhaseDeclarationBase,
    ProgressQueue,
    ProgressStatus,
    ProgressStatusDeclarationBase,
    emit_event,
    is_execution_phase,
    is_failure_event,
    is_success_terminal_event,
    is_terminal_event,
    phase_channel,
    progress_channel_role,
    set_progress_queue,
)

__all__ = [
    "ProgressChannel",
    "ProgressChannelDeclarationBase",
    "ProgressChannelRole",
    "ProgressError",
    "ProgressEvent",
    "ProgressExecutionContext",
    "ProgressIdentity",
    "ProgressPhase",
    "ProgressPhaseDeclarationBase",
    "ProgressQueue",
    "ProgressStatus",
    "ProgressStatusDeclarationBase",
    "emit_event",
    "is_execution_phase",
    "is_failure_event",
    "is_success_terminal_event",
    "is_terminal_event",
    "phase_channel",
    "progress_channel_role",
    "registry",
    "set_progress_queue",
]
