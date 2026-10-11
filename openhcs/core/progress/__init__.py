"""Progress events: declaration, emission and the per-process registry.

A runtime emits through the execution it reports on::

    ProgressExecutionContext(execution_id="exec-1", subject_id="/data/set").emit(
        axis_id="A01",
        step_name="compilation",
        phase=CompileProgressPhase,
        status=RunningProgressStatus,
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
    ProgressStream,
    ProgressContextPayload,
    ProgressEvent,
    ProgressExecutionContext,
    ProgressIdentity,
    ProgressPhase,
    ProgressQueue,
    ProgressStatus,
    emit_event,
    set_progress_queue,
)

__all__ = [
    "ProgressStream",
    "ProgressContextPayload",
    "ProgressError",
    "ProgressEvent",
    "ProgressExecutionContext",
    "ProgressIdentity",
    "ProgressPhase",
    "ProgressQueue",
    "ProgressStatus",
    "emit_event",
    "registry",
    "set_progress_queue",
]
