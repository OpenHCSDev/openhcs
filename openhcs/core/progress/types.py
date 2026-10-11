"""Immutable progress types following OpenHCS patterns."""

import multiprocessing.queues
import queue
import os
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, fields
from dataclasses import replace as dataclass_replace
from collections.abc import Mapping
from typing import Any, ClassVar, Self

from metaclass_registry import AutoRegisterMeta
from python_introspect import dataclass_from_mapping, project_dataclass, to_jsonable
from zmqruntime.messages import TaskProgress

from .exceptions import ProgressError

# =============================================================================
# Progress vocabulary: channels, phases and statuses are class families
# =============================================================================


class ProgressChannel(ABC, metaclass=AutoRegisterMeta):
    """A semantic progress stream; each channel is a subclass.

    ``name`` is the channel's spelling at the wire and UI boundary.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["ProgressChannel"]]] = {}

    name: ClassVar[str | None] = None


class ExecutionProgressChannel(ProgressChannel):
    """A channel carrying the execution tree (as opposed to setup and compile)."""


class InitProgressChannel(ProgressChannel):
    name = "init"


class CompileProgressChannel(ProgressChannel):
    name = "compile"


class PipelineProgressChannel(ExecutionProgressChannel):
    name = "pipeline"


class StepProgressChannel(ExecutionProgressChannel):
    name = "step"


class TerminalProgressEvent:
    """Trait for phases and statuses that close an event lifecycle."""

    is_terminal: ClassVar[bool] = True


class FailureProgressEvent(TerminalProgressEvent):
    """Trait for terminal phases and statuses that represent failure."""

    is_failure: ClassVar[bool] = True


class SuccessTerminalProgressEvent(TerminalProgressEvent):
    """Trait for phases and statuses that represent successful completion."""

    is_success_terminal: ClassVar[bool] = True


class ProgressStatus(ABC, metaclass=AutoRegisterMeta):
    """How the work an event reports on stands; each status is a subclass."""

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["ProgressStatus"]]] = {}

    name: ClassVar[str | None] = None
    is_terminal: ClassVar[bool] = False
    is_failure: ClassVar[bool] = False
    is_success_terminal: ClassVar[bool] = False


class PendingProgressStatus(ProgressStatus):
    name = "pending"


class StartedProgressStatus(ProgressStatus):
    name = "started"


class RunningProgressStatus(ProgressStatus):
    name = "running"


class SuccessProgressStatus(SuccessTerminalProgressEvent, ProgressStatus):
    name = "success"


class FailedProgressStatus(FailureProgressEvent, ProgressStatus):
    name = "failed"


class CancelledProgressStatus(FailureProgressEvent, ProgressStatus):
    name = "cancelled"


class ErrorProgressStatus(FailureProgressEvent, ProgressStatus):
    name = "error"


class QueuedProgressStatus(ProgressStatus):
    name = "queued"


class ProgressPhase(ABC, metaclass=AutoRegisterMeta):
    """Which lifecycle point an event reports; each phase is a subclass.

    A phase owns the channel it is carried on and whether it ends the
    lifecycle; ``name`` is its wire spelling.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["ProgressPhase"]]] = {}

    name: ClassVar[str | None] = None
    channel: ClassVar[type[ProgressChannel]]
    is_terminal: ClassVar[bool] = False
    is_failure: ClassVar[bool] = False
    is_success_terminal: ClassVar[bool] = False

    @classmethod
    def is_execution(cls) -> bool:
        """Whether this phase belongs to the execution tree."""
        return issubclass(cls.channel, ExecutionProgressChannel)

    @classmethod
    def ends_successfully_with(cls, status: type[ProgressStatus]) -> bool:
        """Whether an event in this phase with ``status`` completed successfully."""
        del status
        return cls.is_success_terminal


class StatusTerminatedProgressPhase:
    """Trait for phases whose terminal outcome is carried by the event status."""

    @classmethod
    def ends_successfully_with(cls, status: type[ProgressStatus]) -> bool:
        return status.is_success_terminal


class InitChannelProgressPhase:
    channel: ClassVar[type[ProgressChannel]] = InitProgressChannel


class CompileChannelProgressPhase:
    channel: ClassVar[type[ProgressChannel]] = CompileProgressChannel


class PipelineChannelProgressPhase:
    channel: ClassVar[type[ProgressChannel]] = PipelineProgressChannel


class StepChannelProgressPhase:
    channel: ClassVar[type[ProgressChannel]] = StepProgressChannel


class InitProgressPhase(InitChannelProgressPhase, ProgressPhase):
    name = "init"


class QueuedProgressPhase(PipelineChannelProgressPhase, ProgressPhase):
    name = "queued"


class RunningProgressPhase(PipelineChannelProgressPhase, ProgressPhase):
    name = "running"


class SuccessProgressPhase(
    SuccessTerminalProgressEvent, PipelineChannelProgressPhase, ProgressPhase
):
    name = "success"


class FailedProgressPhase(FailureProgressEvent, PipelineChannelProgressPhase, ProgressPhase):
    name = "failed"


class CancelledProgressPhase(
    FailureProgressEvent, PipelineChannelProgressPhase, ProgressPhase
):
    name = "cancelled"


class CompileProgressPhase(
    StatusTerminatedProgressPhase, CompileChannelProgressPhase, ProgressPhase
):
    name = "compile"


class AxisStartedProgressPhase(PipelineChannelProgressPhase, ProgressPhase):
    name = "axis_started"


class StepStartedProgressPhase(PipelineChannelProgressPhase, ProgressPhase):
    name = "step_started"


class StepCompletedProgressPhase(PipelineChannelProgressPhase, ProgressPhase):
    name = "step_completed"


class PatternGroupProgressPhase(StepChannelProgressPhase, ProgressPhase):
    name = "pattern_group"


class AxisCompletedProgressPhase(
    SuccessTerminalProgressEvent, PipelineChannelProgressPhase, ProgressPhase
):
    name = "axis_completed"


class ViewerSettlementProgressPhase(PipelineChannelProgressPhase, ProgressPhase):
    """Parent-observed progress while streamed viewer state is materialized."""

    name = "viewer_settlement"


class AxisErrorProgressPhase(
    FailureProgressEvent, PipelineChannelProgressPhase, ProgressPhase
):
    name = "axis_error"


# =============================================================================
# ProgressEvent: one declaration, encoded and decoded by its fields
# =============================================================================


@dataclass(frozen=True)
class ProgressIdentity:
    """The fields that identify which work one progress event reports on."""

    execution_id: str
    subject_id: str
    axis_id: str
    step_name: str


@dataclass(frozen=True, kw_only=True)
class ProgressEvent(TaskProgress):
    """One progress event.

    Extends zmqruntime's generic ``TaskProgress``: the wire mapping is exactly
    the declared fields, so encoding and decoding read this declaration.
    """

    phase: type[ProgressPhase]
    status: type[ProgressStatus]
    subject_id: str
    axis_id: str
    step_name: str
    pid: int
    partition_values: list[str] | None = None
    worker_assignments: dict[str, list[str]] | None = None
    worker_slot: str | None = None
    owned_partition_values: list[str] | None = None
    message: str | None = None
    component: str | None = None
    pattern: str | None = None
    context: dict[str, Any] | None = None
    step_names: list[str] | None = None

    @property
    def identity(self) -> ProgressIdentity:
        return project_dataclass(ProgressIdentity, self)

    def with_worker_topology(
        self,
        *,
        worker_assignments: dict[str, list[str]],
        partition_values: list[str],
    ) -> "ProgressEvent":
        """Return this event with execution topology attached."""
        return dataclass_replace(
            self,
            worker_assignments=worker_assignments,
            partition_values=partition_values,
        )

    @property
    def channel(self) -> type[ProgressChannel]:
        return self.phase.channel

    def is_failure(self) -> bool:
        """Whether the phase or the status reports a failure."""
        return self.phase.is_failure or self.status.is_failure

    def is_success_terminal(self) -> bool:
        """Whether the event reports successful completion."""
        return self.phase.ends_successfully_with(self.status)

    def is_complete(self) -> bool:
        """Whether the event closes its lifecycle, by failure or success."""
        return self.is_failure() or self.is_success_terminal()


class ProgressContextPayload(ABC, metaclass=AutoRegisterMeta):
    """One typed entry of ``ProgressEvent.context``, stored under its key.

    Members are dataclasses: the wire body is the declared fields, encoded by
    ``to_jsonable`` and decoded by ``dataclass_from_mapping``.
    """

    __registry_key__ = "context_key"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["ProgressContextPayload"]]] = {}

    context_key: ClassVar[str | None] = None
    malformed_error: ClassVar[type[ValueError]] = ValueError

    def to_context(self) -> dict[str, Any]:
        return self.context_of(self)

    @classmethod
    def from_context(cls, context: Mapping[str, Any] | None) -> Self | None:
        """This payload out of an event context, if the context carries one."""

        if not context or cls.context_key not in context:
            return None
        body = context[cls.context_key]
        if not isinstance(body, Mapping):
            raise cls.malformed_error(f"{cls.context_key!r} must be a mapping.")
        try:
            return dataclass_from_mapping(cls, body)
        except (TypeError, ValueError) as error:
            raise cls.malformed_error(
                f"Malformed {cls.context_key!r} progress context: {error}"
            ) from error

    @staticmethod
    def context_of(*payloads: "ProgressContextPayload | None") -> dict[str, Any] | None:
        """The event context carrying these payloads."""

        context = {
            payload.context_key: to_jsonable(payload)
            for payload in payloads
            if payload is not None
        }
        return context or None


class ProgressQueue(ABC):
    """Where one process puts the progress events it emits."""

    @abstractmethod
    def put(self, event: ProgressEvent) -> None:
        """Enqueue one progress event."""

        raise NotImplementedError


# Thread and process queues carry events as they are.
for _queue_type in (
    queue.Queue,
    queue.SimpleQueue,
    multiprocessing.queues.Queue,
    multiprocessing.queues.SimpleQueue,
):
    ProgressQueue.register(_queue_type)

_progress_queue: ProgressQueue | None = None


def set_progress_queue(progress_queue: ProgressQueue | None) -> None:
    """Install the queue this process emits progress events into."""

    global _progress_queue
    _progress_queue = progress_queue


def emit_event(event: ProgressEvent) -> None:
    """Put one event on the installed progress queue."""

    if _progress_queue is None:
        raise ProgressError(
            "Progress emission requires a queue installed with set_progress_queue()."
        )
    _progress_queue.put(event)


@dataclass(frozen=True, slots=True)
class ProgressExecutionContext:
    """The execution a progress event belongs to; builds and emits its events."""

    execution_id: str
    subject_id: str

    def event_fields(self) -> dict[str, object]:
        """The event fields this context fixes for every event it emits."""

        return {
            declared.name: getattr(self, declared.name)
            for declared in fields(ProgressExecutionContext)
        }

    def event(self, **event_fields: Any) -> ProgressEvent:
        return ProgressEvent(
            **self.event_fields(),
            timestamp=time.time(),
            pid=os.getpid(),
            **event_fields,
        )

    def emit(self, **event_fields: Any) -> None:
        emit_event(self.event(**event_fields))
