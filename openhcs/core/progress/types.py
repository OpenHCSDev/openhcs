"""Immutable progress types following OpenHCS patterns."""

import multiprocessing.queues
import queue
import os
import time
from abc import ABC, abstractmethod
from dataclasses import dataclass, fields
from dataclasses import replace as dataclass_replace
from enum import Enum
from typing import Any, ClassVar

from metaclass_registry import AutoRegisterMeta
from python_introspect import project_dataclass
from zmqruntime.messages import TaskProgress

from .exceptions import ProgressError

# =============================================================================
# ProgressPhase Enum - Unifies TaskPhase + AxisPhase
# =============================================================================


class ProgressPhase(Enum):
    """Progress phases - unified phase vocabulary.

    Extends ZMQRuntime's TaskPhase with OpenHCS-specific phases.
    """

    # Generic phases (from TaskPhase)
    INIT = "init"
    QUEUED = "queued"
    RUNNING = "running"
    SUCCESS = "success"
    FAILED = "failed"
    CANCELLED = "cancelled"

    # Compilation phases
    COMPILE = "compile"

    # Execution phases
    AXIS_STARTED = "axis_started"
    STEP_STARTED = "step_started"
    STEP_COMPLETED = "step_completed"
    PATTERN_GROUP = "pattern_group"
    AXIS_COMPLETED = "axis_completed"
    VIEWER_SETTLEMENT = "viewer_settlement"

    # Error phases
    AXIS_ERROR = "axis_error"

    def __str__(self):
        """String representation for logging."""
        return self.value


class ProgressChannelRole(Enum):
    """Nominal role for semantic progress channels."""

    CONTROL = "control"
    EXECUTION = "execution"


class ProgressChannel(Enum):
    """Semantic channel for phase-specific progress streams."""

    INIT = "init"
    COMPILE = "compile"
    PIPELINE = "pipeline"
    STEP = "step"

    def __str__(self):
        return self.value


# =============================================================================
# ProgressStatus Enum - Unifies TaskStatus + AxisStatus
# =============================================================================


class ProgressStatus(Enum):
    """Progress status - unified status vocabulary.

    Extends ZMQRuntime's TaskStatus with OpenHCS-specific statuses.
    """

    # Generic statuses (from TaskStatus)
    PENDING = "pending"
    STARTED = "started"
    RUNNING = "running"
    SUCCESS = "success"
    FAILED = "failed"
    CANCELLED = "cancelled"

    # OpenHCS-specific statuses
    ERROR = "error"
    QUEUED = "queued"

    def __str__(self):
        """String representation for logging."""
        return self.value


class ProgressChannelDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """Nominal semantic declaration for one progress channel."""

    __registry_key__ = "progress_channel"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[ProgressChannel, type["ProgressChannelDeclarationBase"]]
    ] = {}

    progress_channel: ClassVar[ProgressChannel | None] = None
    role: ClassVar[ProgressChannelRole]

    @classmethod
    def require_channel(cls) -> ProgressChannel:
        if cls.progress_channel is None:
            raise TypeError(f"{cls.__name__} does not declare a progress channel.")
        return cls.progress_channel

    @classmethod
    def for_channel(
        cls,
        channel: ProgressChannel,
    ) -> type["ProgressChannelDeclarationBase"]:
        return cls.__registry__[channel]


class ControlProgressChannel:
    """Trait for progress channels that control setup/compile lifecycle."""

    role: ClassVar[ProgressChannelRole] = ProgressChannelRole.CONTROL


class ExecutionProgressChannel:
    """Trait for progress channels that represent execution lifecycle."""

    role: ClassVar[ProgressChannelRole] = ProgressChannelRole.EXECUTION


class InitProgressChannel(ControlProgressChannel, ProgressChannelDeclarationBase):
    progress_channel = ProgressChannel.INIT


class CompileProgressChannel(ControlProgressChannel, ProgressChannelDeclarationBase):
    progress_channel = ProgressChannel.COMPILE


class PipelineProgressChannel(ExecutionProgressChannel, ProgressChannelDeclarationBase):
    progress_channel = ProgressChannel.PIPELINE


class StepProgressChannel(ExecutionProgressChannel, ProgressChannelDeclarationBase):
    progress_channel = ProgressChannel.STEP


class ProgressPhaseDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """Nominal semantic declaration for one progress phase."""

    __registry_key__ = "phase"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[ProgressPhase, type["ProgressPhaseDeclarationBase"]]
    ] = {}

    phase: ClassVar[ProgressPhase | None] = None
    progress_channel: ClassVar[type[ProgressChannelDeclarationBase]]
    is_terminal: ClassVar[bool] = False
    is_failure: ClassVar[bool] = False
    is_success_terminal: ClassVar[bool] = False

    @classmethod
    def require_phase(cls) -> ProgressPhase:
        if cls.phase is None:
            raise TypeError(f"{cls.__name__} does not declare a progress phase.")
        return cls.phase

    @classmethod
    def for_phase(
        cls,
        phase: ProgressPhase,
    ) -> type["ProgressPhaseDeclarationBase"]:
        return cls.__registry__[phase]

    @classmethod
    def is_success_terminal_for_status(
        cls,
        status_declaration: type["ProgressStatusDeclarationBase"],
    ) -> bool:
        return cls.is_success_terminal


class TerminalProgressEvent:
    """Trait for progress declarations that close an event lifecycle."""

    is_terminal: ClassVar[bool] = True


class FailureProgressEvent(TerminalProgressEvent):
    """Trait for terminal progress declarations that represent failure."""

    is_failure: ClassVar[bool] = True


class SuccessTerminalProgressEvent(TerminalProgressEvent):
    """Trait for progress declarations that represent successful completion."""

    is_success_terminal: ClassVar[bool] = True


class StatusTerminatedProgressPhase:
    """Trait for phases whose terminal outcome is carried by event status."""

    @classmethod
    def is_success_terminal_for_status(
        cls,
        status_declaration: type["ProgressStatusDeclarationBase"],
    ) -> bool:
        return status_declaration.is_success_terminal


class InitChannelProgressPhase:
    """Trait for progress phases carried on the init channel."""

    progress_channel: ClassVar[type[ProgressChannelDeclarationBase]] = InitProgressChannel


class CompileChannelProgressPhase:
    """Trait for progress phases carried on the compile channel."""

    progress_channel: ClassVar[type[ProgressChannelDeclarationBase]] = CompileProgressChannel


class PipelineChannelProgressPhase:
    """Trait for progress phases carried on the pipeline execution channel."""

    progress_channel: ClassVar[type[ProgressChannelDeclarationBase]] = PipelineProgressChannel


class StepChannelProgressPhase:
    """Trait for progress phases carried on the step execution channel."""

    progress_channel: ClassVar[type[ProgressChannelDeclarationBase]] = StepProgressChannel


class InitProgressPhase(InitChannelProgressPhase, ProgressPhaseDeclarationBase):
    phase = ProgressPhase.INIT


class QueuedProgressPhase(PipelineChannelProgressPhase, ProgressPhaseDeclarationBase):
    phase = ProgressPhase.QUEUED


class RunningProgressPhase(PipelineChannelProgressPhase, ProgressPhaseDeclarationBase):
    phase = ProgressPhase.RUNNING


class SuccessProgressPhase(
    SuccessTerminalProgressEvent,
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.SUCCESS


class FailedProgressPhase(
    FailureProgressEvent,
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.FAILED


class CancelledProgressPhase(
    FailureProgressEvent,
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.CANCELLED


class CompileProgressPhase(
    StatusTerminatedProgressPhase,
    CompileChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.COMPILE


class AxisStartedProgressPhase(
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.AXIS_STARTED


class StepStartedProgressPhase(
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.STEP_STARTED


class StepCompletedProgressPhase(
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.STEP_COMPLETED


class PatternGroupProgressPhase(StepChannelProgressPhase, ProgressPhaseDeclarationBase):
    phase = ProgressPhase.PATTERN_GROUP


class AxisCompletedProgressPhase(
    SuccessTerminalProgressEvent,
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.AXIS_COMPLETED


class ViewerSettlementProgressPhase(
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    """Parent-observed progress while streamed viewer state is materialized."""

    phase = ProgressPhase.VIEWER_SETTLEMENT


class AxisErrorProgressPhase(
    FailureProgressEvent,
    PipelineChannelProgressPhase,
    ProgressPhaseDeclarationBase,
):
    phase = ProgressPhase.AXIS_ERROR


class ProgressStatusDeclarationBase(ABC, metaclass=AutoRegisterMeta):
    """Nominal semantic declaration for one progress status."""

    __registry_key__ = "status"
    __skip_if_no_key__ = True
    __registry__: ClassVar[
        dict[ProgressStatus, type["ProgressStatusDeclarationBase"]]
    ] = {}

    status: ClassVar[ProgressStatus | None] = None
    is_terminal: ClassVar[bool] = False
    is_failure: ClassVar[bool] = False
    is_success_terminal: ClassVar[bool] = False

    @classmethod
    def require_status(cls) -> ProgressStatus:
        if cls.status is None:
            raise TypeError(f"{cls.__name__} does not declare a progress status.")
        return cls.status

    @classmethod
    def for_status(
        cls,
        status: ProgressStatus,
    ) -> type["ProgressStatusDeclarationBase"]:
        return cls.__registry__[status]


class PendingProgressStatus(ProgressStatusDeclarationBase):
    status = ProgressStatus.PENDING


class StartedProgressStatus(ProgressStatusDeclarationBase):
    status = ProgressStatus.STARTED


class RunningProgressStatus(ProgressStatusDeclarationBase):
    status = ProgressStatus.RUNNING


class SuccessProgressStatus(
    SuccessTerminalProgressEvent,
    ProgressStatusDeclarationBase,
):
    status = ProgressStatus.SUCCESS


class FailedProgressStatus(FailureProgressEvent, ProgressStatusDeclarationBase):
    status = ProgressStatus.FAILED


class CancelledProgressStatus(FailureProgressEvent, ProgressStatusDeclarationBase):
    status = ProgressStatus.CANCELLED


class ErrorProgressStatus(FailureProgressEvent, ProgressStatusDeclarationBase):
    status = ProgressStatus.ERROR


class QueuedProgressStatus(ProgressStatusDeclarationBase):
    status = ProgressStatus.QUEUED


def phase_channel(phase: ProgressPhase) -> ProgressChannel:
    """Classify phase to semantic channel."""
    return ProgressPhaseDeclarationBase.for_phase(phase).progress_channel.require_channel()


def progress_channel_role(channel: ProgressChannel) -> ProgressChannelRole:
    """Return the nominal role for a progress channel."""
    return ProgressChannelDeclarationBase.for_channel(channel).role


def is_terminal_event(event: "ProgressEvent") -> bool:
    """True when the event is terminal."""
    return is_failure_event(event) or is_success_terminal_event(event)


def is_execution_phase(phase: ProgressPhase) -> bool:
    """True when phase belongs to execution tree."""
    return progress_channel_role(phase_channel(phase)) is ProgressChannelRole.EXECUTION


def is_failure_event(event: "ProgressEvent") -> bool:
    """True when event represents a failure state."""
    return (
        ProgressPhaseDeclarationBase.for_phase(event.phase).is_failure
        or ProgressStatusDeclarationBase.for_status(event.status).is_failure
    )


def is_success_terminal_event(event: "ProgressEvent") -> bool:
    """True when event represents successful terminal completion."""
    return ProgressPhaseDeclarationBase.for_phase(
        event.phase
    ).is_success_terminal_for_status(
        ProgressStatusDeclarationBase.for_status(event.status)
    )


# =============================================================================
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

    phase: ProgressPhase
    status: ProgressStatus
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

    def is_complete(self) -> bool:
        """Whether the event is in a terminal phase or status."""
        return is_terminal_event(self)


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


def set_progress_queue(queue: ProgressQueue | None) -> None:
    """Install the queue this process emits progress events into."""

    global _progress_queue
    _progress_queue = queue


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
