"""OpenHCS runtime projection built on generic zmqruntime projection primitives."""

from __future__ import annotations

from abc import ABC
from dataclasses import dataclass, field
from typing import ClassVar, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

from metaclass_registry import AutoRegisterMeta
from zmqruntime.messages import QueuedExecutionInfo, RunningExecutionInfo
from zmqruntime.progress import (
    GenericAxisProjection,
    GenericExecutionProjection,
    GenericSubjectProjection,
    ProgressProjectionAdapterABC,
    build_execution_projection,
)

from .types import (
    CompileProgressStream,
    PipelineProgressStream,
    ProgressStream,
    ProgressEvent,
    QueuedProgressPhase,
)


class SubjectRuntimeState(ABC, metaclass=AutoRegisterMeta):
    """Where one subject's execution stands; each state is a subclass.

    ``state_name`` is the state's spelling at the UI and wire boundary.
    """

    __registry_key__ = "state_name"
    __skip_if_no_key__ = True
    __registry__: ClassVar[dict[str, type["SubjectRuntimeState"]]] = {}

    state_name: ClassVar[str | None] = None
    is_terminal: ClassVar[bool] = False
    is_active: ClassVar[bool] = False
    default_stream: ClassVar[type[ProgressStream] | None] = None
    status_label: ClassVar[str] = ""
    count_label: ClassVar[str] = ""
    count_sort_order: ClassVar[int] = 0

    @classmethod
    def state_stream_from_events(
        cls,
        events: Iterable[ProgressEvent],
    ) -> type[ProgressStream] | None:
        del events
        return cls.default_stream

    @classmethod
    def percent_from_generic_projection(
        cls,
        *,
        generic_percent: float,
        axis_progress: Tuple["AxisRuntimeProjection", ...],
    ) -> float:
        del axis_progress
        return generic_percent

    @classmethod
    def status_label_for_subject(cls, subject: "SubjectRuntimeProjection") -> str:
        del subject
        return cls.status_label

    @classmethod
    def formatted_status_for_subject(cls, subject: "SubjectRuntimeProjection") -> str:
        label = cls.status_label_for_subject(subject)
        if not label:
            return ""
        return f"{label} {subject.percent:.1f}%"

    @classmethod
    def counted_declarations(
        cls,
    ) -> Tuple[type["SubjectRuntimeState"], ...]:
        return tuple(
            sorted(
                (
                    declaration
                    for declaration in cls.__registry__.values()
                    if declaration.count_label
                ),
                key=lambda declaration: declaration.count_sort_order,
            )
        )

    @classmethod
    def count_status_label(cls, count: int) -> str:
        if count <= 0 or not cls.count_label:
            return ""
        return cls.count_label.format(count=count)

    @classmethod
    def accepts_server_lifecycle_state(cls, state: type[SubjectRuntimeState]) -> bool:
        """Return whether a live server snapshot may advance this state."""

        del state
        return False


class TerminalSubjectRuntimeState:
    """Trait for subject runtime states that close the current execution."""

    is_terminal: ClassVar[bool] = True


class PendingSubjectRuntimeState:
    """Trait for states fully governed by a live server lifecycle snapshot."""

    @classmethod
    def accepts_server_lifecycle_state(cls, state: type[SubjectRuntimeState]) -> bool:
        return state in (
            QueuedSubjectRuntimeState,
            CompilingSubjectRuntimeState,
            ExecutingSubjectRuntimeState,
        )


class IdleSubjectRuntimeState(PendingSubjectRuntimeState, SubjectRuntimeState):
    state_name = "idle"


class QueuedSubjectRuntimeState(
    PendingSubjectRuntimeState,
    SubjectRuntimeState,
):
    state_name = "queued"
    status_label = "⏳ Queued"
    count_label = "⏳ {count} queued"
    count_sort_order = 5
    is_active = True

    @classmethod
    def formatted_status_for_subject(cls, subject: "SubjectRuntimeProjection") -> str:
        status = super().formatted_status_for_subject(subject)
        if subject.queue_position is None:
            return status
        return f"{status} (q#{subject.queue_position})"


class CompilingSubjectRuntimeState(SubjectRuntimeState):
    state_name = "compiling"
    default_stream = CompileProgressStream
    status_label = "⏳ Compiling"
    count_label = "⏳ {count} compiling"
    count_sort_order = 10
    is_active = True

    @classmethod
    def accepts_server_lifecycle_state(cls, state: type[SubjectRuntimeState]) -> bool:
        return state in (
            CompilingSubjectRuntimeState,
            ExecutingSubjectRuntimeState,
        )


class CompiledSubjectRuntimeState(SubjectRuntimeState):
    state_name = "compiled"
    default_stream = CompileProgressStream
    status_label = "✅ Compiled"
    count_label = "✓ {count} compiled"
    count_sort_order = 30

    @classmethod
    def accepts_server_lifecycle_state(cls, state: type[SubjectRuntimeState]) -> bool:
        return state is ExecutingSubjectRuntimeState


class ExecutingSubjectRuntimeState(SubjectRuntimeState):
    state_name = "executing"
    default_stream = PipelineProgressStream
    status_label = "⚙️ Executing"
    count_label = "⚙️ {count} executing"
    count_sort_order = 20
    is_active = True

    @classmethod
    def accepts_server_lifecycle_state(cls, state: type[SubjectRuntimeState]) -> bool:
        return state is ExecutingSubjectRuntimeState


class CompleteSubjectRuntimeState(
    TerminalSubjectRuntimeState, SubjectRuntimeState
):
    state_name = "complete"
    default_stream = PipelineProgressStream
    status_label = "✅ Complete"
    count_label = "✅ {count} complete"
    count_sort_order = 40


class FailedSubjectRuntimeState(
    TerminalSubjectRuntimeState, SubjectRuntimeState
):
    state_name = "failed"
    status_label = "❌ Failed"
    count_label = "❌ {count} failed"
    count_sort_order = 50

    @classmethod
    def state_stream_from_events(
        cls,
        events: Iterable[ProgressEvent],
    ) -> type[ProgressStream] | None:
        latest_failure_event = max(
            (event for event in events if event.is_failure()),
            key=lambda event: event.timestamp,
            default=None,
        )
        if latest_failure_event is None:
            return cls.default_stream
        return latest_failure_event.stream

    @classmethod
    def percent_from_generic_projection(
        cls,
        *,
        generic_percent: float,
        axis_progress: Tuple["AxisRuntimeProjection", ...],
    ) -> float:
        if generic_percent > 0.0 or not axis_progress:
            return generic_percent
        return sum(axis.percent for axis in axis_progress) / len(axis_progress)

    @classmethod
    def status_label_for_subject(cls, subject: "SubjectRuntimeProjection") -> str:
        if subject.state_stream is CompileProgressStream:
            return "❌ Compile Failed"
        return cls.status_label


@dataclass(frozen=True)
class AxisRuntimeProjection:
    axis_id: str
    percent: float
    step_name: str
    is_complete: bool
    is_failed: bool

    @classmethod
    def from_generic_axis(
        cls,
        generic_axis: GenericAxisProjection,
    ) -> "AxisRuntimeProjection":
        return cls(
            axis_id=generic_axis.axis_id,
            percent=generic_axis.percent,
            step_name=generic_axis.step_name,
            is_complete=generic_axis.is_complete,
            is_failed=generic_axis.is_failed,
        )


@dataclass(frozen=True)
class SubjectRuntimeIdentity:
    execution_id: str
    subject_id: str

    @classmethod
    def from_generic_subject(
        cls,
        generic_subject: GenericSubjectProjection[type[SubjectRuntimeState]],
    ) -> "SubjectRuntimeIdentity":
        return cls(
            execution_id=generic_subject.execution_id,
            subject_id=generic_subject.subject_id,
        )


@dataclass(frozen=True)
class SubjectRuntimeProjection:
    identity: SubjectRuntimeIdentity
    state: type[SubjectRuntimeState]
    percent: float
    axis_progress: Tuple[AxisRuntimeProjection, ...]
    latest_timestamp: float
    state_stream: type[ProgressStream] | None = None
    queue_position: int | None = None

    @classmethod
    def from_generic_subject(
        cls,
        generic_subject: GenericSubjectProjection[type[SubjectRuntimeState]],
        *,
        state_stream: type[ProgressStream] | None = None,
    ) -> "SubjectRuntimeProjection":
        axis_progress = tuple(
            AxisRuntimeProjection.from_generic_axis(axis)
            for axis in generic_subject.axis_progress
        )
        return cls(
            identity=SubjectRuntimeIdentity.from_generic_subject(generic_subject),
            state=generic_subject.state,
            percent=generic_subject.state.percent_from_generic_projection(
                generic_percent=generic_subject.percent,
                axis_progress=axis_progress,
            ),
            axis_progress=axis_progress,
            latest_timestamp=generic_subject.latest_timestamp,
            state_stream=state_stream,
        )

    @property
    def execution_id(self) -> str:
        return self.identity.execution_id

    @property
    def subject_id(self) -> str:
        return self.identity.subject_id

    @property
    def active_axes(self) -> Tuple[AxisRuntimeProjection, ...]:
        return tuple(
            axis
            for axis in self.axis_progress
            if not axis.is_complete and not axis.is_failed
        )

    @property
    def is_terminal(self) -> bool:
        return self.state.is_terminal

    @property
    def is_active(self) -> bool:
        return self.state.is_active

    @property
    def status_label(self) -> str:
        return self.state.status_label_for_subject(self)

    @property
    def formatted_status(self) -> str:
        return self.state.formatted_status_for_subject(self)


@dataclass
class ExecutionRuntimeProjection:
    subjects: List[SubjectRuntimeProjection] = field(default_factory=list)
    by_identity: Dict[SubjectRuntimeIdentity, SubjectRuntimeProjection] = field(
        default_factory=dict
    )
    by_subject_latest: Dict[str, SubjectRuntimeProjection] = field(default_factory=dict)
    state_counts: Dict[type[SubjectRuntimeState], int] = field(default_factory=dict)
    overall_percent: float = 0.0

    @classmethod
    def from_generic_projection(
        cls,
        generic_projection: GenericExecutionProjection[type[SubjectRuntimeState]],
        events_by_identity: (
            Mapping[SubjectRuntimeIdentity, Sequence[ProgressEvent]] | None
        ) = None,
    ) -> "ExecutionRuntimeProjection":
        projection = cls()

        for generic_subject in generic_projection.subjects:
            identity = SubjectRuntimeIdentity.from_generic_subject(generic_subject)
            projection.add_subject(
                SubjectRuntimeProjection.from_generic_subject(
                    generic_subject,
                    state_stream=generic_subject.state.state_stream_from_events(
                        ()
                        if events_by_identity is None
                        else events_by_identity.get(identity, ())
                    ),
                )
            )

        for generic_subject in generic_projection.by_subject_latest.values():
            projection.mark_latest(
                SubjectRuntimeIdentity.from_generic_subject(generic_subject)
            )

        projection.recalculate_summary()

        return projection

    def count_for_state(self, state: type[SubjectRuntimeState]) -> int:
        return self.state_counts.get(state, 0)

    def count_status_labels(self) -> Tuple[str, ...]:
        labels: List[str] = []
        for declaration in SubjectRuntimeState.counted_declarations():
            label = declaration.count_status_label(
                self.count_for_state(declaration)
            )
            if label:
                labels.append(label)
        return tuple(labels)

    @property
    def has_active_work(self) -> bool:
        """Whether any latest subject projection represents live work."""

        return any(subject.is_active for subject in self.by_subject_latest.values())

    def add_subject(self, subject_projection: SubjectRuntimeProjection) -> None:
        self.subjects.append(subject_projection)
        self.by_identity[subject_projection.identity] = subject_projection

    def upsert_subject(self, subject_projection: SubjectRuntimeProjection) -> None:
        existing = self.by_identity.get(subject_projection.identity)
        if existing is None:
            self.add_subject(subject_projection)
            return
        self.subjects[self.subjects.index(existing)] = subject_projection
        self.by_identity[subject_projection.identity] = subject_projection

    def mark_latest(self, identity: SubjectRuntimeIdentity) -> None:
        self.by_subject_latest[identity.subject_id] = self.by_identity[identity]

    def get_subject(
        self, subject_id: str, execution_id: Optional[str] = None
    ) -> Optional[SubjectRuntimeProjection]:
        if execution_id is not None:
            return self.by_identity.get(SubjectRuntimeIdentity(execution_id, subject_id))
        return self.by_subject_latest.get(subject_id)

    def reconcile_server_executions(
        self,
        *,
        running_executions: Sequence[RunningExecutionInfo],
        queued_executions: Sequence[QueuedExecutionInfo],
    ) -> None:
        """Project the authoritative live server queue over retained event history."""

        running_identities = {
            SubjectRuntimeIdentity(entry.execution_id, entry.subject_id)
            for entry in running_executions
        }
        for entry in queued_executions:
            identity = SubjectRuntimeIdentity(entry.execution_id, entry.subject_id)
            if identity in running_identities:
                continue
            current = self.by_identity.get(identity)
            if current is None or current.state.accepts_server_lifecycle_state(
                QueuedSubjectRuntimeState
            ):
                self.upsert_subject(
                    SubjectRuntimeProjection(
                        identity=identity,
                        state=QueuedSubjectRuntimeState,
                        percent=0.0,
                        axis_progress=(),
                        latest_timestamp=(
                            0.0 if current is None else current.latest_timestamp
                        ),
                        queue_position=entry.queue_position,
                    )
                )
            self.mark_latest(identity)

        for entry in running_executions:
            identity = SubjectRuntimeIdentity(entry.execution_id, entry.subject_id)
            current = self.by_identity.get(identity)
            server_state = (
                CompilingSubjectRuntimeState
                if entry.compile_only
                else ExecutingSubjectRuntimeState
            )
            if current is None or current.state.accepts_server_lifecycle_state(
                server_state
            ):
                self.upsert_subject(
                    SubjectRuntimeProjection(
                        identity=identity,
                        state=server_state,
                        percent=0.0 if current is None else current.percent,
                        axis_progress=(
                            () if current is None else current.axis_progress
                        ),
                        latest_timestamp=max(
                            entry.start_time,
                            0.0 if current is None else current.latest_timestamp,
                        ),
                    )
                )
            self.mark_latest(identity)

        self.recalculate_summary()

    def recalculate_summary(self) -> None:
        self.state_counts = {
            declaration: 0
            for declaration in SubjectRuntimeState.__registry__.values()
        }
        for subject in self.by_subject_latest.values():
            self.state_counts[subject.state] += 1
        self.overall_percent = (
            sum(subject.percent for subject in self.by_subject_latest.values())
            / len(self.by_subject_latest)
            if self.by_subject_latest
            else 0.0
        )


class _OpenHCSProjectionAdapter(
    ProgressProjectionAdapterABC[ProgressEvent, SubjectRuntimeState]
):
    compile_channel = CompileProgressStream.name
    pipeline_channel = PipelineProgressStream.name

    def subject_id(self, event: ProgressEvent) -> str:
        return event.subject_id

    def axis_id(self, event: ProgressEvent) -> str:
        return event.axis_id

    def step_name(self, event: ProgressEvent) -> str:
        return event.step_name

    def percent(self, event: ProgressEvent) -> float:
        return event.percent

    def timestamp(self, event: ProgressEvent) -> float:
        return event.timestamp

    def channel(self, event: ProgressEvent) -> str:
        return event.stream.name

    def known_axes(self, events: Iterable[ProgressEvent]) -> List[str]:
        axes: set[str] = set()
        for event in events:
            if event.partition_values:
                axes.update(event.partition_values)
        return sorted(axes)

    def is_failure_event(self, event: ProgressEvent) -> bool:
        return event.is_failure()

    def is_success_terminal_event(self, event: ProgressEvent) -> bool:
        return event.is_success_terminal()

    def state_idle(self) -> type[SubjectRuntimeState]:
        return IdleSubjectRuntimeState

    def state_idle_from_events(
        self,
        events: Sequence[ProgressEvent],
    ) -> type[SubjectRuntimeState]:
        if any(
            event.worker_assignments is not None or event.phase is QueuedProgressPhase
            for event in events
        ):
            return QueuedSubjectRuntimeState
        return self.state_idle()

    def state_compiling(self) -> type[SubjectRuntimeState]:
        return CompilingSubjectRuntimeState

    def state_compiled(self) -> type[SubjectRuntimeState]:
        return CompiledSubjectRuntimeState

    def state_executing(self) -> type[SubjectRuntimeState]:
        return ExecutingSubjectRuntimeState

    def state_complete(self) -> type[SubjectRuntimeState]:
        return CompleteSubjectRuntimeState

    def state_failed(self) -> type[SubjectRuntimeState]:
        return FailedSubjectRuntimeState


_PROJECTION_ADAPTER = _OpenHCSProjectionAdapter()


def build_execution_runtime_projection(
    events_by_execution: Mapping[str, List[ProgressEvent]],
    *,
    running_executions: Sequence[RunningExecutionInfo] = (),
    queued_executions: Sequence[QueuedExecutionInfo] = (),
) -> ExecutionRuntimeProjection:
    events_by_identity: Dict[SubjectRuntimeIdentity, List[ProgressEvent]] = {}
    for execution_id, events in events_by_execution.items():
        for event in events:
            events_by_identity.setdefault(
                SubjectRuntimeIdentity(execution_id, event.subject_id),
                [],
            ).append(event)

    generic_projection = build_execution_projection(
        events_by_execution,
        adapter=_PROJECTION_ADAPTER,
    )
    projection = ExecutionRuntimeProjection.from_generic_projection(
        generic_projection,
        events_by_identity=events_by_identity,
    )
    projection.reconcile_server_executions(
        running_executions=running_executions,
        queued_executions=queued_executions,
    )
    return projection
