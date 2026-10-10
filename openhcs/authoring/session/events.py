"""Session events: what changed, pushed to every subscribed client.

Each kind of change is one frozen dataclass under :class:`SessionEvent`. A
client either subscribes (the Qt GUI marshals each event to its thread) or
blocks on :meth:`SessionEventLog.after` for the events past a sequence number
(headless MCP), so no client polls session state on a timer.
"""

from __future__ import annotations

import threading
from abc import ABC
from collections import deque
from collections.abc import Callable
from dataclasses import dataclass
from typing import Any, ClassVar

from openhcs.core.execution_state import (
    ExecutionCompletionPayload,
    ManagerExecutionState,
)
from openhcs.constants.constants import OrchestratorState


@dataclass(frozen=True)
class SessionEvent(ABC):
    """One change to session state. ``kind`` is the class name."""

    kind: ClassVar[str | None] = None

    def __init_subclass__(cls, **kwargs: Any) -> None:
        super().__init_subclass__(**kwargs)
        cls.kind = cls.__name__

    @property
    def scope_id(self) -> str:
        """Dataset scope the event concerns ("" for session-wide events)."""

        return ""

    @property
    def message(self) -> str:
        """One line describing the change for clients without a renderer."""

        return self.kind or ""


@dataclass(frozen=True, slots=True)
class DatasetScopedEvent(SessionEvent):
    """An event about one dataset scope."""

    dataset_scope_id: str

    @property
    def scope_id(self) -> str:
        return self.dataset_scope_id


@dataclass(frozen=True, slots=True)
class StatusReported(SessionEvent):
    text: str

    @property
    def message(self) -> str:
        return self.text


@dataclass(frozen=True, slots=True)
class ErrorReported(SessionEvent):
    text: str

    @property
    def message(self) -> str:
        return self.text


@dataclass(frozen=True, slots=True)
class DatasetsChanged(SessionEvent):
    """Dataset rows (membership, order or per-row status) changed."""


@dataclass(frozen=True, slots=True)
class AvailabilityChanged(SessionEvent):
    """Which operations are available may have changed."""


@dataclass(frozen=True, slots=True)
class SelectionChanged(SessionEvent):
    selected_scope_ids: tuple[str, ...]
    current_scope_id: str

    @property
    def scope_id(self) -> str:
        return self.current_scope_id


@dataclass(frozen=True, slots=True)
class DatasetStateChanged(DatasetScopedEvent):
    state: OrchestratorState

    @property
    def message(self) -> str:
        return f"{self.dataset_scope_id}: {self.state.value}"


@dataclass(frozen=True, slots=True)
class DatasetConfigChanged(DatasetScopedEvent):
    effective_config: object


@dataclass(frozen=True, slots=True)
class CompiledStateChanged(DatasetScopedEvent):
    compiled: object | None

    @property
    def message(self) -> str:
        state = "compiled" if self.compiled is not None else "not compiled"
        return f"{self.dataset_scope_id}: {state}"


@dataclass(frozen=True, slots=True)
class PipelineChanged(DatasetScopedEvent):
    """The dataset's pipeline steps changed."""


@dataclass(frozen=True, slots=True)
class PipelineImported(DatasetScopedEvent):
    """A pipeline was imported into the dataset from a source workspace."""


@dataclass(frozen=True, slots=True)
class GlobalConfigChanged(SessionEvent):
    config: object


@dataclass(frozen=True, slots=True)
class ExecutionStateChanged(SessionEvent):
    state: ManagerExecutionState

    @property
    def message(self) -> str:
        return self.state.value


@dataclass(frozen=True, slots=True)
class DatasetRunning(DatasetScopedEvent):
    @property
    def message(self) -> str:
        return f"Running {self.dataset_scope_id}"


@dataclass(frozen=True, slots=True)
class DatasetExecutionFinished(DatasetScopedEvent):
    completion: ExecutionCompletionPayload

    @property
    def message(self) -> str:
        return f"{self.dataset_scope_id}: {self.completion.status.value}"


@dataclass(frozen=True, slots=True)
class BatchFinished(SessionEvent):
    completed_count: int
    failed_count: int

    @property
    def message(self) -> str:
        return (
            f"All done: {self.completed_count} completed, "
            f"{self.failed_count} failed"
        )


@dataclass(frozen=True, slots=True)
class RunTimedOut(SessionEvent):
    """A run outlived its wait timeout; the session force-stopped the batch."""

    scope_ids: tuple[str, ...]
    wait_timeout_ms: int

    @property
    def message(self) -> str:
        return (
            f"Run of {len(self.scope_ids)} dataset(s) exceeded "
            f"{self.wait_timeout_ms} ms; stopping."
        )


@dataclass(frozen=True, slots=True)
class InitializationFailed(DatasetScopedEvent):
    dataset_name: str
    error: str

    @property
    def message(self) -> str:
        return f"Failed to initialize {self.dataset_name}: {self.error}"


@dataclass(frozen=True, slots=True)
class CompilationFailed(DatasetScopedEvent):
    dataset_name: str
    error: str

    @property
    def message(self) -> str:
        return f"Compilation failed for {self.dataset_name}: {self.error}"


@dataclass(frozen=True, slots=True)
class ProgressStarted(SessionEvent):
    total: int


@dataclass(frozen=True, slots=True)
class ProgressAdvanced(SessionEvent):
    done: int


@dataclass(frozen=True, slots=True)
class ProgressFinished(SessionEvent):
    pass


@dataclass(frozen=True, slots=True)
class LogsCleared(SessionEvent):
    pass


@dataclass(frozen=True, slots=True)
class RuntimeProjectionChanged(SessionEvent):
    projection: object


@dataclass(frozen=True, slots=True)
class ServerConnectionChanged(SessionEvent):
    status: object


@dataclass(frozen=True, slots=True)
class ServerCompatibilityObserved(SessionEvent):
    compatibility: object


@dataclass(frozen=True, slots=True)
class DebugSnapshotAvailable(SessionEvent):
    notification: object


@dataclass(frozen=True, slots=True)
class LiveMeasurementAvailable(SessionEvent):
    notification: object


@dataclass(frozen=True, slots=True)
class RuntimeArtifactAvailable(SessionEvent):
    notification: object


@dataclass(frozen=True, slots=True)
class PresentationRequested(SessionEvent):
    """A renderer operation asked the attached renderer to present something."""

    operation: type
    request: object


@dataclass(frozen=True, slots=True)
class SessionEventRecord:
    """One published event and its position in the session's event order."""

    sequence: int
    event: SessionEvent


SessionEventListener = Callable[[SessionEventRecord], None]


class SessionEventLog:
    """Ordered, bounded record of published events plus live subscribers."""

    def __init__(self, *, retained: int = 2048) -> None:
        self._records: deque[SessionEventRecord] = deque(maxlen=retained)
        self._next_sequence = 1
        self._condition = threading.Condition()
        self._listeners: list[SessionEventListener] = []

    @property
    def last_sequence(self) -> int:
        with self._condition:
            return self._next_sequence - 1

    def publish(self, event: SessionEvent) -> SessionEventRecord:
        with self._condition:
            record = SessionEventRecord(self._next_sequence, event)
            self._next_sequence += 1
            self._records.append(record)
            listeners = tuple(self._listeners)
            self._condition.notify_all()
        for listener in listeners:
            listener(record)
        return record

    def subscribe(self, listener: SessionEventListener) -> Callable[[], None]:
        with self._condition:
            self._listeners.append(listener)

        def unsubscribe() -> None:
            with self._condition:
                if listener in self._listeners:
                    self._listeners.remove(listener)

        return unsubscribe

    def after(
        self,
        sequence: int,
        *,
        timeout_seconds: float = 0.0,
    ) -> tuple[SessionEventRecord, ...]:
        """Records past ``sequence``, waiting up to the timeout for the first."""

        with self._condition:
            self._condition.wait_for(
                lambda: self._next_sequence - 1 > sequence,
                timeout=timeout_seconds,
            )
            return tuple(record for record in self._records if record.sequence > sequence)
