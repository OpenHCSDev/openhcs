"""ZMQ progress event construction for execution-server phases."""

from __future__ import annotations

import threading
from collections.abc import Callable
from dataclasses import dataclass, field, replace
from typing import Self

from openhcs.core.progress import (
    ProgressEvent,
    ProgressExecutionContext,
    ProgressPhase,
    ProgressQueue,
    ProgressStatus,
)


@dataclass(frozen=True, slots=True)
class ZMQCompilerProgressQueue(ProgressQueue):
    """Compiler progress, reported as the subject of the ZMQ request."""

    enqueue: Callable[[ProgressEvent], None]
    subject_id: str

    def put(self, event: ProgressEvent) -> None:
        self.enqueue(replace(event, subject_id=self.subject_id))


@dataclass(frozen=True, slots=True)
class ZMQProgressEmitter(ProgressExecutionContext):
    """Semantic progress-event emitter for one ZMQ execution."""

    enqueue: Callable[[ProgressEvent], None]

    def emit(self, **event_fields) -> None:
        self.enqueue(self.event(**event_fields))

    def compile_started(self, step_count: int) -> None:
        self.emit(
            axis_id="",
            step_name="pipeline",
            total=step_count,
            phase=ProgressPhase.COMPILE,
            status=ProgressStatus.STARTED,
            completed=0,
            percent=0.0,
        )

    def compile_heartbeat(self, step_count: int) -> None:
        self.emit(
            axis_id="",
            step_name="pipeline",
            total=step_count,
            phase=ProgressPhase.COMPILE,
            status=ProgressStatus.RUNNING,
            completed=0,
            percent=0.0,
        )

    def planned_init_started(
        self,
        *,
        partition_values: list[str],
        step_names: list[str],
    ) -> None:
        self.emit(
            axis_id="",
            step_name="",
            phase=ProgressPhase.INIT,
            status=ProgressStatus.STARTED,
            percent=0.0,
            completed=0,
            total=1,
            partition_values=sorted(partition_values),
            step_names=step_names,
        )

    def artifact_init_started(
        self,
        *,
        compiled_axis_ids: list[str],
        worker_assignments: dict[str, list[str]],
        step_names: list[str],
    ) -> None:
        self.emit(
            axis_id="",
            step_name="",
            phase=ProgressPhase.INIT,
            status=ProgressStatus.STARTED,
            percent=0.0,
            completed=0,
            total=1,
            partition_values=compiled_axis_ids,
            worker_assignments=worker_assignments,
            step_names=step_names,
        )

    def compiled_init_started(
        self,
        *,
        compiled_axis_ids: list[str],
        worker_assignments: dict[str, list[str]],
    ) -> None:
        self.emit(
            axis_id="",
            step_name="",
            phase=ProgressPhase.INIT,
            status=ProgressStatus.STARTED,
            percent=0.0,
            completed=0,
            total=1,
            partition_values=compiled_axis_ids,
            worker_assignments=worker_assignments,
        )

    def compile_succeeded(
        self,
        *,
        step_count: int,
        compiled_axis_ids: list[str],
        worker_assignments: dict[str, list[str]],
    ) -> None:
        self.emit(
            axis_id="",
            step_name="pipeline",
            total=step_count,
            phase=ProgressPhase.COMPILE,
            status=ProgressStatus.SUCCESS,
            completed=1,
            percent=100.0,
            partition_values=compiled_axis_ids,
            worker_assignments=worker_assignments,
        )

    def axis_compile_succeeded(self, axis_id: str) -> None:
        self.emit(
            axis_id=axis_id,
            step_name="compilation",
            phase=ProgressPhase.COMPILE,
            status=ProgressStatus.SUCCESS,
            completed=1,
            total=1,
            percent=100.0,
        )

    def compile_failed(self, *, axis_ids: list[str], error: str) -> None:
        failed_axis_ids = sorted(axis_ids) if axis_ids else ["pipeline"]
        for axis_id in failed_axis_ids:
            self.emit(
                axis_id=axis_id,
                step_name="compilation",
                phase=ProgressPhase.COMPILE,
                status=ProgressStatus.FAILED,
                completed=0,
                total=1,
                percent=0.0,
                error=error,
                message=error,
            )


@dataclass(slots=True)
class ZMQCompileProgressHeartbeat:
    """Periodic compile progress heartbeat during long synchronous compilation."""

    progress_emitter: ZMQProgressEmitter
    step_count: int
    interval_seconds: float = 2.0
    _stop_event: threading.Event = field(init=False, repr=False)
    _thread: threading.Thread | None = field(init=False, default=None, repr=False)

    def __post_init__(self) -> None:
        self._stop_event = threading.Event()

    def __enter__(self) -> Self:
        self._thread = threading.Thread(target=self._run, daemon=True)
        self._thread.start()
        return self

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        self._stop_event.set()
        if self._thread is not None:
            self._thread.join(timeout=self.interval_seconds + 1.0)

    def _run(self) -> None:
        while not self._stop_event.wait(self.interval_seconds):
            self.progress_emitter.compile_heartbeat(self.step_count)
