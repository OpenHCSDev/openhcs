"""One measured pipeline run driven through the OpenHCS session.

The benchmark CLI is a headless session client: it adds the dataset, sets the
pipeline source, initializes, compiles and runs it with the same
SessionOperation classes the GUI and MCP use. The run request carries the
submission and wait timeouts; Ctrl-C stops the batch through StopExecution.
"""

from __future__ import annotations

import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path

from openhcs.agent.dto.session import (
    DatasetPipelineSourceRequest,
    DatasetRootsRequest,
    DatasetRowState,
    DatasetRunRequest,
    DatasetTargetsRequest,
    SessionOperationResult,
    StopExecutionRequest,
)
from openhcs.authoring.session.events import (
    CompilationFailed,
    ErrorReported,
    InitializationFailed,
    RunTimedOut,
    SessionEvent,
)
from openhcs.authoring.session.operations.datasets import (
    AddDatasets,
    CompileDatasets,
    InitializeDatasets,
    RunDatasets,
    SetDatasetPipeline,
    StopExecution,
)
from openhcs.authoring.session.session import Session
from openhcs.authoring.session.views import DatasetListView

EVENT_WAIT_SECONDS = 0.5
STOP_GRACE_SECONDS = 30.0


class MeasuredRunEnded(RuntimeError):
    """The run ended without completing; ``row`` is its final dataset row."""

    def __init__(self, message: str, row: DatasetRowState | None) -> None:
        super().__init__(message)
        self.row = row


class MeasuredRunTimedOut(MeasuredRunEnded):
    """The run outlived its wait timeout and the session stopped it."""


@dataclass
class SessionMeasuredRun:
    """Drive one dataset through the session and wait on its events."""

    session: Session
    scope_id: str | None = None
    _sequence: int = 0

    def add(self, plate: Path, execution_plate: Path | None) -> str:
        result = self._require(
            AddDatasets,
            DatasetRootsRequest(
                roots=(str(plate),),
                execution_root=None if execution_plate is None else str(execution_plate),
            ),
        )
        (self.scope_id,) = result.target_scope_ids
        return self.scope_id

    def set_pipeline_source(self, source: str) -> None:
        self._require(
            SetDatasetPipeline,
            DatasetPipelineSourceRequest(scope_id=self._scope_id, pipeline_source=source),
        )

    def initialize(self) -> DatasetRowState:
        self._require(InitializeDatasets, DatasetTargetsRequest((self._scope_id,)))
        return self._wait(
            lambda row: row.initialized and not row.init_pending,
            failures=(InitializationFailed,),
        )

    def compile(self) -> DatasetRowState:
        self._require(CompileDatasets, DatasetTargetsRequest((self._scope_id,)))
        return self._wait(
            lambda row: row.compiled and not row.compile_pending,
            failures=(CompilationFailed,),
        )

    def run(self, request: DatasetRunRequest) -> DatasetRowState:
        """Run to a terminal status; Ctrl-C stops the batch, then re-raises."""

        self._require(RunDatasets, request)
        try:
            row = self._wait(self._run_finished, failures=())
        except KeyboardInterrupt:
            self.stop()
            raise
        if row.terminal_status != "complete":
            raise MeasuredRunEnded(
                f"Run of {self._scope_id} ended {row.terminal_status}.", row
            )
        return row

    def stop(self) -> DatasetRowState:
        """Stop the running batch; force it when a graceful stop does not end it."""

        for force in (False, True):
            if not self.session.execution_state.busy:
                break
            self.session.invoke(StopExecution, StopExecutionRequest(force=force))
            deadline = time.monotonic() + STOP_GRACE_SECONDS
            while self.session.execution_state.busy and time.monotonic() < deadline:
                self.session.events_after(
                    self.session.event_log.last_sequence,
                    timeout_seconds=EVENT_WAIT_SECONDS,
                )
        return self.row()

    def row(self) -> DatasetRowState:
        (row,) = (
            row
            for row in self.session.view(DatasetListView).rows
            if row.scope_id == self._scope_id
        )
        return row

    def _run_finished(self, row: DatasetRowState) -> bool:
        return (
            row.terminal_status is not None
            and not row.execution_active
            and not self.session.execution_state.busy
        )

    @property
    def _scope_id(self) -> str:
        if self.scope_id is None:
            raise RuntimeError("Add the dataset first.")
        return self.scope_id

    def _require(self, operation, request) -> SessionOperationResult:
        self._sequence = self.session.event_log.last_sequence
        result = self.session.invoke(operation, request)
        if not result.accepted:
            raise RuntimeError(
                f"{operation.operation_id} was rejected: "
                + "; ".join(error.message for error in result.errors)
            )
        return result

    def _wait(
        self,
        finished: Callable[[DatasetRowState], bool],
        *,
        failures: tuple[type[SessionEvent], ...],
    ) -> DatasetRowState:
        """Follow session events until ``finished`` holds or a failure arrives."""

        timed_out: RunTimedOut | None = None
        while True:
            # Read the row before the events: an event published before the
            # row changed (RunTimedOut before the stop) is then always seen.
            row = self.row()
            done = finished(row)
            for record in self.session.events_after(
                self._sequence, timeout_seconds=0.0 if done else EVENT_WAIT_SECONDS
            ):
                self._sequence = record.sequence
                event = record.event
                if isinstance(event, RunTimedOut):
                    timed_out = event
                elif isinstance(event, failures):
                    raise MeasuredRunEnded(event.message, self.row())
                elif isinstance(event, ErrorReported):
                    print(event.message, file=sys.stderr, flush=True)
            if done:
                if timed_out is not None:
                    raise MeasuredRunTimedOut(timed_out.message, row)
                return row
