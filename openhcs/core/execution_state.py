"""Shared execution state vocabulary for workflow status projection."""

from __future__ import annotations

import time
from abc import ABC, abstractmethod
from collections.abc import Callable, Mapping
from dataclasses import asdict, dataclass, fields
from enum import Enum
from math import isfinite
from typing import Any, ClassVar, Self

from metaclass_registry import AutoRegisterMeta
from zmqruntime.messages import MessageFields

from openhcs.constants.constants import (
    OrchestratorCompleted,
    OrchestratorExecFailed,
    OrchestratorReady,
    OrchestratorState,
)


@dataclass(frozen=True, slots=True)
class ExecutionOutputSummary:
    """Typed OpenHCS output-plate fields embedded in a runtime result summary."""

    EXECUTION_RECORD_KEY: ClassVar[str] = "output_summary"

    output_dataset_root: str | None = None
    auto_add_output_dataset: bool | None = None

    def __post_init__(self) -> None:
        if self.output_dataset_root is not None and not isinstance(
            self.output_dataset_root,
            str,
        ):
            raise TypeError("output_dataset_root must be a string or None")
        if self.auto_add_output_dataset is not None and not isinstance(
            self.auto_add_output_dataset,
            bool,
        ):
            raise TypeError(
                "auto_add_output_dataset must be a bool or None"
            )

    @classmethod
    def from_results_summary(
        cls,
        summary: Mapping[str, Any],
    ) -> ExecutionOutputSummary:
        return cls(
            **{
                declared_field.name: summary[declared_field.name]
                for declared_field in fields(cls)
                if declared_field.name in summary
            }
        )

    def results_summary_fields(self) -> dict[str, object]:
        """Project only declared output-plate values for wire enrichment."""

        return {key: value for key, value in asdict(self).items() if value is not None}

    @property
    def is_present(self) -> bool:
        return any(value is not None for value in asdict(self).values())


@dataclass(frozen=True, slots=True)
class PipelineLoadPhase:
    """The resource loads an execution ran in its workers before any lane started.

    Its own interval inside the execution's time bounds, on the same clock
    (``time.time()`` of the server). An execution of a pipeline that was
    prepared, or that declares no load, reports ``loads == 0``.
    """

    RESULTS_SUMMARY_KEY: ClassVar[str] = "load_phase"

    started_at: float
    ended_at: float
    loads: int

    def __post_init__(self) -> None:
        if isinstance(self.loads, bool) or not isinstance(self.loads, int):
            raise TypeError("A load phase counts its loads with an integer.")
        if (
            not isinstance(self.started_at, float)
            or not isinstance(self.ended_at, float)
            or not isfinite(self.started_at)
            or not isfinite(self.ended_at)
        ):
            raise TypeError("A load phase starts and ends at finite float times.")
        if self.ended_at < self.started_at or self.loads < 0:
            raise ValueError("A load phase cannot end before it starts or undo loads.")

    @classmethod
    def timed(cls, load: Callable[[], int]) -> Self:
        """Run the loads and report when they started, ended and how many ran."""
        started_at = time.time()
        loads = load()
        return cls(started_at=started_at, ended_at=time.time(), loads=loads)

    @classmethod
    def without_lanes(cls) -> Self:
        """The phase of an execution that started no lane: nothing was loaded."""
        return cls.timed(lambda: 0)

    @property
    def seconds(self) -> float:
        return self.ended_at - self.started_at

    def results_summary_fields(self) -> dict[str, dict[str, float | int]]:
        """The phase as the execution record's summary carries it."""
        return {self.RESULTS_SUMMARY_KEY: asdict(self)}

    @classmethod
    def from_results_summary(cls, summary: Mapping[str, object]) -> Self:
        """Read the phase an execution record reports; its absence is an error."""
        reported = summary[cls.RESULTS_SUMMARY_KEY]
        if not isinstance(reported, Mapping):
            raise TypeError("An execution record reports its load phase as fields.")
        return cls(**{name.name: reported[name.name] for name in fields(cls)})


@dataclass(frozen=True, slots=True)
class ExecutionCompletionPayload:
    """One typed terminal result passed from polling through UI presentation."""

    status: type[TerminalExecutionStatus]
    execution_id: str | None
    results: Mapping[str, Any]
    output_dataset: ExecutionOutputSummary
    traceback_text: str
    message: str

    @property
    def output_dataset_root(self) -> str | None:
        return self.output_dataset.output_dataset_root

    @property
    def auto_add_output_dataset(self) -> bool | None:
        return self.output_dataset.auto_add_output_dataset

    @classmethod
    def completed(
        cls,
        status: type[TerminalExecutionStatus],
        execution_id: str | None,
        execution_payload: Mapping[str, Any],
    ) -> ExecutionCompletionPayload:
        """Decode the successful runtime payload shape."""

        raw_results = execution_payload.get(MessageFields.RESULTS_SUMMARY, {})
        results = dict(raw_results) if isinstance(raw_results, Mapping) else {}
        return cls(
            status=status,
            execution_id=execution_id,
            results=results,
            output_dataset=ExecutionOutputSummary.from_results_summary(results),
            traceback_text="",
            message="Execution completed",
        )

    @classmethod
    def failed(
        cls,
        status: type[TerminalExecutionStatus],
        execution_id: str | None,
        execution_payload: Mapping[str, Any],
    ) -> ExecutionCompletionPayload:
        """Decode the failed runtime payload shape."""

        return cls(
            status=status,
            execution_id=execution_id,
            results={},
            output_dataset=ExecutionOutputSummary(),
            traceback_text=str(execution_payload.get(MessageFields.TRACEBACK, "")),
            message=str(execution_payload.get(MessageFields.ERROR, "Unknown error")),
        )

    @classmethod
    def cancelled(
        cls,
        status: type[TerminalExecutionStatus],
        execution_id: str | None,
        execution_payload: Mapping[str, Any],
    ) -> ExecutionCompletionPayload:
        """Build the local cancellation completion shape."""

        del execution_payload
        return cls(
            status=status,
            execution_id=execution_id,
            results={},
            output_dataset=ExecutionOutputSummary(),
            traceback_text="",
            message="Execution was cancelled",
        )


class ManagerExecutionState(str, Enum):
    """Plate-manager state with member-owned execution policies."""

    suppresses_stop_failure: bool
    stop_pending: bool
    busy: bool
    run_button_text: str
    allows_auto_add_output: bool
    implicit_stop_force: bool | None

    IDLE = (
        "idle",
        True,
        False,
        False,
        "Run",
        lambda compiled: compiled,
        False,
        None,
    )
    RUNNING = (
        "running",
        False,
        False,
        True,
        "Stop",
        lambda _compiled: True,
        True,
        False,
    )
    STOPPING = (
        "stopping",
        True,
        True,
        True,
        "Stop",
        lambda _compiled: False,
        False,
        None,
    )
    FORCE_KILL_READY = (
        "force_kill_ready",
        True,
        True,
        True,
        "Force Kill",
        lambda _compiled: True,
        False,
        True,
    )

    def __new__(
        cls,
        value: str,
        suppresses_stop_failure: bool,
        stop_pending: bool,
        busy: bool,
        run_button_text: str,
        run_button_enabled: Callable[[bool], bool],
        allows_auto_add_output: bool,
        implicit_stop_force: bool | None,
    ) -> ManagerExecutionState:
        member = str.__new__(cls, value)
        member._value_ = value
        member.suppresses_stop_failure = suppresses_stop_failure
        member.stop_pending = stop_pending
        member.busy = busy
        member.run_button_text = run_button_text
        member._run_button_enabled = run_button_enabled
        member.allows_auto_add_output = allows_auto_add_output
        member.implicit_stop_force = implicit_stop_force
        return member

    def run_button_enabled(self, has_compiled_plate: bool) -> bool:
        """Execute this state's run/stop control availability leaf."""

        return self._run_button_enabled(has_compiled_plate)

    def stop_request(
        self,
        force: bool | None = None,
    ) -> tuple[ManagerExecutionState, bool]:
        """Resolve one stop command and its resulting manager state."""

        requested_force = self.implicit_stop_force if force is None else force
        if requested_force is None:
            raise RuntimeError(f"Execution state {self.value!r} does not accept Stop")
        next_state = (
            ManagerExecutionState.STOPPING
            if requested_force
            else ManagerExecutionState.FORCE_KILL_READY
        )
        return next_state, requested_force


class TerminalExecutionStatus(ABC, metaclass=AutoRegisterMeta):
    """Terminal workflow status shared by UI, MCP, and dev-client polling.

    Each status is a subclass; ``name`` is its spelling on the wire, and
    ``serialized_aliases`` are other runtime spellings it is read from.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    counts_as_failed: ClassVar[bool]
    orchestrator_state: ClassVar[type[OrchestratorState]]
    status_prefix: ClassVar[str]
    emit_failure: ClassVar[bool]
    auto_add_output_dataset: ClassVar[bool]
    serialized_aliases: ClassVar[frozenset[str]] = frozenset()

    @staticmethod
    def named(value: str) -> type[TerminalExecutionStatus]:
        """The status spelled ``value`` or one of its aliases."""
        for status in TerminalExecutionStatus.__registry__.values():
            if value == status.name or value in status.serialized_aliases:
                return status
        raise ValueError(f"{value!r} is not a terminal execution status.")

    @classmethod
    @abstractmethod
    def completion_payload(
        cls,
        *,
        execution_id: str | None,
        execution_payload: Mapping[str, Any],
    ) -> ExecutionCompletionPayload:
        """Decode this status's runtime payload into the terminal result."""


class ExecutionCompleted(TerminalExecutionStatus):
    name = "complete"
    counts_as_failed = False
    orchestrator_state = OrchestratorCompleted
    status_prefix = "✅ Complete"
    emit_failure = False
    auto_add_output_dataset = True

    @classmethod
    def completion_payload(cls, *, execution_id, execution_payload):
        return ExecutionCompletionPayload.completed(cls, execution_id, execution_payload)


class ExecutionFailed(TerminalExecutionStatus):
    name = "failed"
    counts_as_failed = True
    orchestrator_state = OrchestratorExecFailed
    status_prefix = "❌ Exec Failed"
    emit_failure = True
    auto_add_output_dataset = False
    serialized_aliases = frozenset({"error"})

    @classmethod
    def completion_payload(cls, *, execution_id, execution_payload):
        return ExecutionCompletionPayload.failed(cls, execution_id, execution_payload)


class ExecutionCancelled(TerminalExecutionStatus):
    name = "cancelled"
    counts_as_failed = True
    orchestrator_state = OrchestratorReady
    status_prefix = "✗ Cancelled"
    emit_failure = False
    auto_add_output_dataset = False

    @classmethod
    def completion_payload(cls, *, execution_id, execution_payload):
        return ExecutionCompletionPayload.cancelled(cls, execution_id, execution_payload)


def parse_terminal_status(
    status: str | type[TerminalExecutionStatus],
) -> type[TerminalExecutionStatus]:
    """Return the terminal status for a UI/runtime status value."""
    if isinstance(status, type):
        return status
    return TerminalExecutionStatus.named(status)
