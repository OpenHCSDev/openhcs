"""A batch that errors out because it was stopped ends cancelled, not failed."""

from __future__ import annotations

import asyncio

import pytest

from openhcs.authoring.session.execution_control import ExecutionControl
from openhcs.core.execution_state import (
    ExecutionCancelled,
    ExecutionFailed,
    ManagerExecutionState,
)


class _Batch:
    active_plates = ("dataset",)

    def __init__(self) -> None:
        self.terminal: dict[str, type] = {}

    def cancellable_plates(self) -> tuple[str, ...]:
        return self.active_plates

    def execution_id(self, scope_id: str) -> None:
        return None

    def mark_terminal(self, scope_id: str, status: type) -> None:
        self.terminal[scope_id] = status


class _Client:
    async def disconnect(self) -> None:
        return None


class _Session:
    def __init__(self, state: ManagerExecutionState) -> None:
        self.execution_state = state
        self.batch = _Batch()
        self.client = _Client()
        self.finished: list[tuple[type, str]] = []

    def set_dataset_state(self, scope_id: str, state: type) -> None:
        del scope_id, state

    def finish_dataset_execution(self, completion, scope_id: str) -> None:
        self.finished.append((completion.status, scope_id))

    def refresh(self) -> None:
        return None


@pytest.mark.parametrize(
    "state",
    [state for state in ManagerExecutionState if state.stop_pending],
)
def test_a_stopped_batch_that_errors_is_cancelled(state: ManagerExecutionState) -> None:
    session = _Session(state)

    asyncio.run(ExecutionControl(session).handle_execution_failure())

    assert session.finished == [(ExecutionCancelled, "dataset")]
    assert session.batch.terminal == {}
    assert session.execution_state is ManagerExecutionState.IDLE


def test_a_running_batch_that_errors_is_failed() -> None:
    session = _Session(ManagerExecutionState.RUNNING)

    asyncio.run(ExecutionControl(session).handle_execution_failure())

    assert session.finished == []
    assert session.batch.terminal == {"dataset": ExecutionFailed}
    assert session.execution_state is ManagerExecutionState.IDLE
