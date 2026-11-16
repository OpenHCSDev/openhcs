"""A batch that errors out because it was stopped ends cancelled, not failed."""

from __future__ import annotations

import asyncio

import pytest

from openhcs.core.execution.execution_state import (
    ExecutionCancelled,
    ExecutionFailed,
    ManagerExecutionState,
)
from tests.unit.pyqt_gui.session_harness import caller_session


@pytest.mark.parametrize(
    "state",
    [state for state in ManagerExecutionState if state.stop_pending],
)
def test_a_stopped_batch_that_errors_is_cancelled(state: ManagerExecutionState) -> None:
    with caller_session() as session:
        session.batch.begin_batch(("dataset",))
        session.execution_state = state

        asyncio.run(session.handle_execution_failure())

        assert dict(session.batch.terminal_items()) == {"dataset": ExecutionCancelled}
        assert session.execution_state is ManagerExecutionState.IDLE


def test_a_running_batch_that_errors_is_failed() -> None:
    with caller_session() as session:
        session.batch.begin_batch(("dataset",))
        session.execution_state = ManagerExecutionState.RUNNING

        asyncio.run(session.handle_execution_failure())

        assert dict(session.batch.terminal_items()) == {"dataset": ExecutionFailed}
        assert session.execution_state is ManagerExecutionState.IDLE
