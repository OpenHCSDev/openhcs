from zmqruntime.execution import (
    ExecutionStatusPoller,
    CallbackExecutionStatusPollPolicy,
)


def test_execution_status_poller_handles_running_then_complete():
    events: list[str] = []
    responses = iter(
        [
            {"status": "ok", "execution": {"status": "queued"}},
            {"status": "ok", "execution": {"status": "running"}},
            {"status": "ok", "execution": {"status": "complete"}},
        ]
    )

    def poll_status(_execution_id: str):
        return next(responses)

    policy = CallbackExecutionStatusPollPolicy(
        poll_status_fn=poll_status,
        poll_interval_seconds_value=0.0,
        on_running_fn=lambda execution_id, _payload: events.append(
            f"running:{execution_id}"
        ),
        on_terminal_fn=lambda execution_id, terminal_status, _payload: events.append(
            f"terminal:{execution_id}:{terminal_status}"
        ),
    )

    ExecutionStatusPoller().run("exec-1", policy)

    assert events == ["running:exec-1", "terminal:exec-1:complete"]


def test_execution_status_poller_handles_status_error():
    events: list[str] = []

    policy = CallbackExecutionStatusPollPolicy(
        poll_status_fn=lambda _execution_id: {"status": "error", "error": "unavailable"},
        poll_interval_seconds_value=0.0,
        on_status_error_fn=lambda execution_id, message: events.append(
            f"error:{execution_id}:{message}"
        ),
    )

    ExecutionStatusPoller().run("exec-2", policy)

    assert events == ["error:exec-2:unavailable"]


def test_execution_status_poller_poll_exception_can_continue():
    events: list[str] = []
    state = {"count": 0}

    def poll_status(_execution_id: str):
        state["count"] += 1
        if state["count"] == 1:
            raise RuntimeError("transient")
        return {"status": "ok", "execution": {"status": "cancelled"}}

    policy = CallbackExecutionStatusPollPolicy(
        poll_status_fn=poll_status,
        poll_interval_seconds_value=0.0,
        on_poll_exception_fn=lambda _execution_id, _error: True,
        on_terminal_fn=lambda execution_id, terminal_status, _payload: events.append(
            f"terminal:{execution_id}:{terminal_status}"
        ),
    )

    ExecutionStatusPoller().run("exec-3", policy)

    assert events == ["terminal:exec-3:cancelled"]
