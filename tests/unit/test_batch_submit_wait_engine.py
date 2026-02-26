import asyncio

import pytest

from zmqruntime.execution import (
    BatchSubmitWaitEngine,
    CallbackBatchSubmitWaitPolicy,
)


def test_batch_submit_wait_engine_submits_then_waits():
    events: list[str] = []

    async def submit(job: str) -> str:
        events.append(f"submit:{job}")
        return f"id:{job}"

    async def wait(submission_id: str, job: str) -> None:
        events.append(f"wait:{job}:{submission_id}")

    policy = CallbackBatchSubmitWaitPolicy[str](
        submit_fn=submit,
        wait_fn=wait,
        job_key_fn=lambda job: job,
        fail_fast_submit_value=True,
        fail_fast_wait_value=True,
    )

    artifacts = asyncio.run(BatchSubmitWaitEngine[str]().run(["a", "b"], policy))

    assert artifacts == {"a": "id:a", "b": "id:b"}
    assert events == [
        "submit:a",
        "submit:b",
        "wait:a:id:a",
        "wait:b:id:b",
    ]


def test_batch_submit_wait_engine_non_fail_fast_wait_continues():
    errors: list[str] = []
    finals: list[str] = []

    async def submit(job: str) -> str:
        return f"id:{job}"

    async def wait(submission_id: str, job: str) -> None:
        if job == "b":
            raise RuntimeError("failed")

    policy = CallbackBatchSubmitWaitPolicy[str](
        submit_fn=submit,
        wait_fn=wait,
        job_key_fn=lambda job: job,
        fail_fast_submit_value=True,
        fail_fast_wait_value=False,
        on_wait_error_fn=lambda job, error, _idx, _total: errors.append(
            f"{job}:{error}"
        ),
        on_wait_finally_fn=lambda job, _idx, _total: finals.append(job),
    )

    artifacts = asyncio.run(BatchSubmitWaitEngine[str]().run(["a", "b"], policy))

    assert artifacts == {"a": "id:a"}
    assert errors == ["b:failed"]
    assert finals == ["a", "b"]


def test_batch_submit_wait_engine_fail_fast_submit_raises():
    async def submit(job: str) -> str:
        if job == "b":
            raise RuntimeError("submit failed")
        return f"id:{job}"

    async def wait(submission_id: str, job: str) -> None:
        return None

    policy = CallbackBatchSubmitWaitPolicy[str](
        submit_fn=submit,
        wait_fn=wait,
        job_key_fn=lambda job: job,
        fail_fast_submit_value=True,
        fail_fast_wait_value=True,
    )

    with pytest.raises(RuntimeError, match="submit failed"):
        asyncio.run(BatchSubmitWaitEngine[str]().run(["a", "b", "c"], policy))
