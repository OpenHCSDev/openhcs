import asyncio

import pytest

from openhcs.pyqt_gui.widgets.shared.services.batch_workflow_service import (
    BatchWorkflowService,
    CompileJob,
)
from zmqruntime.execution import BatchSubmitWaitEngine


def _job(plate_path: str) -> CompileJob:
    return CompileJob(
        plate_path=plate_path,
        plate_name=plate_path,
        definition_pipeline=[],
        pipeline_config={"x": 1},
    )


def test_compile_policy_with_engine_collects_artifacts_and_callbacks():
    service = BatchWorkflowService.__new__(BatchWorkflowService)
    callback_events: list[tuple[str, str, str]] = []

    async def fake_submit_compile_job(*, job: CompileJob, zmq_client, loop) -> str:
        return f"exec-{job.plate_path}"

    async def fake_wait_compile_job(
        *, submission_id: str, job: CompileJob, zmq_client, loop
    ) -> None:
        callback_events.append(("wait", job.plate_path, submission_id))

    service._submit_compile_job = fake_submit_compile_job
    service._wait_compile_job = fake_wait_compile_job

    jobs = [_job("/tmp/a"), _job("/tmp/b")]
    policy = service._make_compile_policy(
        zmq_client=object(),
        loop=object(),
        fail_fast_submit=False,
        fail_fast_wait=False,
        on_wait_success=lambda job, submission_id, _idx, _total: callback_events.append(
            ("success", job.plate_path, submission_id)
        ),
    )
    artifacts = asyncio.run(BatchSubmitWaitEngine[CompileJob]().run(jobs, policy))

    assert artifacts == {
        "/tmp/a": "exec-/tmp/a",
        "/tmp/b": "exec-/tmp/b",
    }
    assert callback_events == [
        ("wait", "/tmp/a", "exec-/tmp/a"),
        ("success", "/tmp/a", "exec-/tmp/a"),
        ("wait", "/tmp/b", "exec-/tmp/b"),
        ("success", "/tmp/b", "exec-/tmp/b"),
    ]


def test_compile_policy_fail_fast_submit_raises():
    service = BatchWorkflowService.__new__(BatchWorkflowService)

    async def fake_submit_compile_job(*, job: CompileJob, zmq_client, loop) -> str:
        if job.plate_path == "/tmp/b":
            raise RuntimeError("boom")
        return f"exec-{job.plate_path}"

    async def fake_wait_compile_job(
        *, submission_id: str, job: CompileJob, zmq_client, loop
    ) -> None:
        return None

    service._submit_compile_job = fake_submit_compile_job
    service._wait_compile_job = fake_wait_compile_job

    policy = service._make_compile_policy(
        zmq_client=object(),
        loop=object(),
        fail_fast_submit=True,
        fail_fast_wait=True,
    )

    with pytest.raises(RuntimeError, match="boom"):
        asyncio.run(
            BatchSubmitWaitEngine[CompileJob]().run(
                [_job("/tmp/a"), _job("/tmp/b"), _job("/tmp/c")], policy
            )
        )

def test_compile_policy_non_fail_fast_wait_tracks_error_and_finally():
    service = BatchWorkflowService.__new__(BatchWorkflowService)
    callbacks = {"start": [], "success": [], "error": [], "finally": []}

    async def fake_submit_compile_job(*, job: CompileJob, zmq_client, loop) -> str:
        return f"exec-{job.plate_path}"

    async def fake_wait_compile_job(
        *, submission_id: str, job: CompileJob, zmq_client, loop
    ) -> None:
        if job.plate_path == "/tmp/b":
            raise RuntimeError("compile failed")

    service._submit_compile_job = fake_submit_compile_job
    service._wait_compile_job = fake_wait_compile_job

    policy = service._make_compile_policy(
        zmq_client=object(),
        loop=object(),
        fail_fast_submit=False,
        fail_fast_wait=False,
        on_wait_start=lambda job, _idx, _total: callbacks["start"].append(
            job.plate_path
        ),
        on_wait_success=lambda job, execution_id, _idx, _total: callbacks[
            "success"
        ].append((job.plate_path, execution_id)),
        on_wait_error=lambda job, error, _idx, _total: callbacks["error"].append(
            (job.plate_path, str(error))
        ),
        on_wait_finally=lambda job, _idx, _total: callbacks["finally"].append(
            job.plate_path
        ),
    )
    artifacts = asyncio.run(
        BatchSubmitWaitEngine[CompileJob]().run([_job("/tmp/a"), _job("/tmp/b")], policy)
    )

    assert artifacts == {"/tmp/a": "exec-/tmp/a"}
    assert callbacks["start"] == ["/tmp/a", "/tmp/b"]
    assert callbacks["success"] == [("/tmp/a", "exec-/tmp/a")]
    assert callbacks["error"] == [("/tmp/b", "compile failed")]
    assert callbacks["finally"] == ["/tmp/a", "/tmp/b"]
