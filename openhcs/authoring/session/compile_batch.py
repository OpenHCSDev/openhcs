"""Compile a batch of datasets: on request, or before execution."""

from __future__ import annotations

import logging
from collections.abc import Mapping
from typing import TYPE_CHECKING

from zmqruntime.execution import BatchSubmitWaitEngine, CallbackBatchSubmitWaitPolicy

from openhcs.authoring.session.compilation import (
    CompiledDataset,
    DatasetPipelineRequest,
    submit_compile,
    wait_for_compile,
)
from openhcs.authoring.session.events import (
    CompilationFailed,
    DatasetsChanged,
    ErrorReported,
    StatusReported,
)
from openhcs.authoring.session.run_requests import dataset_pipeline_request
from openhcs.core.execution_state import TerminalExecutionStatus
from openhcs.constants.constants import OrchestratorState
from openhcs.runtime.zmq_execution_signature import TransportValue

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session

logger = logging.getLogger(__name__)


class CompileBatch:
    """Compile-only batches and compile-before-execution."""

    def __init__(self, session: "Session") -> None:
        self._session = session
        self._engine = BatchSubmitWaitEngine[DatasetPipelineRequest]()

    async def compile_datasets(self, scope_ids: tuple[str, ...]) -> None:
        session = self._session
        for scope_id in scope_ids:
            session.require_work_allowed(scope_id)
        for scope_id in scope_ids:
            previous_execution_id = session.batch.supersede_terminal(scope_id)
            if previous_execution_id is not None:
                session.progress_tracker.clear_execution(previous_execution_id)
        session.mark_compile_pending(scope_ids)
        try:
            client = await session.connect_client()
            session.publish(
                StatusReported(f"Queueing compilation for {len(scope_ids)} dataset(s)...")
            )
            requests: list[DatasetPipelineRequest] = []
            for scope_id in scope_ids:
                try:
                    requests.append(
                        dataset_pipeline_request(scope_id, session.global_config)
                    )
                except Exception as error:
                    self._compile_failed(scope_id, error)

            waiting_announced = False

            def on_wait_start(_request, _index: int, total: int) -> None:
                nonlocal waiting_announced
                if not waiting_announced:
                    waiting_announced = True
                    session.publish(
                        StatusReported(
                            f"Queued {total} compilation job(s). Waiting for completion..."
                        )
                    )

            def on_wait_success(request, _execution_id, _index, _total) -> None:
                session.set_dataset_state(request.scope_id, OrchestratorState.COMPILED)
                logger.info("Successfully compiled %s", request.scope_id)

            def on_failure(request, error, _index, _total) -> None:
                self._compile_failed(request.scope_id, error)

            def on_wait_finally(request, _index, _total) -> None:
                session.clear_compile_pending((request.scope_id,))

            await self._engine.run(
                requests,
                self._policy(
                    client,
                    fail_fast=False,
                    on_submit_error=on_failure,
                    on_wait_start=on_wait_start,
                    on_wait_success=on_wait_success,
                    on_wait_error=on_failure,
                    on_wait_finally=on_wait_finally,
                ),
            )
        finally:
            session.clear_compile_pending(scope_ids)
        session.publish(
            StatusReported(f"Compilation completed for {len(scope_ids)} dataset(s)")
        )

    async def compile_before_execution(
        self,
        requests: list[DatasetPipelineRequest],
        config_params: Mapping[str, dict[str, TransportValue]] = {},
    ) -> dict[str, str]:
        """Compile every request; return compile artifact ids by scope id."""

        session = self._session
        client = session.client.require_client()
        requests = [
            request.with_config_params(config_params.get(request.scope_id))
            for request in requests
        ]
        waiting_announced = False

        def on_wait_start(_request, _index, _total) -> None:
            nonlocal waiting_announced
            if not waiting_announced:
                waiting_announced = True
                session.publish(
                    StatusReported(
                        f"Queued {len(requests)} compile job(s) before execution. "
                        "Waiting for completion..."
                    )
                )
            session.publish(DatasetsChanged())

        def on_wait_success(request, _execution_id, index, total) -> None:
            session.publish(StatusReported(f"Compiled {index}/{total}: {request.scope_id}"))
            session.publish(DatasetsChanged())

        def on_failure(request, error, _index, _total) -> None:
            logger.error(
                "Compile-before-execution failed for %s: %s",
                request.scope_id,
                error,
                exc_info=True,
            )
            session.batch.mark_terminal(request.scope_id, TerminalExecutionStatus.FAILED)
            session.publish(ErrorReported(f"Compile failed for {request.scope_id}: {error}"))
            session.publish(DatasetsChanged())

        return await self._engine.run(
            requests,
            self._policy(
                client,
                fail_fast=True,
                on_submit_success=lambda request, execution_id, _i, _t: (
                    session.batch.record_execution(request.scope_id, execution_id)
                ),
                on_submit_error=on_failure,
                on_wait_start=on_wait_start,
                on_wait_success=on_wait_success,
                on_wait_error=on_failure,
            ),
        )

    def _policy(self, client, *, fail_fast: bool, **callbacks):
        return CallbackBatchSubmitWaitPolicy(
            submit_fn=lambda request: self._submit(client, request),
            wait_fn=lambda execution_id, request: self._wait(
                client, execution_id, request
            ),
            job_key_fn=lambda request: request.scope_id,
            fail_fast_submit_value=fail_fast,
            fail_fast_wait_value=fail_fast,
            **{f"{name}_fn": callback for name, callback in callbacks.items()},
        )

    async def _submit(self, client, request: DatasetPipelineRequest) -> str:
        self._session.set_compiled(request.scope_id, None)
        return await submit_compile(client, request)

    async def _wait(self, client, execution_id: str, request: DatasetPipelineRequest) -> None:
        try:
            inspection = await wait_for_compile(
                client,
                execution_id=execution_id,
                scope_id=request.scope_id,
            )
        finally:
            self._session.progress_tracker.clear_execution(execution_id)
        self._session.set_compiled(
            request.scope_id,
            CompiledDataset(
                compile_artifact_id=execution_id,
                steps=tuple(request.steps),
                inspection=inspection,
            ),
        )

    def _compile_failed(self, scope_id: str, error: Exception) -> None:
        logger.error("COMPILATION ERROR: %s: %s", scope_id, error, exc_info=True)
        session = self._session
        session.clear_compile_pending((scope_id,))
        session.set_dataset_state(scope_id, OrchestratorState.COMPILE_FAILED)
        session.publish(
            CompilationFailed(scope_id, session.dataset_name(scope_id), str(error))
        )
