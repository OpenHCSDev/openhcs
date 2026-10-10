"""Submit a compiled dataset for execution and follow it to its terminal status."""

from __future__ import annotations

import logging
import threading
from dataclasses import dataclass
from collections.abc import Callable
from typing import TYPE_CHECKING

from zmqruntime.execution import (
    CallbackExecutionStatusPollPolicy,
    ExecutionStatusPoller,
    ExecutionSubmissionResponse,
)
from zmqruntime.messages import MessageFields

from openhcs.authoring.session.compilation import (
    DatasetPipelineRequest,
    pipeline_fingerprint,
    run_blocking,
)
from openhcs.authoring.session.events import ErrorReported, StatusReported
from openhcs.core.execution_state import (
    TerminalExecutionStatus,
    parse_terminal_status,
)
from openhcs.core.debug import DebugExecutionConfig
from openhcs.core.orchestrator.orchestrator import OrchestratorState
from openhcs.runtime.zmq_execution_client import ZMQExecutionRequestBuilder
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams

if TYPE_CHECKING:
    from zmqruntime.messages import PongResponse

    from openhcs.authoring.session.session import Session


@dataclass(frozen=True, slots=True)
class SubmittedExecution:
    """What the session submitted for one ordinary execution."""

    scope_id: str
    request: ZMQExecutionRequestBuilder
    endpoint: "PongResponse | None"

logger = logging.getLogger(__name__)


class ExecutionSubmission:
    """Submits executions, records their ids and follows their status."""

    def __init__(self, session: "Session") -> None:
        self._session = session
        self._poller = ExecutionStatusPoller()

    async def submit_execution(
        self,
        request: DatasetPipelineRequest,
        *,
        compile_artifact_id: str,
        auxiliary_params: ZMQAuxiliaryExecutionParams | None,
    ) -> None:
        """Submit an ordinary execution and keep what was submitted, for evidence."""

        client = self._session.client.require_client()
        prepared = ZMQExecutionRequestBuilder.from_task(
            request.submission(
                compile_artifact_id=compile_artifact_id,
                auxiliary_params=auxiliary_params,
            )
        )
        execution_id = await self._submit(
            request,
            compile_artifact_id=compile_artifact_id,
            send=lambda: client.submit_prepared_pipeline(prepared),
            label="execution",
        )
        if execution_id is not None:
            self._session.submitted_executions[execution_id] = SubmittedExecution(
                scope_id=request.scope_id,
                request=prepared,
                endpoint=client.connected_endpoint,
            )

    async def submit_debug(
        self,
        request: DatasetPipelineRequest,
        *,
        compile_artifact_id: str,
        debug_config: DebugExecutionConfig,
    ) -> None:
        client = self._session.client.require_client()
        await self._submit(
            request,
            compile_artifact_id=compile_artifact_id,
            send=lambda: client.submit_debug_pipeline(
                request.submission(compile_artifact_id=compile_artifact_id),
                debug_config=debug_config,
            ),
            label="debug run",
        )

    async def _submit(
        self,
        request: DatasetPipelineRequest,
        *,
        compile_artifact_id: str,
        send: Callable[[], dict],
        label: str,
    ) -> str | None:
        session = self._session
        scope_id = request.scope_id
        logger.info(
            "Submit %s: dataset=%s execution_root=%s artifact_id=%s steps=%d "
            "fingerprint=%s",
            label,
            scope_id,
            request.execution_root,
            compile_artifact_id,
            len(request.steps),
            pipeline_fingerprint(request.steps),
        )
        response = ExecutionSubmissionResponse.from_wire(await run_blocking(send))
        if response.accepted:
            execution_id = response.require_execution_id(f"{label} submission")
            session.batch.record_execution(scope_id, execution_id)
            session.publish(StatusReported(f"Submitted {label} for {scope_id}"))
            self.follow(execution_id, scope_id)
            return execution_id

        error_text = response.require_failure_text(f"{label} submission")
        logger.error("%s submission failed for %s: %s", label, scope_id, error_text)
        session.publish(ErrorReported(f"Submission failed for {scope_id}: {error_text}"))
        session.batch.mark_terminal(scope_id, TerminalExecutionStatus.FAILED)
        session.set_dataset_state(scope_id, OrchestratorState.EXEC_FAILED)
        return None

    def follow(self, execution_id: str, scope_id: str) -> None:
        """Follow one execution on a background thread until it is terminal."""

        session = self._session

        class _ClientDisconnected(RuntimeError):
            pass

        def poll_status(polled_execution_id: str) -> dict:
            client = session.client.zmq_client
            if client is None:
                raise _ClientDisconnected("ZMQ client disconnected")
            return client.get_status(polled_execution_id)

        def current(execution: str) -> bool:
            current_id = session.batch.execution_id(scope_id)
            if current_id != execution:
                logger.info(
                    "Ignoring stale status for %s: execution_id=%s current=%s",
                    scope_id,
                    execution,
                    current_id,
                )
                return False
            return True

        def on_terminal(terminal_id: str, status: str, payload: dict) -> None:
            session.record_finished_execution(terminal_id, payload)
            if current(terminal_id):
                session.finish_dataset_execution(
                    parse_terminal_status(status).completion_payload(
                        execution_id=terminal_id,
                        execution_payload=payload,
                    ),
                    scope_id,
                )

        def on_status_error(error_id: str, message: str) -> None:
            if current(error_id):
                session.finish_dataset_execution(
                    TerminalExecutionStatus.FAILED.completion_payload(
                        execution_id=error_id,
                        execution_payload={MessageFields.ERROR: message},
                    ),
                    scope_id,
                )

        def on_poll_exception(_execution_id: str, error: Exception) -> bool:
            if isinstance(error, _ClientDisconnected):
                return False
            logger.warning("Error polling status for %s: %s", scope_id, error)
            return True

        policy = CallbackExecutionStatusPollPolicy(
            poll_status_fn=poll_status,
            poll_interval_seconds_value=0.5,
            on_running_fn=lambda _id, _payload: session.dataset_running(scope_id),
            on_terminal_fn=on_terminal,
            on_status_error_fn=on_status_error,
            on_poll_exception_fn=on_poll_exception,
        )

        def run() -> None:
            try:
                self._poller.run(execution_id, policy)
            except Exception as error:
                logger.error(
                    "Error following execution for %s: %s",
                    scope_id,
                    error,
                    exc_info=True,
                )
                session.publish(ErrorReported(f"{scope_id}: {error}"))

        threading.Thread(target=run, daemon=True).start()
