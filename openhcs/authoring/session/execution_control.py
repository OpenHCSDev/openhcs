"""Stop a running batch, terminalize a failed one, and release the client."""

from __future__ import annotations

import logging
import threading
from typing import TYPE_CHECKING

from zmqruntime import EndpointShutdownMode
from zmqruntime.shutdown import EndpointShutdownService

from openhcs.authoring.session.events import ErrorReported
from openhcs.constants.constants import OrchestratorState
from openhcs.core.execution_state import (
    ManagerExecutionState,
    TerminalExecutionStatus,
)

if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session

logger = logging.getLogger(__name__)


class ExecutionControl:
    """Owns cancellation, failure terminalization and client teardown."""

    def __init__(self, session: "Session") -> None:
        self._session = session

    def _shutdown_service(self) -> EndpointShutdownService:
        config = self._session.client.config
        return EndpointShutdownService.for_endpoint(
            config,
            config.client_endpoint(config.default_port),
        )

    def check_all_completed(self) -> None:
        session = self._session
        if not session.execution_state.busy:
            return
        if not session.batch.all_batch_terminal():
            return
        completed, failed = session.batch.terminal_counts()
        session.main_thread.post(lambda: session.finish_batch(completed, failed))

    async def handle_execution_failure(self) -> None:
        session = self._session
        for scope_id in tuple(session.batch.active_plates):
            session.batch.mark_terminal(scope_id, TerminalExecutionStatus.FAILED)
            session.set_dataset_state(scope_id, OrchestratorState.EXEC_FAILED)
        session.execution_state = ManagerExecutionState.IDLE
        try:
            await session.client.disconnect()
        except Exception as error:
            logger.warning("Error disconnecting old client: %s", error)
        session.refresh()

    def stop(self, force: bool = False) -> None:
        session = self._session
        port = session.client.config.default_port
        shutdown_service = self._shutdown_service()

        def shut_down_server() -> None:
            try:
                result = shutdown_service.shutdown_ports(
                    ports=[port],
                    mode=EndpointShutdownMode.from_force(force),
                )
                if not result.succeeded:
                    if session.execution_state.suppresses_stop_failure:
                        logger.info(
                            "Suppressing stale stop failure while stop is already "
                            "terminalizing: %s",
                            result.failure_message,
                        )
                        self.cancel_active_datasets()
                        return
                    session.publish(ErrorReported(result.failure_message))
                    return
                self.cancel_active_datasets()
            except Exception as error:
                logger.error("Error stopping server: %s", error)
                session.publish(ErrorReported(f"Error stopping execution: {error}"))

        threading.Thread(target=shut_down_server, daemon=True).start()
        if force:
            self.cancel_active_datasets()
            threading.Thread(target=self.disconnect, daemon=True).start()

    def cancel_active_datasets(self) -> None:
        session = self._session
        for scope_id in session.batch.cancellable_plates():
            session.finish_dataset_execution(
                TerminalExecutionStatus.CANCELLED.completion_payload(
                    execution_id=session.batch.execution_id(scope_id),
                    execution_payload={},
                ),
                scope_id,
            )

    def disconnect(self) -> None:
        try:
            self._session.client.disconnect_sync()
        except Exception as error:
            logger.warning("Error disconnecting ZMQ client: %s", error)
