"""Asynchronous preparation lifecycle for an execution endpoint's catalog."""

from __future__ import annotations

import signal
import threading
import time
from collections.abc import Callable
from concurrent.futures import CancelledError, Future
from concurrent.futures import TimeoutError as FutureTimeoutError
from dataclasses import replace
from typing import TYPE_CHECKING

from threadpoolctl import threadpool_info
from zmqruntime import OperationCancellation
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

if TYPE_CHECKING:
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
    from openhcs.agent.dto.functions import (
        FunctionCatalogPreparationHandle,
        FunctionCatalogPreparationState,
    )
    from openhcs.agent.services.function_catalog_service import (
        FunctionCatalogServiceABC,
    )


class FunctionCatalogPreparation:
    """Own one lazily started endpoint catalog preparation operation."""

    @staticmethod
    def prepare_persistent_catalog(
        *, status_callback: Callable[[str], None] | None = None
    ) -> None:
        """Prepare registered kernels and metadata under owned-process cancellation."""

        from openhcs.processing.backends.lib_registry.registry_service import (
            RegistryService,
        )

        def cancel_preparation(_signal_number, _frame) -> None:
            raise CancelledError

        previous_handler = signal.signal(signal.SIGTERM, cancel_preparation)
        try:
            RegistryService.prepare_in_current_process(status_callback=status_callback)
        finally:
            signal.signal(signal.SIGTERM, previous_handler)

    def __init__(
        self,
        function_catalog: "FunctionCatalogServiceABC",
    ) -> None:
        self._lock = threading.RLock()
        self._future: Future[None] | None = None
        self._thread: threading.Thread | None = None
        self._cancellation = OperationCancellation()
        self._function_catalog = function_catalog
        self._snapshot = EndpointStartupStatus(
            sequence=0,
            phase=EndpointStartupPhase.PREPARING_CAPABILITIES,
            message="Function catalog has not been requested",
            timestamp=0.0,
        )

    def ensure_started(self) -> Future[None]:
        """Coalesce preparation of the current projections, not historical READY."""

        with self._lock:
            prepare = self._function_catalog.prepare
            if self._future is not None:
                if (
                    not self._future.done()
                    or self._future.cancelled()
                    or self._future.exception() is not None
                    or self._function_catalog.projections_current()
                ):
                    return self._future
                prepare = self._function_catalog.prepare_projections
            future = self._new_preparation_future()
            if future.cancelled():
                return future
            thread = threading.Thread(
                target=self._prepare,
                args=(future, prepare),
                name="openhcs-function-catalog-preparation",
                daemon=True,
            )
            self._thread = thread
            thread.start()
            return future

    def _new_preparation_future(self) -> Future[None]:
        """Create this owner's future while the caller holds its lifecycle lock."""
        future: Future[None] = Future()
        self._future = future
        if self._cancellation.requested():
            future.cancel()
        else:
            self._set_message("Starting function catalog preparation")
        return future

    def prepare_before_serving(
        self,
        status_callback: Callable[[EndpointStartupStatus], None] | None = None,
    ) -> None:
        """Warm in the server main thread before accepting endpoint requests."""
        with self._lock:
            future = self._new_preparation_future() if self._future is None else None
        if future is not None and not future.cancelled():
            if status_callback is not None:
                status_callback(self.snapshot())
            self._prepare(future, self._prepare_current_process, status_callback)
        self.wait_until_ready(status_callback)

    def _prepare_current_process(self, *, status_callback, cancellation) -> None:
        """Use the registry owner and project its already-prepared catalogue."""
        if cancellation.requested():
            raise CancelledError
        status_callback("Preparing registered callables in the execution server")
        self.prepare_persistent_catalog(status_callback=status_callback)
        if cancellation.requested():
            raise CancelledError
        self._function_catalog.prepare_projections(
            status_callback=status_callback,
            cancellation=cancellation,
        )

    def cancel_and_join(self) -> None:
        """Cancel and join the exact preparation operation owned here."""

        self._cancellation.cancel()
        with self._lock:
            thread = self._thread
        if thread is not None and thread is not threading.current_thread():
            thread.join()

    def wait_until_ready(
        self,
        status_callback: Callable[[EndpointStartupStatus], None] | None = None,
        *,
        observation_interval_seconds: float = 1.0,
    ) -> None:
        """Wait for the owned operation while projecting its latest status."""

        future = self.ensure_started()
        while not future.done():
            snapshot = self.snapshot()
            if status_callback is not None:
                status_callback(snapshot)
            try:
                future.result(timeout=observation_interval_seconds)
            except FutureTimeoutError:
                continue
        snapshot = self.snapshot()
        if status_callback is not None:
            status_callback(snapshot)
        future.result()

    def snapshot(self) -> EndpointStartupStatus:
        """Return the latest immutable preparation update."""

        with self._lock:
            return self._snapshot

    def start(
        self, connection: ExecutionConnectionSpec
    ) -> FunctionCatalogPreparationState:
        """Start/coalesce the existing future and return its responsive handle."""
        from zmqruntime.messages import ProcessIdentity

        from openhcs.agent.dto.functions import FunctionCatalogPreparationHandle

        connection.require_port("Function catalog preparation")
        handle = FunctionCatalogPreparationHandle(connection, ProcessIdentity.current())
        self.ensure_started()
        return self.observe(handle)

    def observe(
        self, handle: FunctionCatalogPreparationHandle
    ) -> FunctionCatalogPreparationState:
        """Project this future, never wait, restart or build another job store."""
        from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError
        from openhcs.agent.dto.functions import (
            FunctionCatalogPreparationOutcome as Outcome,
        )
        from openhcs.agent.dto.functions import (
            FunctionCatalogPreparationState,
        )

        handle.require_current_owner()
        errors = ()
        with self._lock:
            future, snapshot = self._future, self._snapshot
            if future is None:
                outcome = Outcome.NOT_STARTED
            elif future.cancelled():
                outcome = Outcome.CANCELLED
            elif not future.done():
                outcome = (
                    Outcome.CANCELLING
                    if self._cancellation.requested()
                    else Outcome.PENDING
                )
            elif (error := future.exception()) is not None:
                outcome = Outcome.FAILED
                errors = (
                    AgentError(
                        code="function_catalog_preparation_failed",
                        message=str(error),
                        exception_type=type(error).__name__,
                    ),
                )
            else:
                if self._function_catalog.projections_current():
                    outcome = Outcome.READY
                else:
                    outcome = Outcome.NOT_STARTED
                    snapshot = replace(
                        snapshot,
                        phase=EndpointStartupPhase.PREPARING_CAPABILITIES,
                        message="Current function catalog projections require preparation",
                    )
        return FunctionCatalogPreparationState(
            schema_version=SCHEMA_VERSION,
            handle=handle,
            outcome=outcome,
            progress=snapshot,
            errors=errors,
        )

    def cancel_preparation(
        self, handle: FunctionCatalogPreparationHandle
    ) -> FunctionCatalogPreparationState:
        """Signal the same owner promptly; its thread unwinds the supervised child."""
        handle.require_current_owner()
        self._cancellation.cancel()
        return self.observe(handle)

    def _set_message(
        self,
        message: str,
        *,
        phase: EndpointStartupPhase = EndpointStartupPhase.PREPARING_CAPABILITIES,
    ) -> None:
        with self._lock:
            self._snapshot = EndpointStartupStatus(
                sequence=self._snapshot.sequence + 1,
                phase=phase,
                message=message,
                timestamp=time.time(),
            )

    def _prepare(
        self,
        future: Future[None],
        prepare: Callable[..., None],
        observer: Callable[[EndpointStartupStatus], None] | None = None,
    ) -> None:
        """Complete this same future under either admitted preparation context."""

        def report(message: str) -> None:
            self._set_message(message)
            if observer is not None:
                observer(self.snapshot())

        try:
            prepare(
                status_callback=report,
                cancellation=self._cancellation,
            )
            if self._cancellation.requested():
                raise CancelledError
            threadpool_info()
            if self._cancellation.requested():
                raise CancelledError
        except CancelledError:
            self._set_message(
                "Function catalog preparation cancelled",
                phase=EndpointStartupPhase.FAILED,
            )
            future.cancel()
        except BaseException as error:
            self._set_message(str(error), phase=EndpointStartupPhase.FAILED)
            future.set_exception(error)
        else:
            self._set_message(
                "Function catalog ready", phase=EndpointStartupPhase.CONNECTED
            )
            future.set_result(None)
