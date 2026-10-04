"""Keep MCP I/O responsive without moving main-thread-owned application work."""

from __future__ import annotations

import asyncio
from collections.abc import Callable, Coroutine
from concurrent.futures import Future
from contextvars import copy_context
import threading
from typing import Any, ParamSpec, TypeVar

from PyQt6.QtCore import QCoreApplication, QEventLoop, QThread
from polystore import cleanup_backend_connections
from pyqt_reactive.core.future_completion import FutureCompletion
from pyqt_reactive.services.async_operation_executor import AsyncOperationExecutor
from pyqt_reactive.services.ui_thread_dispatch import (
    UiThreadDispatcher,
    UiThreadDispatchTimeoutError,
)

from openhcs.agent.exceptions import AgentFacingErrorMixin

ParametersT = ParamSpec("ParametersT")
ResultT = TypeVar("ResultT")


class McpQueuedCallNotStartedError(AgentFacingErrorMixin, UiThreadDispatchTimeoutError):
    """Original dispatch owner cancelled this callback before it began."""

    agent_error_code = "mcp_call_not_started"
    agent_error_hint = (
        "The Qt dispatcher cancelled this queued callback before invocation. "
        "This call did not execute; it created no runtime process or handle. "
        "This is not an uncertain started operation. Preserve its failed receipt "
        "and resolve the occupied main-thread work before a separate new attempt."
    )


class McpMainThreadDispatcher(UiThreadDispatcher):
    """Extend the original Qt dispatch owner with request-context propagation.

    ObjectState operations also require the process main thread in a headless
    server. Absence of a Qt application must not authorize a worker thread.
    """

    @staticmethod
    def _is_ui_thread() -> bool:
        return (
            threading.current_thread() is threading.main_thread()
            and UiThreadDispatcher._is_ui_thread()
        )

    def call(
        self, callback: Callable[[], ResultT], *, timeout_ms: int = 5000
    ) -> ResultT:
        request_context = copy_context()
        try:
            return super().call(
                lambda: request_context.run(callback), timeout_ms=timeout_ms
            )
        except UiThreadDispatchTimeoutError as error:
            # The original owner raises only after cancel() wins before start;
            # a started call waits its real completion instead. No process probe,
            # second dispatch clock, or retry decision belongs to this boundary.
            raise McpQueuedCallNotStartedError(str(error)) from error

    async def invoke(self, callback: Callable[[], ResultT]) -> ResultT:
        """Await the original affine call without blocking SDK notifications."""
        if self._is_ui_thread():
            return self.call(callback)
        return await asyncio.to_thread(self.call, callback)


class McpTransportExecutor(AsyncOperationExecutor):
    """Run the SDK loop off-main while the original Qt dispatcher owns calls.

    QCoreApplication supplies only an event dispatcher, not a GUI or native
    execution server. Compiler, catalog and kernel placement remain unchanged.
    """

    def __init__(self) -> None:
        if threading.current_thread() is not threading.main_thread():
            raise RuntimeError("MCP transport must be started on the process main thread.")
        self._application = QCoreApplication.instance() or QCoreApplication([])
        if QThread.currentThread() != self._application.thread():
            raise RuntimeError("MCP transport requires the Qt application main thread.")
        super().__init__(max_workers=1)
        self.dispatcher = McpMainThreadDispatcher()

    def run(
        self,
        operation: Callable[ParametersT, Coroutine[Any, Any, ResultT]],
        *args: ParametersT.args,
        **kwargs: ParametersT.kwargs,
    ) -> ResultT:
        """Join one transport using event-driven completion, not a new poller."""
        loop = QEventLoop()
        future = self.submit(operation, *args, **kwargs)

        def finished(completed: Future[ResultT]) -> None:
            loop.quit()

        completion = FutureCompletion(future, finished)
        if not future.done():
            loop.exec()
        # Keep the original completion relay alive through the event loop.
        del completion
        return future.result()

    def close(self) -> None:
        """Release process resources on their original main-thread owner.

        Both transports reach this boundary after their SDK operation finishes.
        PolyStore owns the lazy ImageJ context and registered resource cleanup;
        leaving it to interpreter finalization is not an MCP lifecycle.
        """
        if threading.current_thread() is not threading.main_thread():
            raise RuntimeError("MCP transport must be closed on the process main thread.")
        if self._closed:
            return
        try:
            self.dispatcher.close()
        finally:
            try:
                super().close()
            finally:
                cleanup_backend_connections(include_process_resources=True)
