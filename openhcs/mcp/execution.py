"""Keep MCP I/O responsive without moving main-thread-owned application work."""

from __future__ import annotations

import asyncio
from collections.abc import Callable, Coroutine
from contextvars import copy_context
import threading
from typing import Any, ParamSpec, TypeVar

from formbridge.services.async_operation_executor import AsyncOperationExecutor
from formbridge.services.main_thread_dispatch import (
    MainThreadDispatchTimeoutError,
    QueuedMainThreadDispatcher,
)
from polystore import cleanup_backend_connections

from openhcs.agent.exceptions import AgentFacingErrorMixin

ParametersT = ParamSpec("ParametersT")
ResultT = TypeVar("ResultT")


class McpQueuedCallNotStartedError(AgentFacingErrorMixin, MainThreadDispatchTimeoutError):
    """The dispatcher cancelled this callback before it began."""

    agent_error_code = "mcp_call_not_started"
    agent_error_hint = (
        "The main-thread dispatcher cancelled this queued callback before invocation. "
        "This call did not execute; it created no runtime process or handle. "
        "This is not an uncertain started operation. Preserve its failed receipt "
        "and resolve the occupied main-thread work before a separate new attempt."
    )


class McpMainThreadDispatcher(QueuedMainThreadDispatcher):
    """Run MCP application work on the process main thread with request context.

    ObjectState operations require the process main thread in a headless server,
    so the dispatcher must be built there.
    """

    def __init__(self) -> None:
        if threading.current_thread() is not threading.main_thread():
            raise RuntimeError("The MCP dispatcher must be built on the process main thread.")
        super().__init__()

    def call(
        self, callback: Callable[[], ResultT], *, timeout_ms: int = 5000
    ) -> ResultT:
        request_context = copy_context()
        return super().call(
            lambda: request_context.run(callback), timeout_ms=timeout_ms
        )

    @staticmethod
    def _dispatch_timeout_error() -> MainThreadDispatchTimeoutError:
        """Project only the dispatcher's successful cancellation.

        The dispatcher passes this error to its queued call's atomic cancel(). A
        callback's own exception, including a dispatch timeout after a side
        effect, remains the callback outcome and never passes through this hook.
        """
        return McpQueuedCallNotStartedError("Timed out waiting for main-thread dispatch.")

    async def invoke(self, callback: Callable[[], ResultT]) -> ResultT:
        """Await one main-thread call without blocking SDK notifications."""
        if self._is_owner_thread():
            return self.call(callback)
        return await asyncio.to_thread(self.call, callback)


class McpTransportExecutor(AsyncOperationExecutor):
    """Run the SDK loop off-main while the main thread serves dispatched calls."""

    def __init__(self) -> None:
        if threading.current_thread() is not threading.main_thread():
            raise RuntimeError("MCP transport must be started on the process main thread.")
        super().__init__(max_workers=1)
        self.dispatcher = McpMainThreadDispatcher()

    def run(
        self,
        operation: Callable[ParametersT, Coroutine[Any, Any, ResultT]],
        *args: ParametersT.args,
        **kwargs: ParametersT.kwargs,
    ) -> ResultT:
        """Serve main-thread calls until the transport operation finishes."""
        future = self.submit(operation, *args, **kwargs)
        self.dispatcher.run_until(future)
        return future.result()

    def close(self) -> None:
        """Release process resources on the main thread.

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
