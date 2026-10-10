"""Bounded source journey through the existing MCP and endpoint status owners."""

import asyncio
import threading
from types import SimpleNamespace

import pytest
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    DescribeFunctionCapability,
    GenerateSyntheticPlateCapability,
    InspectPlatePathCapability,
    ProgressAcknowledgedCapability,
    SearchFunctionsCapability,
    SubmitCompileCapability,
    SubmitPipelineExecutionCapability,
)
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.functions import (
    FunctionCatalogControlResponse,
    FunctionCatalogPage,
    FunctionCatalogPreparationControlResponse,
)
from openhcs.agent.services.endpoint_function_catalog_service import (
    ZMQFunctionCatalogService,
)
from openhcs.mcp.server import _await_with_declared_progress, build_server
from openhcs.mcp.dev_client_core import DEFAULT_CALL_TIMEOUT_SECONDS
from openhcs.runtime.zmq_config import OpenHCSZMQConfig
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient


class RecordingContext:
    request_context = object()

    def __init__(self):
        self.messages = []
        self.preparing = asyncio.Event()
        self.heartbeat = asyncio.Event()

    async def report_progress(self, progress, total=None, message=None):
        self.messages.append((progress, message))
        if "Preparing exact child" in message:
            self.preparing.set()
        if "still running" in message:
            self.heartbeat.set()


@pytest.mark.parametrize(
    "declaration",
    (
        GenerateSyntheticPlateCapability,
        InspectPlatePathCapability,
        SubmitCompileCapability,
        SubmitPipelineExecutionCapability,
    ),
)
def test_submission_leaf_declares_existing_worker_progress(declaration):
    spec = declaration
    assert 0 < spec.progress_heartbeat_seconds < DEFAULT_CALL_TIMEOUT_SECONDS
    assert spec.progress_worker_thread_safe is True
    assert issubclass(declaration, ProgressAcknowledgedCapability)
    assert "progress_heartbeat_seconds" not in declaration.__dict__


def test_reused_client_reports_actual_phase_before_heartbeat_and_retains_ui_callback():
    ui = []
    client = ZMQExecutionClient(port=5555, connection_status_callback=ui.append)
    capability = SimpleNamespace(
        title=SearchFunctionsCapability.title, progress_heartbeat_seconds=0.02
    )

    async def exercise():
        context = RecordingContext()

        async def operation():
            await asyncio.to_thread(
                client._emit_connection_status,
                EndpointStartupPhase.PREPARING_CAPABILITIES,
                "Preparing exact child",
            )
            # No wall-clock stall: require delivery before releasing preparation.
            await asyncio.wait_for(context.preparing.wait(), timeout=0.2)
            await context.heartbeat.wait()
            client._emit_connection_status(
                EndpointStartupPhase.CONNECTED, "Typed PONG ready"
            )
            return client

        result = await _await_with_declared_progress(capability, context, operation())
        return result, context

    result, context = asyncio.run(exercise())
    assert result is client
    assert len(ui) == 2
    assert "preparing_capabilities: Preparing exact child" in context.messages[1][1]
    assert "Preparing exact child" in context.messages[2][1]
    assert "still running" in context.messages[2][1]
    assert "connected: Typed PONG ready" in context.messages[-1][1]
    assert [progress for progress, _ in context.messages] == sorted(
        progress for progress, _ in context.messages
    )


@pytest.mark.parametrize(
    "error_type", (TimeoutError, ValueError, asyncio.CancelledError)
)
def test_terminal_operation_preserves_error_and_flushes_original_status(error_type):
    client = ZMQExecutionClient(port=5555)
    error = error_type("Original terminal observation")

    async def exercise():
        context = RecordingContext()

        async def operation():
            client._emit_connection_status(
                EndpointStartupPhase.FAILED, "Exact child failed"
            )
            raise error

        with pytest.raises(error_type) as caught:
            await _await_with_declared_progress(
                SearchFunctionsCapability, context, operation()
            )
        assert caught.value is error
        assert "failed: Exact child failed" in context.messages[-1][1]
        client._emit_connection_status(
            EndpointStartupPhase.DISCONNECTED, "After request"
        )
        await asyncio.sleep(0)
        assert "After request" not in str(context.messages)

    asyncio.run(exercise())


def test_catalog_family_inherits_progress_without_search_leaf_repetition():
    assert (
        DescribeFunctionCapability.progress_heartbeat_seconds
        == ProgressAcknowledgedCapability.progress_heartbeat_seconds
    )
    assert "progress_heartbeat_seconds" not in SearchFunctionsCapability.__dict__


def test_registered_catalog_tool_routes_original_pending_control_statuses_without_native_launch():
    """Real generated binding/service/client loop; only native I/O is synthetic."""
    ui, requests, workers = [], [], []
    page = FunctionCatalogPage(SCHEMA_VERSION, "synthetic-revision", (), 0, 50)
    ready = threading.Event()
    pending = FunctionCatalogPreparationControlResponse(
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            "Preparing exact child",
            sequence=1,
        ),
        retry_after_seconds=0.01,
    )

    class SyntheticControlClient(ZMQExecutionClient):
        def is_connected(self):
            return True

        def _send_control_request(self, request, **kwargs):
            workers.append(threading.get_ident())
            requests.append(request)
            return (
                FunctionCatalogControlResponse(page).to_control_response()
                if ready.is_set()
                else pending.to_control_response()
            )

        def _spawn_server_process(self):
            raise AssertionError("Source journey must never launch native")

    client = SyntheticControlClient(port=5555, connection_status_callback=ui.append)
    service = ZMQFunctionCatalogService(
        lambda: OpenHCSZMQConfig(default_port=5555),
        client_factory=lambda config: client,
    )
    built = build_server(SimpleNamespace(function_catalog=service))

    async def exercise():
        context = RecordingContext()
        tool = built._tool_manager.get_tool("openhcs_search_functions")
        task = asyncio.create_task(tool.fn(mcp_context=context, query="source-only"))
        try:
            preparation = asyncio.create_task(context.preparing.wait())
            completed, _ = await asyncio.wait({preparation, task}, timeout=0.5)
            assert preparation in completed, (
                context.messages,
                task.result() if task.done() else "still pending",
                [(status.phase, status.message) for status in ui],
            )
            assert not task.done(), "Preparing is not a ready result"
            ready.set()
            result = await task
            return result, context
        finally:
            ready.set()
            preparation.cancel()
            await asyncio.gather(preparation, return_exceptions=True)
            if not task.done():
                task.cancel()
                await asyncio.gather(task, return_exceptions=True)

    result, context = asyncio.run(exercise())
    assert result["revision"] == page.revision
    assert result["items"] == []
    assert len(requests) >= 2
    assert all(worker != threading.get_ident() for worker in workers)
    assert [status.phase for status in ui] == [
        EndpointStartupPhase.PREPARING_CAPABILITIES,
        EndpointStartupPhase.CONNECTED,
    ]
    assert "preparing_capabilities: Preparing exact child" in context.messages[1][1]
    assert "connected: Function catalog is ready" in context.messages[-1][1]


def test_cancelled_progress_await_drops_late_worker_callbacks_and_restores_scope():
    client = ZMQExecutionClient(port=5555)
    worker_started, worker_release = threading.Event(), threading.Event()

    def worker():
        worker_started.set()
        assert worker_release.wait(1.0)
        client._emit_connection_status(
            EndpointStartupPhase.FAILED, "Late worker status"
        )

    async def exercise():
        context = RecordingContext()
        task = asyncio.create_task(
            _await_with_declared_progress(
                SearchFunctionsCapability, context, asyncio.to_thread(worker)
            )
        )
        try:
            while not worker_started.is_set():
                await asyncio.sleep(0)
            task.cancel()
            with pytest.raises(asyncio.CancelledError):
                await task
            worker_release.set()
        finally:
            worker_release.set()
        # Loop shutdown joins the original executor worker; no process kill.
        return context

    context = asyncio.run(exercise())
    assert len(context.messages) == 1
    assert "Late worker status" not in str(context.messages)


def test_concurrent_mcp_requests_share_one_client_without_cross_talk():
    ui = []
    client = ZMQExecutionClient(port=5555, connection_status_callback=ui.append)

    async def request(label):
        context = RecordingContext()

        async def operation():
            await asyncio.to_thread(
                client._emit_connection_status,
                EndpointStartupPhase.PREPARING_CAPABILITIES,
                f"Preparing exact child {label}",
            )
            await asyncio.wait_for(context.preparing.wait(), 0.2)
            return label

        result = await _await_with_declared_progress(
            SearchFunctionsCapability, context, operation()
        )
        return result, context.messages

    async def exercise():
        return await asyncio.gather(request("left"), request("right"))

    left, right = asyncio.run(exercise())
    assert left[0] == "left" and right[0] == "right"
    assert len(ui) == 2
    assert "left" in left[1][-1][1] and "right" not in str(left[1])
    assert "right" in right[1][-1][1] and "left" not in str(right[1])


def test_new_catalog_declarations_and_cooperative_hooks_use_unchanged_generated_consumer():
    """Only declarations change; the existing registry generates both tools."""
    client = ZMQExecutionClient(port=5555)
    page = FunctionCatalogPage(SCHEMA_VERSION, "new-case", (), 0, 50)

    class InvocationAudit:
        """Cooperative invocation hook composed over the declared shape."""

        __slots__ = ()

        def invoke(self, declaration, binder, arguments):
            binder.context.audit.append(declaration.name)
            return super().invoke(declaration, binder, arguments)

    base_invocation = SearchFunctionsCapability.invocation
    audited_type = type(
        "AuditedSearchInvocation",
        (InvocationAudit, type(base_invocation)),
        {"__slots__": ()},
    )

    class NewBefore(SearchFunctionsCapability):
        name = "openhcs_source_feedback_before"
        cli_command = None
        invocation = audited_type(
            service=base_invocation.service, method=base_invocation.method
        )

    class NewAfter(SearchFunctionsCapability):
        name = "openhcs_source_feedback_after"
        cli_command = None

    class Catalog:
        def search(self, **kwargs):
            client._emit_connection_status(
                EndpointStartupPhase.PREPARING_CAPABILITIES, "New declaration feedback"
            )
            return page

    context = SimpleNamespace(function_catalog=Catalog(), audit=[])
    try:
        built = build_server(context)

        async def exercise():
            for declaration in (NewBefore, NewAfter):
                progress = RecordingContext()
                tool = built._tool_manager.get_tool(declaration.name)
                result = await tool.fn(mcp_context=progress, query="new-case")
                assert result["revision"] == "new-case"
                assert "New declaration feedback" in progress.messages[-1][1]

        asyncio.run(exercise())
        assert context.audit == [NewBefore.name]
    finally:
        for declaration in (NewBefore, NewAfter):
            AgentCapabilityDeclaration.__registry__.pop(declaration.name)
