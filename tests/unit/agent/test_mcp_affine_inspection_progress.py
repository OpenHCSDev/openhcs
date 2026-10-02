"""Real generated bindings retain main affinity while SDK progress stays live."""

import asyncio
from contextvars import ContextVar
import threading
import time
from types import SimpleNamespace

from PyQt6.QtCore import QCoreApplication, QThread
import pytest
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    CreateOrchestratorSessionFromPipelineSourceCapability,
    InspectPipelineSourceArtifactPlanCapability,
    MainThreadProgressCapability,
)
from openhcs.agent.dto.common import AgentError, SCHEMA_VERSION
from openhcs.agent.dto.execution import ArtifactPlanInspection
from openhcs.mcp.execution import McpMainThreadDispatcher, McpTransportExecutor
from pyqt_reactive.services.ui_thread_dispatch import (
    UiThreadDispatchError, UiThreadDispatcherClosedError, UiThreadDispatchTimeoutError,
)
from openhcs.mcp.server import build_server
from openhcs.serialization.json import to_jsonable


@pytest.mark.parametrize("declaration", (
    InspectPipelineSourceArtifactPlanCapability,
    CreateOrchestratorSessionFromPipelineSourceCapability,
))
def test_source_leaf_composes_original_progress_and_affinity(declaration):
    assert issubclass(declaration, MainThreadProgressCapability)
    spec = declaration.to_spec()
    assert spec.progress_heartbeat_seconds == 1.0
    assert spec.progress_worker_thread_safe is False
    assert "progress_heartbeat_seconds" not in declaration.__dict__
    assert "progress_worker_thread_safe" not in declaration.__dict__


class AffineInspectionService:
    """Only compilation is synthetic; declaration, binding and relay are real."""

    def __init__(self, request_identity, *, error=None):
        self.release = threading.Event()
        self.request_identity = request_identity
        self.error = error
        self.calls = []

    def inspect_pipeline_source_artifact_plan_request(self, request):
        assert threading.current_thread() is threading.main_thread()
        assert QThread.currentThread() == QCoreApplication.instance().thread()
        self.calls.append((request, self.request_identity.get()))
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            "Source inspection on original main thread",
        ).publish()
        assert self.wait_for_completion(), "SDK heartbeat was starved by main-affine work"
        if self.error is not None:
            raise self.error
        return ArtifactPlanInspection(
            schema_version=SCHEMA_VERSION, plate_path=request.plate_path
        )

    def wait_for_completion(self):
        return self.release.wait(3)


class InspectionProgressContext:
    request_context = object()

    def __init__(self, service):
        self.service = service
        self.messages = []

    async def report_progress(self, progress, total=None, message=None):
        assert threading.current_thread() is not threading.main_thread()
        self.messages.append(message)
        if "still running" in message:
            self.service.release.set()


@pytest.mark.parametrize("error", (None, ValueError("original"), asyncio.CancelledError("original")))
def test_generated_inspection_main_thread_context_progress_and_terminal(error):
    identity = ContextVar("affine-inspection-identity", default="outside")
    service = AffineInspectionService(identity, error=error)
    executor = McpTransportExecutor()
    built = build_server(
        SimpleNamespace(execution_service=service),
        main_thread_dispatcher=executor.dispatcher,
    )
    tool = built._tool_manager.get_tool(InspectPipelineSourceArtifactPlanCapability.name)
    context = InspectionProgressContext(service)

    async def exercise():
        token = identity.set("original-request")
        try:
            if isinstance(error, asyncio.CancelledError):
                with pytest.raises(asyncio.CancelledError) as caught:
                    await tool.fn(mcp_context=context, plate_path="/synthetic", pipeline_source="pipeline_steps = []")
                assert caught.value is error
                return None
            return await tool.fn(mcp_context=context, plate_path="/synthetic", pipeline_source="pipeline_steps = []")
        finally:
            identity.reset(token)

    try:
        result = executor.run(exercise)
    finally:
        executor.close()
    assert len(service.calls) == 1
    assert service.calls[0][1] == "original-request"
    assert identity.get() == "outside"
    assert any("Source inspection on original main thread" in message for message in context.messages)
    assert any("still running" in message for message in context.messages)
    if error is None:
        assert result["plate_path"] == "/synthetic"
        assert result["errors"] == []
    elif isinstance(error, ValueError):
        assert result["errors"] == [to_jsonable(AgentError.from_exception(
            "mcp_tool_failed", error,
            hint="The MCP server caught this exception at the tool boundary.",
        ))]


def test_independent_new_leaf_cooperative_hooks_need_no_consumer_edits():
    calls = []

    class AuditCapability(AgentCapabilityDeclaration):
        @classmethod
        def execute_request(cls, context, request):
            calls.append(("audit-enter", cls.name))
            result = super().execute_request(context, request)
            calls.append(("audit-exit", cls.name))
            return result

    class NewBefore(AuditCapability, InspectPipelineSourceArtifactPlanCapability):
        name = "openhcs_affine_inspection_before"
        cli_command = None

    class NewAfter(InspectPipelineSourceArtifactPlanCapability, AuditCapability):
        name = "openhcs_affine_inspection_after"
        cli_command = None

    identity = ContextVar("new-affine-declaration", default="new-case")
    service = AffineInspectionService(identity)
    executor = McpTransportExecutor()
    built = build_server(SimpleNamespace(execution_service=service), main_thread_dispatcher=executor.dispatcher)

    async def exercise():
        for declaration in (NewBefore, NewAfter):
            service.release.clear()
            context = InspectionProgressContext(service)
            tool = built._tool_manager.get_tool(declaration.name)
            result = await tool.fn(mcp_context=context, plate_path="/new-case", pipeline_source="pipeline_steps = []")
            assert result["plate_path"] == "/new-case"
            assert any("still running" in message for message in context.messages)

    try:
        executor.run(exercise)
        assert calls == [(stage, declaration.name) for declaration in (NewBefore, NewAfter) for stage in ("audit-enter", "audit-exit")]
        assert len(service.calls) == 2
    finally:
        executor.close()
        for declaration in (NewBefore, NewAfter):
            AgentCapabilityDeclaration.__registry__.pop(declaration.name)


def test_started_dispatch_waits_authoritative_completion_beyond_prestart_limit():
    executor = McpTransportExecutor()
    calls = []

    def work():
        calls.append(threading.get_ident())
        time.sleep(0.04)
        return "one-completion"

    async def exercise():
        return await asyncio.to_thread(executor.dispatcher.call, work, timeout_ms=1)

    try:
        assert executor.run(exercise) == "one-completion"
        assert calls == [threading.get_ident()]
    finally:
        executor.close()


def test_not_started_dispatch_is_cancelled_without_invoking_callback():
    executor = McpTransportExecutor()
    entered, second_finished = threading.Event(), threading.Event()
    calls = []

    def first():
        calls.append("first")
        entered.set()
        assert second_finished.wait(1)

    async def exercise():
        task = asyncio.create_task(executor.dispatcher.invoke(first))
        assert await asyncio.to_thread(entered.wait, 1)
        try:
            with pytest.raises(UiThreadDispatchTimeoutError):
                await asyncio.to_thread(executor.dispatcher.call, lambda: calls.append("forbidden"), timeout_ms=1)
        finally:
            second_finished.set()
        await task

    try:
        executor.run(exercise)
        assert calls == ["first"]
    finally:
        executor.close()


def test_closed_dispatcher_rejects_without_invocation():
    executor = McpTransportExecutor()
    calls = []
    executor.dispatcher.close()

    async def exercise():
        with pytest.raises(UiThreadDispatcherClosedError):
            await executor.dispatcher.invoke(lambda: calls.append("forbidden"))

    try:
        executor.run(exercise)
        assert calls == []
    finally:
        executor.close()


def test_headless_absence_does_not_authorize_worker_affinity(monkeypatch):
    monkeypatch.setattr(QCoreApplication, "instance", lambda: None)
    dispatcher = McpMainThreadDispatcher()
    calls = []

    async def exercise():
        with pytest.raises(UiThreadDispatchError, match="No Qt application"):
            await asyncio.to_thread(dispatcher.call, lambda: calls.append("forbidden"))

    try:
        asyncio.run(exercise())
        assert calls == []
        assert dispatcher.call(lambda: "original-main") == "original-main"
    finally:
        dispatcher.close()


def test_transport_rejects_worker_start_without_affinity_claim():
    async def exercise():
        with pytest.raises(RuntimeError, match="process main thread"):
            await asyncio.to_thread(McpTransportExecutor)

    asyncio.run(exercise())


def test_async_cancellation_after_start_retains_exactly_one_owned_callback():
    executor = McpTransportExecutor()
    entered, release, finished = threading.Event(), threading.Event(), threading.Event()
    calls = []

    def work():
        calls.append("started")
        entered.set()
        assert release.wait(1)
        calls.append("finished")
        finished.set()

    async def exercise():
        task = asyncio.create_task(executor.dispatcher.invoke(work))
        assert await asyncio.to_thread(entered.wait, 1)
        task.cancel()
        with pytest.raises(asyncio.CancelledError):
            await task
        release.set()
        assert await asyncio.to_thread(finished.wait, 1)

    try:
        executor.run(exercise)
        assert calls == ["started", "finished"]
    finally:
        release.set()
        executor.close()


class WireInspectionService(AffineInspectionService):
    """Bound only synthetic work; never replace transport or progress owners."""

    def wait_for_completion(self):
        time.sleep(2.4)
        return True

    def inspect_pipeline_source_artifact_plan_request(self, request):
        self.error = ValueError("Original controlled source error") if request.pipeline_source == "failed" else None
        return super().inspect_pipeline_source_artifact_plan_request(request)


def serve_stdio_inspection_fixture():
    from openhcs.mcp.stdio import McpStdioTransport

    identity = ContextVar("wire-source-identity", default="wire")
    with McpStdioTransport.reserve_process_stdio() as transport:
        transport.run(build_server(
            SimpleNamespace(execution_service=WireInspectionService(identity)),
            main_thread_dispatcher=transport.execution.dispatcher,
        ))


def test_resident_continuous_connections_keep_affinity_and_wire_progress(tmp_path):
    from pyqt_reactive.services.async_operation_executor import AsyncOperationExecutor
    from openhcs.mcp.dev_client_core import McpDevServerSpec, McpDevSocketSession
    from openhcs.mcp.socket import McpSocketTransport, wait_for_socket
    import io
    import sys

    transport = McpSocketTransport(tmp_path / "affine.sock")
    service = WireInspectionService(ContextVar("resident-source-identity", default="resident"))
    built = build_server(SimpleNamespace(execution_service=service), main_thread_dispatcher=transport.execution.dispatcher)
    clients = AsyncOperationExecutor(max_workers=1)
    diagnostics = io.StringIO()

    async def exercise():
        assert await asyncio.to_thread(wait_for_socket, transport.socket_path, timeout_seconds=10)
        try:
            for connection in range(2):
                async with McpDevSocketSession(McpDevServerSpec(sys.executable), diagnostics, transport.socket_path) as session:
                    await session.initialize(timeout_seconds=10)
                    for source in ("cold", "failed"):
                        result = await session.call_tool(
                            InspectPipelineSourceArtifactPlanCapability.name,
                            {"plate_path": "/synthetic", "pipeline_source": source},
                            timeout_seconds=1.6,
                        )
                        payload = result["structuredContent"]
                        if source == "failed":
                            assert payload["errors"][0]["message"] == "Original controlled source error"
                        else:
                            assert payload["plate_path"] == "/synthetic"
                            assert payload["errors"] == []
        finally:
            transport._stop.set()
            if transport._listener is not None:
                transport._listener.close()

    future = clients.submit(exercise)
    try:
        transport.serve(built)
        future.result()
        assert len(service.calls) == 4
        assert "still running" in diagnostics.getvalue()
        assert "Source inspection on original main thread" in diagnostics.getvalue()
    finally:
        clients.close()
