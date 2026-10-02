"""Real generated bindings retain main affinity while SDK progress stays live."""

import asyncio
from contextvars import ContextVar
import threading
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
from openhcs.mcp.execution import McpTransportExecutor
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
        assert self.release.wait(3), "SDK heartbeat was starved by main-affine work"
        if self.error is not None:
            raise self.error
        return ArtifactPlanInspection(
            schema_version=SCHEMA_VERSION, plate_path=request.plate_path
        )


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
