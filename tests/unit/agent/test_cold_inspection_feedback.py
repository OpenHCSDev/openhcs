"""Existing declaration, gateway and codec boundaries expose actual stages."""

from contextvars import ContextVar
import threading
from types import SimpleNamespace

import pytest
from zmqruntime.startup import EndpointStartupStatus

from openhcs.agent.capabilities import (
    MainThreadProgressCapability, QueryPlateFilesCapability, SamplePlateImageCapability,
    InspectPipelineSourceArtifactPlanCapability,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.config_service import ConfigService
from openhcs.agent.services.artifact_plan_inspection_service import (
    AgentProgressQueue, CompileInspectionGatewayABC, ArtifactPlanInspectionService,
)
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.core.progress import (
    ProgressEventPayload, ProgressIdentity, ProgressPhase, ProgressStatus, create_event,
)
from openhcs.mcp.execution import McpTransportExecutor
from openhcs.mcp.server import build_server

from tests.unit.agent.test_agent_services import _FakeCompileInspectionGateway
from tests.unit.agent.test_plate_inspection_service import ImageXpressPlateFixture


@pytest.mark.parametrize("declaration", (QueryPlateFilesCapability, SamplePlateImageCapability))
def test_physical_reader_declarations_inherit_original_affine_progress(declaration):
    assert issubclass(declaration, MainThreadProgressCapability)
    assert declaration.progress_heartbeat_seconds == 1.0
    assert declaration.progress_worker_thread_safe is False
    assert "progress_worker_thread_safe" not in declaration.__dict__


def test_original_progress_codec_is_the_only_event_store_and_rejects_bad_enum():
    queue = AgentProgressQueue()
    event = create_event(ProgressEventPayload(
        identity=ProgressIdentity("inspection", "/source", "A01", "new-declared-step"),
        phase=ProgressPhase.COMPILE, status=ProgressStatus.RUNNING, percent=25,
        completed=1, total=4,
    ))
    statuses = []
    with EndpointStartupStatus.callback_scope(statuses.append):
        queue.put(event.to_dict())
        invalid = event.to_dict()
        invalid["phase"] = "not-a-declared-phase"
        with pytest.raises(ValueError, match="Invalid phase"):
            queue.put(invalid)
        with pytest.raises(KeyError):
            queue.put({"phase": "compile", "status": "running"})
    assert queue.events == [event]
    assert len(statuses) == 1
    assert statuses[0].message == "compile: running: A01: new-declared-step: 1/4"


@pytest.mark.parametrize("fails", (False, True))
def test_new_gateway_hook_cooperates_in_both_mros_before_terminal_result(tmp_path, fails):
    """Independent audit capability needs no edits to service or MCP consumers."""
    identity = ContextVar("cold-feedback-request", default="outside")
    calls, messages = [], []
    compile_entered = threading.Event()
    release = threading.Event()
    error = ValueError("original declared compiler error")

    class AuditGateway(CompileInspectionGatewayABC):
        def compile(self, request):
            calls.append(("enter", identity.get()))
            result = super().compile(request)
            calls.append(("exit", identity.get()))
            return result

    class DeclaredGateway(_FakeCompileInspectionGateway):
        def _compile(self, request):
            assert threading.current_thread() is threading.main_thread()
            compile_entered.set()
            self.emit_progress(request)
            assert release.wait(3), "Actual stage relay was not delivered during held work"
            if fails:
                raise error
            return super()._compile(request)

    class Before(AuditGateway, DeclaredGateway):
        pass

    class After(DeclaredGateway, AuditGateway):
        pass

    class StageContext:
        request_context = object()

        async def report_progress(self, progress, total=None, message=None):
            assert threading.current_thread() is not threading.main_thread()
            messages.append(message)
            if "compile: running: A01: compilation" in message:
                assert compile_entered.is_set()
                release.set()

    executor = McpTransportExecutor()
    config = ConfigService()
    try:
        for gateway_type in (Before, After):
            release.clear()
            compile_entered.clear()
            gateway = gateway_type()
            service = ArtifactPlanInspectionService(
                path_policy=AgentPathPolicy.with_roots(
                    readable_roots=(tmp_path,), writable_roots=(tmp_path,),
                ),
                config_service=config, compile_inspection_gateway=gateway,
            )
            built = build_server(SimpleNamespace(artifact_plan_service=service),
                                 main_thread_dispatcher=executor.dispatcher)
            tool = built._tool_manager.get_tool(InspectPipelineSourceArtifactPlanCapability.name)

            async def exercise():
                token = identity.set("original-request")
                try:
                    return await tool.fn(mcp_context=StageContext(), plate_path=str(tmp_path),
                                         pipeline_source="pipeline_steps = []")
                finally:
                    identity.reset(token)

            before = len(messages)
            result = executor.run(exercise)
            observed = messages[before:]
            assert any("Preparing source inspection compiler" in item for item in observed)
            if fails:
                assert result["errors"][0]["exception_type"] == "ValueError"
                assert result["errors"][0]["message"] == str(error)
                assert any("Source inspection compiler failed" in item for item in observed)
                assert not any("projection completed" in item for item in observed)
            else:
                assert result["errors"] == []
                assert any("projection completed" in item for item in observed)
        expected = ["enter"] * 2 if fails else ["enter", "exit"] * 2
        assert calls == [(stage, "original-request") for stage in expected]
        assert identity.get() == "outside"
    finally:
        release.set()
        executor.close()


def test_real_inventory_binding_relays_shared_reader_preparation(tmp_path):
    plate = ImageXpressPlateFixture.write(tmp_path)
    service = PlateInspectionService(AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,), writable_roots=(),
    ))
    messages = []

    class StageContext:
        request_context = object()

        async def report_progress(self, progress, total=None, message=None):
            assert threading.current_thread() is not threading.main_thread()
            messages.append(message)

    executor = McpTransportExecutor()
    built = build_server(SimpleNamespace(plate_inspection_service=service),
                         main_thread_dispatcher=executor.dispatcher)
    tool = built._tool_manager.get_tool(QueryPlateFilesCapability.name)

    async def exercise():
        return await tool.fn(mcp_context=StageContext(), plate_path=str(plate),
                             source_format="imagexpress", include_previews=False)

    try:
        result = executor.run(exercise)
        assert result["errors"] == [], result
        assert result["total_count"] == 2
        assert any("Preparing physical microscope handler" in item for item in messages)
        assert any("Physical microscope handler ready" in item for item in messages)
        assert any("Reading plate file inventory" in item for item in messages)
    finally:
        executor.close()
