"""One staged field crosses the real generated binding and original compiler."""

from contextvars import ContextVar
from pathlib import Path
import threading
from types import SimpleNamespace

from PyQt6.QtCore import QCoreApplication, QThread

from openhcs.agent.capabilities import InspectPipelineSourceArtifactPlanCapability
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.config_service import ConfigService
from openhcs.agent.services.execution_session_service import (
    ExecutionSessionService, InProcessCompileInspectionGateway,
)
from openhcs.agent.services.function_catalog_service import FunctionCatalogService
from openhcs.agent.services.pipeline_authoring_service import PipelineAuthoringService
from openhcs.demo.synthetic_data import SyntheticMicroscopyGenerator
from openhcs.mcp.execution import McpTransportExecutor
from openhcs.mcp.server import build_server
from openhcs.processing.backends.lib_registry.registry_service import RegistryService


def test_real_generated_source_inspection_keeps_original_compiler_on_main(monkeypatch, tmp_path: Path):
    def forbidden_catalog(*args, **kwargs):
        raise AssertionError("Declared compilation must not prepare unrelated catalogs")

    monkeypatch.setattr(RegistryService, "get_all_functions_with_metadata", forbidden_catalog)
    plate = tmp_path / "staged-source"
    SyntheticMicroscopyGenerator(
        output_dir=str(plate), grid_size=(1, 1), tile_size=(64, 64),
        wavelengths=1, z_stack_levels=1, wells=["A01"], num_cells=3,
        random_seed=123, include_all_components=True,
    ).generate_dataset()
    # This is a declared-module source fixture, not a catalog-cold/render proof.
    # The installed cold canonical journey remains parent-owned.
    source = """from openhcs.core.config import PipelineConfig
from openhcs.core.steps.function_step import FunctionStep
from openhcs.processing.backends.cellprofiler.smoothing import reducenoise

pipeline_config = PipelineConfig(num_workers=1)
pipeline_steps = [FunctionStep(func=(reducenoise, {
    'patch_size': 3, 'patch_distance': 3, 'cutoff_distance': 0.1,
}), name='DeclaredNlm')]
"""
    identity = ContextVar("real-inspection-request", default="outside")
    calls, progress_threads = [], []

    class AffineCompileGateway(InProcessCompileInspectionGateway):
        def compile(self, request):
            assert threading.current_thread() is threading.main_thread()
            assert QThread.currentThread() == QCoreApplication.instance().thread()
            assert identity.get() == "exact-source-request"
            calls.append(request)
            return super().compile(request)

    class ProgressContext:
        request_context = object()

        async def report_progress(self, *args, **kwargs):
            assert threading.current_thread() is not threading.main_thread()
            progress_threads.append(threading.get_ident())

    config = ConfigService()
    service = ExecutionSessionService(
        path_policy=AgentPathPolicy.with_roots(readable_roots=(tmp_path,), writable_roots=(tmp_path,)),
        pipeline_service=PipelineAuthoringService(FunctionCatalogService(), config),
        config_service=config,
        compile_inspection_gateway=AffineCompileGateway(),
    )
    executor = McpTransportExecutor()
    built = build_server(SimpleNamespace(execution_service=service), main_thread_dispatcher=executor.dispatcher)
    tool = built._tool_manager.get_tool(InspectPipelineSourceArtifactPlanCapability.name)

    async def exercise():
        token = identity.set("exact-source-request")
        try:
            return await tool.fn(mcp_context=ProgressContext(), plate_path=str(plate), pipeline_source=source)
        finally:
            identity.reset(token)

    try:
        result = executor.run(exercise)
        assert result["errors"] == [], result
        assert result["axes"] == ["A01"]
        assert result["step_count"] == 1
        assert result["steps"][0]["step_name"] == "DeclaredNlm"
        assert result["source_workspace"]["file_count"] == 1
        assert len(calls) == 1 and progress_threads
        assert calls[0].pipeline_document.original_source == source
        assert identity.get() == "outside"
    finally:
        executor.close()
