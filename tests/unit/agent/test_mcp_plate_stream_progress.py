"""Real saved-ROI stream owners behind the generated affine MCP binding."""

import asyncio
from contextvars import ContextVar
from dataclasses import replace
import io
from pathlib import Path
import sys
import threading
import time

import pytest
from PyQt6.QtCore import QCoreApplication, QThread
from pyqt_reactive.services.async_operation_executor import AsyncOperationExecutor
from polystore.disk import DiskStorageBackend
from polystore.filemanager import FileManager
from polystore.roi import PointShape, ROI
from polystore.streaming.viewer_transport import ViewerStreamKwarg

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration, MainThreadProgressCapability,
    StreamPlateFilesToViewerCapability, UiStreamSelectedPlateFilesToViewerCapability,
)
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.mcp.dev_client_core import McpDevServerSpec, McpDevSocketSession
from openhcs.mcp.execution import McpTransportExecutor
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.mcp.server import build_server
from openhcs.mcp.socket import McpSocketTransport, wait_for_socket

from test_persisted_output_reopen import NoRuntimeBridge, declared_output
from tests.unit.test_streaming_service import FakeViewer


@pytest.fixture
def saved_roi_stream(tmp_path, monkeypatch):
    """Original writer/inventory/source/ROI algorithms; controlled receiver only."""
    inspection, declarations = declared_output(tmp_path / "source", ("synthetic_raw",))
    source_path, _pixels, projection, _declaration = declarations[0]
    result_root = tmp_path / "results"
    result_root.mkdir()
    archive = result_root / "not-an-acquisition.roi.zip"
    geometry = [ROI([PointShape(12.5, 8.25)], {"label": 7})]
    DiskStorageBackend().save(
        ROIArchiveSourceMetadata.bind(geometry, projection.image_metadata), archive,
    )
    persisted = ROIArchiveSourceMetadata.decode(DiskStorageBackend().load(archive))
    assert persisted.source_provenance == projection.image_metadata.source_provenance
    assert persisted.source_voxel_spacing == projection.image_metadata.source_voxel_spacing
    unsigned = result_root / "missing-source.roi.zip"
    DiskStorageBackend().save(geometry, unsigned)
    # Reuse the original path authority, explicitly adding this synthetic root.
    from openhcs.agent.path_policy import AgentPathPolicy
    from openhcs.agent.services.plate_inspection_service import PlateInspectionService
    inspection = PlateInspectionService(AgentPathPolicy.with_roots(
        readable_roots=(tmp_path,), writable_roots=(),
    ))
    viewer = FakeViewer()
    received = []
    timings = []
    identity = ContextVar("stream-request-identity", default="outside")

    def acquire(**fields):
        assert threading.current_thread() is threading.main_thread()
        assert QThread.currentThread() == QCoreApplication.instance().thread()
        assert fields["fresh"] is False and fields["ready_timeout"] == 30.0
        return viewer

    def receive(_manager, data, paths, backend, **fields):
        assert threading.current_thread() is threading.main_thread()
        assert backend == "napari_stream" and paths == [str(archive)]
        request = fields[ViewerStreamKwarg.STREAM_REQUEST.value]
        restored = ImagePayloadMetadata.from_viewer_image_metadata(
            request.source.item_fields["image_metadata"]
        )
        assert restored.to_viewer_image_metadata() == projection.image_metadata.to_viewer_image_metadata()
        assert request.source.metadata.metadata_by_path[str(archive)] == dict(
            persisted.source_provenance.scalar_source_identity.component_metadata,
        )
        assert restored.source_voxel_spacing == projection.image_metadata.source_voxel_spacing
        assert restored.source_spatial_domain == projection.image_metadata.source_spatial_domain
        # The archive travels as saved: its geometry plus the bound source
        # declaration, which the viewer reads and keeps out of the feature table.
        assert [ROIArchiveSourceMetadata.geometry(rois) for rois in data] == [geometry]
        assert ROIArchiveSourceMetadata.decode(data[0]) == persisted
        received.append((data, paths, request, identity.get()))

    def settle():
        assert threading.current_thread() is threading.main_thread()
        assert received, "Settlement must follow receiver publication"
        started = time.monotonic()
        if not timings:
            time.sleep(12)
        timings.append(time.monotonic() - started)
        viewer.settlement_calls += 1
        return True

    monkeypatch.setattr(
        "openhcs.agent.services.plate_streaming_service.StreamingViewerLifecycle.get_or_create_visualizer", acquire,
    )
    monkeypatch.setattr(FileManager, "save_batch", receive)
    monkeypatch.setattr(viewer, "settle_viewer_state", settle)
    service = PlateStreamingService(inspection, NoRuntimeBridge())
    arguments = {
        "plate_path": str(source_path.parent.parent),
        "result_directory": str(result_root), "kind": "result", "limit": 1,
        "file_paths": [archive.name], "fresh_viewer": False,
    }
    return service, arguments, identity, received, timings, unsigned


@pytest.mark.parametrize("declaration", (
    StreamPlateFilesToViewerCapability, UiStreamSelectedPlateFilesToViewerCapability,
))
def test_stream_declaration_composes_original_progress_and_main_affinity(declaration):
    assert issubclass(declaration, MainThreadProgressCapability)
    spec = declaration
    assert spec.progress_heartbeat_seconds == 1.0
    assert spec.progress_worker_thread_safe is False
    assert "progress_heartbeat_seconds" not in declaration.__dict__
    assert "progress_worker_thread_safe" not in declaration.__dict__


def test_saved_roi_continuous_sdk_receipt_error_reuse_beyond_ordinary_idle(
    tmp_path, saved_roi_stream,
):
    service, arguments, identity, received, timings, unsigned = saved_roi_stream
    transport = McpSocketTransport(tmp_path.parent / "stream.sock")
    built = build_server(OpenHCSAgentContext(plate_streaming_service=service),
                         main_thread_dispatcher=transport.execution.dispatcher)
    clients = AsyncOperationExecutor(max_workers=1)
    diagnostics = io.StringIO()
    events = []

    class ObservedSession(McpDevSocketSession):
        def record_progress_notification(self, notification):
            super().record_progress_notification(notification)
            assert threading.current_thread() is not threading.main_thread()
            events.append((time.monotonic(), notification.params.progressToken, notification.params.message))

    async def exercise():
        assert await asyncio.to_thread(wait_for_socket, transport.socket_path, timeout_seconds=10)
        try:
            async with ObservedSession(McpDevServerSpec(sys.executable), diagnostics, transport.socket_path) as session:
                await session.initialize(timeout_seconds=10)
                for index, paths in enumerate((arguments["file_paths"], [unsigned.name], arguments["file_paths"])):
                    before = len(events)
                    request_id = session.request_id + 1
                    started = time.monotonic()
                    result = await session.call_tool(StreamPlateFilesToViewerCapability.name,
                        {**arguments, "file_paths": paths}, timeout_seconds=10)
                    elapsed = time.monotonic() - started
                    progress = events[before:]
                    assert progress and progress[0][0] - started < 1
                    assert all(event[1] == request_id for event in progress)
                    payload = result["structuredContent"]
                    if index == 1:
                        assert payload["errors"][0]["code"] == "plate_file_stream_failed"
                        assert "Native ROI source metadata is required" in payload["errors"][0]["message"]
                        assert len(received) == 1
                    else:
                        assert payload["errors"] == []
                        assert payload["streamed_roi_paths"] == [str(Path(arguments["result_directory"]) / paths[0])]
                        assert payload["streamed_image_paths"] == []
                    if index == 0:
                        assert elapsed >= 12
                        assert any(event[0] - started > 10 and "still running" in event[2] for event in progress)
                        assert any("Streaming 1 ROI file(s)" in event[2] for event in progress)
                    print("ROI_STREAM_TERMINAL", index, elapsed, "idle10", "token", request_id, flush=True)
        finally:
            transport._stop.set()
            if transport._listener is not None:
                transport._listener.close()

    future = clients.submit(exercise)
    try:
        transport.serve(built)
        future.result()
        assert len(received) == 2 and len(timings) == 2
        assert "Resolving physical plate source context" in diagnostics.getvalue()
        assert "Checking managed viewer lifecycle" in diagnostics.getvalue()
    finally:
        clients.close()


def test_independent_stream_leaf_cooperative_hook_uses_generated_consumer(saved_roi_stream):
    service, arguments, identity, received, timings, _unsigned = saved_roi_stream
    timings.append(0.0)  # This declaration test does not repeat the slow experiment.
    hooks = []

    def audited(method):
        def run(service, request, connection):
            hooks.append("enter")
            result = method(service, request, connection)
            hooks.append("exit")
            return result

        return run

    # An independent declaration composes its own invocation from the inherited
    # one; the generated MCP consumer runs whichever invocation it declares.
    inherited = StreamPlateFilesToViewerCapability.invocation

    class IndependentStream(StreamPlateFilesToViewerCapability):
        name = "openhcs_independent_stream_progress_441"
        cli_command = None
        invocation = replace(inherited, method=audited(inherited.method))

    class IndependentStreamAfter(IndependentStream):
        name = "openhcs_independent_stream_progress_after_441"

    class ProgressContext:
        request_context = object()

        async def report_progress(self, progress, total=None, message=None):
            assert threading.current_thread() is not threading.main_thread()
            hooks.append(message)

    executor = McpTransportExecutor()
    built = build_server(OpenHCSAgentContext(plate_streaming_service=service),
                         main_thread_dispatcher=executor.dispatcher)

    async def exercise():
        token = identity.set("stream-request")
        try:
            for declaration in (IndependentStream, IndependentStreamAfter):
                result = await built._tool_manager.get_tool(declaration.name).fn(
                    mcp_context=ProgressContext(), **arguments)
                assert result["errors"] == []
                assert received[-1][3] == "stream-request"
        finally:
            identity.reset(token)

    try:
        executor.run(exercise)
        assert len(received) == 2
        assert hooks.count("enter") == hooks.count("exit") == 2
        assert hooks.index("enter") < hooks.index("exit")
        assert any("published and viewer settlement completed" in message for message in hooks)
    finally:
        executor.close()
        for declaration in (IndependentStream, IndependentStreamAfter):
            AgentCapabilityDeclaration.__registry__.pop(declaration.name)
