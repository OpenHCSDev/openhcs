"""Provider/plugin-free source contracts; installed native acceptance is separate."""

from __future__ import annotations

import inspect
from dataclasses import replace
from typing import get_type_hints

import pytest
from pyqt_reactive.services.window_snapshot import (
    QtWindowSnapshotRequest,
    WindowRenderFrame,
    WindowSnapshotFrameCondition,
    WindowSnapshotRenderOwner,
    WindowVisualObservation,
)
from python_introspect import dataclass_from_mapping

from openhcs.agent.capabilities import ViewerSnapshotWindowCapability
from openhcs.agent.dto.common import AgentError
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import (
    ViewerWindowDescriptor,
    ViewerWindowSnapshotRequest,
    ViewerWindowSnapshotResult,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.viewer_window_service import ViewerWindowService
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.runtime.viewer_snapshot import ViewerWindowSnapshotService
from openhcs.serialization.json import to_jsonable


def _request(tmp_path):
    return ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
        frame_condition="render_complete",
        observation_timeout_s=0.5,
    )


def _receipt(request):
    return WindowVisualObservation(
        condition=request.frame_condition,
        window_identity=3,
        started_at_monotonic=1.0,
        completed_at_monotonic=3.0,
        configured_flash_duration_s=0.0,
        baseline_inactive=True,
        flash_start_count=0,
        painted_frame_count=1,
        render_frame=WindowRenderFrame(3, 4, 2.0),
    )


def _response(request, observation):
    return {
        "status": "success",
        "snapshot": request,
        "observation": observation,
        "viewer": {"type": "napari", "title": "Source snapshot"},
        "resource": {
            "uri": "file:///source-frame.png",
            "title": "Source snapshot",
            "mime_type": "image/png",
        },
        "width": 80,
        "height": 60,
    }


def test_snapshot_mcp_signature_and_projection_come_from_original_owners(tmp_path):
    request = _request(tmp_path)
    assert ViewerSnapshotWindowCapability.input_contract is ViewerWindowSnapshotRequest
    hints = get_type_hints(ViewerWindowSnapshotRequest.from_fields)
    assert hints["frame_condition"] is WindowSnapshotFrameCondition
    assert (
        "observation_timeout_s"
        in inspect.signature(ViewerWindowSnapshotRequest.from_fields).parameters
    )
    arguments = request.as_tool_arguments()
    assert arguments["frame_condition"] == "render_complete"
    assert arguments["observation_timeout_s"] == 0.5
    assert (
        request.capture_fields()
        == dataclass_from_mapping(
            ViewerWindowSnapshotRequest,
            to_jsonable(request),
        ).capture_fields()
    )


def test_snapshot_error_preserves_every_requested_capture_field(tmp_path):
    request = _request(tmp_path)
    result = ViewerWindowSnapshotResult.from_request_error(
        request=request,
        error=AgentError(code="source", message="original failure"),
    )
    assert not result.captured
    assert result.same_capture_contract(request)
    assert result.errors[0].message == "original failure"


def test_failed_render_preserves_original_observation_without_claiming_capture(
    tmp_path,
):
    request = _request(tmp_path)
    receipt = replace(_receipt(request), render_frame=None, painted_frame_count=0)
    result = ViewerWindowService()._snapshot_result_from_response(
        connection=request.connection,
        request=request,
        response={
            "status": "error",
            "message": "original native timeout",
            "observation": receipt,
        },
    )
    assert not result.captured and result.resource is None
    assert result.same_capture_contract(request)
    assert result.observation is receipt
    assert result.errors[0].message == "original native timeout"


@pytest.mark.parametrize(
    "receipt_change",
    [
        {"render_frame": None},
        {"render_frame": WindowRenderFrame(99, 4, 2.0)},
        {"render_frame": WindowRenderFrame(3, 4, 0.0)},
        {"condition": WindowSnapshotFrameCondition.IMMEDIATE},
    ],
)
def test_captured_pixels_do_not_admit_missing_stale_or_foreign_receipts(
    tmp_path, receipt_change
):
    request = _request(tmp_path)
    response = _response(request, replace(_receipt(request), **receipt_change))
    service = ViewerWindowService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,),
            writable_roots=(tmp_path,),
        )
    )
    with pytest.raises(ValueError):
        service._snapshot_result_from_response(
            connection=request.connection, request=request, response=response
        )


def test_native_receipt_and_capture_contract_roundtrip_through_result(tmp_path):
    request = _request(tmp_path)
    receipt = _receipt(request)
    result = ViewerWindowService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,),
            writable_roots=(tmp_path,),
        )
    )._snapshot_result_from_response(
        connection=request.connection,
        request=request,
        response=_response(request, receipt),
    )
    assert result.captured and result.same_capture_contract(request)
    assert result.observation is receipt
    # The normal DTO decoder reconstructs the typed nested renderer receipt.
    decoded = dataclass_from_mapping(
        ViewerWindowSnapshotResult, to_jsonable(replace(result, response={}))
    )
    assert decoded.observation == receipt


@pytest.mark.parametrize(
    "resource_change",
    [
        {"uri": 17},
        {"size_bytes": "not an integer"},
        {"undeclared_field": 1},
    ],
)
def test_snapshot_resource_decodes_once_against_original_schema(
    tmp_path, resource_change
):
    request = _request(tmp_path)
    response = _response(request, _receipt(request))
    response["resource"].update(resource_change)
    with pytest.raises((TypeError, ValueError)):
        ViewerWindowService()._snapshot_result_from_response(
            connection=request.connection,
            request=request,
            response=response,
        )


def test_managed_reply_uses_real_qt_frame_through_original_capture_ancestor(tmp_path):
    from PyQt6.QtCore import QEventLoop, pyqtSignal
    from PyQt6.QtGui import QColor, QImage, QPainter
    from PyQt6.QtWidgets import QApplication, QWidget

    # Same existing QApplication/Qt painter entrypoint as pyqt-reactive's qapp
    # fixture, without loading OpenHCS root-conftest process cleanup hooks.
    app = QApplication.instance() or QApplication([])

    class Canvas(QWidget):
        frame_completed = pyqtSignal()

        def paintEvent(self, event):
            painter = QPainter(self)
            painter.fillRect(self.rect(), QColor("green"))
            painter.end()
            self.frame_completed.emit()

    class NativePaintOwner(WindowSnapshotRenderOwner):
        def __init__(self, canvas):
            super().__init__()
            self.canvas = canvas

        @property
        def widget(self):
            return self.canvas

        @property
        def frame_completed(self):
            return self.canvas.frame_completed

        def request_frame(self):
            self.canvas.update()

    canvas = Canvas()
    canvas.resize(80, 60)
    canvas.show()
    app.processEvents()
    completed, failed = [], []
    event_loop = QEventLoop()

    def complete(response):
        completed.append(response)
        event_loop.quit()

    def fail(response):
        failed.append(response)
        event_loop.quit()

    request = _request(tmp_path)
    try:
        ViewerWindowSnapshotService().request_viewer_capture(
            QtWindowSnapshotRequest(
                widget=canvas,
                capture=request,
                subject_id="source-render",
                title="Source snapshot",
                render_owner=NativePaintOwner(canvas),
            ),
            ViewerWindowDescriptor(
                viewer_type=ViewerType.NAPARI, title="Source snapshot"
            ),
            complete,
            fail,
        )
        assert not completed and not failed
        # The capture owns its existing deadline; run Qt until its terminal reply.
        event_loop.exec()
        assert not failed and len(completed) == 1
        result = ViewerWindowService(
            path_policy=AgentPathPolicy.with_roots(
                readable_roots=(tmp_path,),
                writable_roots=(tmp_path,),
            )
        )._snapshot_result_from_response(
            connection=request.connection,
            request=request,
            response=completed[0],
        )
        assert result.captured and result.same_capture_contract(request)
        assert result.observation.render_frame.renderer_identity == id(canvas)
        assert QImage(result.resource.path).pixelColor(30, 30) == QColor("green")
    finally:
        canvas.close()
        canvas.deleteLater()
