"""Accepted Qt queue -> native-owner hook -> typed snapshot reply, source only."""

import pickle
import queue
from concurrent.futures import Future
from dataclasses import replace
from types import SimpleNamespace

import pytest
from napari.components import ViewerModel
from qtpy.QtCore import QEvent, Signal
from qtpy.QtGui import QColor, QImage, QPainter
from qtpy.QtWidgets import QApplication, QWidget
from pyqt_reactive.services.window_snapshot import WindowSnapshotFrameCondition
from zmqruntime.config import TransportMode
from zmqruntime.transport import TransportEndpoint

from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import ViewerWindowSnapshotRequest
from openhcs.runtime.napari_viewer_server import (
    NapariAcceptedControlRequest,
    NapariControlMessageAction,
    NapariScreenshotControlMessageAction,
    NapariViewerServer,
)
from openhcs.runtime.viewer_snapshot import ViewerWindowSnapshotService


@pytest.fixture
def queued_viewer():
    # Real Qt paint entrypoint and real ViewerModel; no application/server startup.
    app = QApplication.instance() or QApplication([])

    class Canvas(QWidget):
        frameSwapped = Signal()

        def paintEvent(self, event):
            painter = QPainter(self)
            painter.fillRect(self.rect(), QColor("blue"))
            painter.end()
            self.frameSwapped.emit()

    canvas = Canvas()
    canvas.resize(80, 60)
    canvas.show()
    app.processEvents()
    viewer = ViewerModel()
    viewer.__dict__["window"] = SimpleNamespace(
        qt_viewer=SimpleNamespace(
            window=canvas.window, canvas=SimpleNamespace(native=canvas)
        )
    )
    server = object.__new__(NapariViewerServer)
    server.viewer = viewer
    server.endpoint = TransportEndpoint(
        host="localhost", port=5584, transport_mode=TransportMode.TCP
    )
    server.napari_window_title = "Queued source snapshot"
    server.accepted_control_requests = queue.Queue()
    yield app, canvas, server
    from qtpy.compat import isalive

    if isalive(canvas):
        canvas.close()
        canvas.deleteLater()
    app.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    app.processEvents()


def enqueue(server, capture):
    reply = Future()
    message = pickle.loads(pickle.dumps({"type": "screenshot", "payload": capture}))
    server.accepted_control_requests.put(NapariAcceptedControlRequest(message, reply))
    server.process_messages()
    return reply


def test_default_render_condition_flows_through_registered_queue_and_real_paint(
    queued_viewer, tmp_path
):
    app, canvas, server = queued_viewer
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
        observation_timeout_s=0.5,
    )
    assert request.frame_condition is WindowSnapshotFrameCondition.RENDER_COMPLETE
    action = NapariControlMessageAction.for_message_type("screenshot")
    assert isinstance(action, NapariScreenshotControlMessageAction)
    assert isinstance(action, ViewerWindowSnapshotService)
    assert action.__class__.__mro__.index(
        NapariControlMessageAction
    ) < action.__class__.__mro__.index(ViewerWindowSnapshotService)
    reply = enqueue(server, request)
    assert not reply.done() and not tuple(tmp_path.glob("*.png"))
    app.processEvents()
    response = pickle.loads(reply.result(timeout=0))
    assert response["status"] == "success"
    assert response["snapshot"].same_capture_contract(request)
    receipt = response["observation"]
    request.frame_condition.validate_observation(receipt)
    assert receipt.render_frame.renderer_identity == id(canvas)
    assert QImage(response["resource"]["path"]).pixelColor(30, 30) == QColor("blue")
    assert response["native_dimensions"]["ndisplay"] == server.viewer.dims.ndisplay
    app.processEvents()
    assert reply.done()  # One immutable result despite grab repainting the canvas.


def test_explicit_immediate_still_uses_shared_capture_contract(queued_viewer, tmp_path):
    _, _, server = queued_viewer
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
        frame_condition=WindowSnapshotFrameCondition.IMMEDIATE,
    )
    response = pickle.loads(enqueue(server, request).result(timeout=0))
    assert response["status"] == "success" and response["observation"] is None
    assert response["snapshot"].same_capture_contract(request)


def test_queued_destroyed_owner_preserves_failure_receipt(queued_viewer, tmp_path):
    app, canvas, server = queued_viewer
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
    )
    reply = enqueue(server, request)
    canvas.deleteLater()
    app.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    response = pickle.loads(reply.result(timeout=0))
    assert response["status"] == "error"
    assert response["observation"].render_frame is None
    assert "destroyed" in response["message"]
    assert not tuple(tmp_path.glob("*.png"))


def test_real_vispy_native_binding_through_original_registered_queue(
    queued_viewer, tmp_path
):
    import time

    from qtpy import API_NAME, QtCore
    from vispy.app import Canvas

    app, window, server = queued_viewer
    # Original Canvas.native returns this backend, whose MRO owns the Qt widget.
    # Keep it hidden: source acceptance tests ownership, not OpenGL rendering.
    canvas = Canvas(parent=window, show=False, size=(64, 64))
    from vispy.app.backends._qt import CanvasBackendDesktop, QGLWidget

    native = canvas.native
    assert isinstance(native, CanvasBackendDesktop)
    assert isinstance(native, QGLWidget) and isinstance(native, QtCore.QObject)
    native.hide()
    server.viewer.window.qt_viewer.canvas = canvas
    action = NapariControlMessageAction.for_message_type("screenshot")
    assert action.qt_core() is QtCore
    print(f"QtPy binding={API_NAME}; native MRO={type(native).__mro__}")
    try:
        request = ViewerWindowSnapshotRequest.from_fields(
            connection=ExecutionConnectionSpec(port=5584),
            output_dir_path=str(tmp_path),
            timeout_ms=400,
            observation_timeout_s=0.02,
        ).start_operation()
        reply = enqueue(server, request)
        assert not reply.done(), "Observation must arm, not reject the real Qt parent"
        timer = native.findChild(QtCore.QTimer)
        assert timer is not None and timer.parent() is native
        end = time.monotonic() + request.timeout_ms / 1000
        while not reply.done() and time.monotonic() < end:
            app.processEvents()
        response = pickle.loads(reply.result(timeout=0))
        assert response["status"] == "error" and "not observed" in response["message"]
        assert response["observation"].render_frame is None
        assert response["observation"].operation_deadline == request.operation_deadline
        assert not tuple(tmp_path.glob("*.png"))
        native.frameSwapped.emit()  # Late signal cleanup, not a fake render proof.
        app.processEvents()
        assert reply.done() and not tuple(tmp_path.glob("*.png"))
    finally:
        canvas.close()


def test_new_control_case_requires_only_registered_declaration_and_hook(queued_viewer):
    _, _, server = queued_viewer

    class DeclarationOnlyControl(NapariControlMessageAction):
        message_type = "source_qa_declaration_only"

        def handle(self, server, message):
            return {"status": "success", "token": message["payload"]}

    try:
        reply = Future()
        server.accepted_control_requests.put(
            NapariAcceptedControlRequest(
                {"type": DeclarationOnlyControl.message_type, "payload": 17},
                reply,
            )
        )
        server.process_messages()
        assert pickle.loads(reply.result(timeout=0)) == {"status": "success", "token": 17}
    finally:
        NapariControlMessageAction.__registry__.pop(DeclarationOnlyControl.message_type)


def test_deferred_reply_projection_error_completes_accepted_request(
    queued_viewer, tmp_path, monkeypatch
):
    app, _, server = queued_viewer

    def reject_native_projection(server, response):
        raise ValueError("native dimension projection failed")

    monkeypatch.setattr(
        NapariScreenshotControlMessageAction, "_native_reply",
        staticmethod(reject_native_projection),
    )
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
        observation_timeout_s=0.5,
    )
    reply = enqueue(server, request)
    app.processEvents()
    response = pickle.loads(reply.result(timeout=0))
    assert response["status"] == "error"
    assert "native dimension projection failed" in response["message"]


def test_snapshot_original_deadline_releases_transport_without_cancelling_qt_work(
    queued_viewer, tmp_path
):
    import threading
    from openhcs.runtime.napari_viewer_server import NapariControlTransportPump

    app, _, server = queued_viewer
    server._running = True
    pump = NapariControlTransportPump(server)
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path), timeout_ms=150, observation_timeout_s=0.02,
    ).start_operation()
    replies = Future()

    def receive():
        replies.set_result(pump._response_payload(
            pickle.dumps({"type": "screenshot", "payload": request})
        ))

    thread = threading.Thread(target=receive)
    thread.start()
    # Deliberately no Qt dispatch before the ORIGINAL request deadline.
    response = pickle.loads(replies.result(timeout=2))
    thread.join(timeout=1)
    assert not thread.is_alive() and response["status"] == "error"
    assert not server.accepted_control_requests.empty()  # Not cancelled/not-started claim.
    assert not tuple(tmp_path.glob("*.png"))
    server.process_messages()
    app.processEvents()
    assert not tuple(tmp_path.glob("*.png"))
    assert pickle.loads(replies.result()) == response  # Late callback cannot replace it.
    server._running = False


@pytest.mark.parametrize("corrupted_fields", [
    {"operation_deadline": "old positional slot value"},
    {"frame_condition": 5.0},
])
def test_corrupted_snapshot_is_rejected_before_qt_queue(
    queued_viewer, tmp_path, corrupted_fields
):
    from openhcs.runtime.napari_viewer_server import NapariControlTransportPump

    _, _, server = queued_viewer
    pump = NapariControlTransportPump(server)
    request = replace(ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
    ), **corrupted_fields)
    response = pickle.loads(pump._response_payload(pickle.dumps(
        {"type": "screenshot", "payload": request}
    )))
    assert response["status"] == "error"
    assert server.accepted_control_requests.empty()
    assert not tuple(tmp_path.glob("*.png"))
