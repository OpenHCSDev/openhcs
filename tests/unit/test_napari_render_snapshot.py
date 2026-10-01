"""Accepted Qt queue -> native-owner hook -> typed snapshot reply, source only."""

import pickle
import queue
from types import SimpleNamespace

import pytest
from napari.components import ViewerModel
from PyQt6.QtCore import QEvent, pyqtSignal
from PyQt6.QtGui import QColor, QImage, QPainter
from PyQt6.QtWidgets import QApplication, QWidget
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
        frameSwapped = pyqtSignal()

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
    from PyQt6 import sip

    if not sip.isdeleted(canvas):
        canvas.close()
        canvas.deleteLater()
    app.sendPostedEvents(None, QEvent.Type.DeferredDelete)
    app.processEvents()


def enqueue(server, capture):
    reply = queue.Queue(maxsize=1)
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
    assert reply.empty() and not tuple(tmp_path.glob("*.png"))
    app.processEvents()
    response = pickle.loads(reply.get_nowait())
    assert response["status"] == "success"
    assert response["snapshot"].same_capture_contract(request)
    receipt = response["observation"]
    request.frame_condition.validate_observation(receipt)
    assert receipt.render_frame.renderer_identity == id(canvas)
    assert QImage(response["resource"]["path"]).pixelColor(30, 30) == QColor("blue")
    assert response["native_dimensions"]["ndisplay"] == server.viewer.dims.ndisplay
    app.processEvents()
    assert reply.empty()  # Exactly one reply despite grab repainting the canvas.


def test_explicit_immediate_still_uses_shared_capture_contract(queued_viewer, tmp_path):
    _, _, server = queued_viewer
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
        frame_condition=WindowSnapshotFrameCondition.IMMEDIATE,
    )
    response = pickle.loads(enqueue(server, request).get_nowait())
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
    response = pickle.loads(reply.get_nowait())
    assert response["status"] == "error"
    assert response["observation"].render_frame is None
    assert "destroyed" in response["message"]
    assert not tuple(tmp_path.glob("*.png"))


def test_new_control_case_requires_only_registered_declaration_and_hook(queued_viewer):
    _, _, server = queued_viewer

    class DeclarationOnlyControl(NapariControlMessageAction):
        message_type = "source_qa_declaration_only"

        def handle(self, server, message):
            return {"status": "success", "token": message["payload"]}

    try:
        reply = queue.Queue(maxsize=1)
        server.accepted_control_requests.put(
            NapariAcceptedControlRequest(
                {"type": DeclarationOnlyControl.message_type, "payload": 17},
                reply,
            )
        )
        server.process_messages()
        assert pickle.loads(reply.get_nowait()) == {"status": "success", "token": 17}
    finally:
        NapariControlMessageAction.__registry__.pop(DeclarationOnlyControl.message_type)
