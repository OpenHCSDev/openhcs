"""One real Qt queue/deadline journey through the original gateway, no sockets."""

import pickle
import queue
import time

import pytest

from test_napari_render_snapshot import queued_viewer
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import ViewerWindowSnapshotRequest
from openhcs.agent.services import viewer_window_service as service_module
from openhcs.agent.services.viewer_window_service import ZMQViewerWindowGateway
from openhcs.runtime.napari_viewer_server import NapariAcceptedControlRequest


def test_default_capture_reply_relation_and_explicit_contradictions(tmp_path):
    connection = ExecutionConnectionSpec(port=5584)
    direct = ViewerWindowSnapshotRequest(
        connection=connection, output_dir_path=str(tmp_path)
    )
    factory = ViewerWindowSnapshotRequest.from_fields(
        connection=connection, output_dir_path=str(tmp_path)
    )
    assert direct.observation_timeout_s == factory.observation_timeout_s == 2.5
    assert factory.timeout_ms == 5000
    assert factory.observation_timeout_s * 1000 < factory.timeout_ms
    for timeout in (5.0, 10.0):
        with pytest.raises(ValueError, match="less than transport"):
            ViewerWindowSnapshotRequest.from_fields(
                connection=connection,
                observation_timeout_s=timeout,
                timeout_ms=5000,
            )


def test_no_frame_failure_reaches_original_gateway_before_bound_and_cannot_capture_late(
    queued_viewer,
    tmp_path,
    monkeypatch,
):
    app, canvas, server = queued_viewer
    canvas.setUpdatesEnabled(False)
    reply = queue.Queue(maxsize=1)

    class Socket:
        def setsockopt(self, *args):
            pass

        def connect(self, *args):
            pass

        def close(self, *args, **kwargs):
            pass

        def send(self, data, flags):
            self.message = pickle.loads(data)
            server.accepted_control_requests.put(
                NapariAcceptedControlRequest(self.message, reply)
            )
            server.process_messages()

        def recv(self, flags):
            return reply.get_nowait()

    socket = Socket()

    class Context:
        def socket(self, *args):
            return socket

        def destroy(self, **kwargs):
            pass

    class Poller:
        def register(self, *args):
            pass

        def poll(self, timeout):
            self.timeout = timeout
            end = time.monotonic() + timeout / 1000
            while reply.empty() and time.monotonic() < end:
                app.processEvents()
            return [(socket, service_module.zmq.POLLIN)] if not reply.empty() else []

    poller = Poller()
    monkeypatch.setattr(service_module.zmq, "Poller", lambda: poller)
    request = ViewerWindowSnapshotRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        output_dir_path=str(tmp_path),
        timeout_ms=400,
        observation_timeout_s=0.02,
    )
    started = time.monotonic()
    response = ZMQViewerWindowGateway(context_factory=Context).snapshot_window(request)
    assert time.monotonic() - started < request.timeout_ms / 1000
    assert 0 < poller.timeout <= request.timeout_ms
    assert response["status"] == "error"
    receipt = response["observation"]
    assert receipt.render_frame is None and receipt.painted_frame_count == 0
    assert receipt.observation_budget_s <= request.observation_timeout_s
    assert receipt.operation_deadline == socket.message["payload"].operation_deadline
    assert not tuple(tmp_path.glob("*.png")) and reply.empty()
    canvas.setUpdatesEnabled(True)
    canvas.update()
    app.processEvents()
    assert reply.empty() and not tuple(tmp_path.glob("*.png"))
