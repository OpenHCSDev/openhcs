"""Receiver integration checks for work acknowledged before Qt projection."""

from __future__ import annotations

import json
import uuid
import gc
import weakref
import logging

import numpy as np
import pytest
import zmq
from polystore.disk import DiskStorageBackend
from polystore.roi import ROI, PolygonShape, load_rois_from_zip
from polystore.roi_converters import NapariROIConverter
from polystore.streaming.identity import StreamProducerIdentity
from zmqruntime.config import TransportMode
from zmqruntime.transport import get_zmq_transport_url, remove_ipc_socket
from zmqruntime.viewer_protocol import ViewerBatchDisplayPayload

from openhcs.core.config import NapariDimensionMode, NapariDisplayConfig
from openhcs.runtime.napari_viewer_server import (
    NapariSettleControlMessageAction,
    NapariViewerServer,
)
from openhcs.runtime.viewer_protocol import (
    NapariViewerServerRequest,
    ViewerControlResponse,
    ViewerSettlePhase,
    ViewerSettleProgress,
)


@pytest.fixture
def receiver(qtbot):
    import napari

    server = NapariViewerServer(
        NapariViewerServerRequest(
            port=45000 + uuid.uuid4().int % 10000,
            viewer_title="isolated accepted-work test",
            replace_layers=False,
            log_file_path=None,
            transport_mode=TransportMode.IPC,
        )
    )
    server.viewer = napari.Viewer(show=False)
    try:
        yield server
    finally:
        server.request_shutdown()
        server.viewer.close()


@pytest.fixture
def wire_receiver(receiver):
    context = zmq.Context()
    socket = context.socket(zmq.REQ)
    socket.setsockopt(zmq.LINGER, 0)
    socket.setsockopt(zmq.RCVTIMEO, 5000)
    receiver._running = True
    receiver.data_transport_pump.start()
    socket.connect(get_zmq_transport_url(
        receiver.port, host="localhost", mode=receiver.transport_mode,
        config=receiver.config,
    ))

    def send(item):
        socket.send(wire_batch(item))
        return socket.recv_json()

    try:
        yield send
    finally:
        receiver._running = False
        receiver.data_transport_pump.stop()
        socket.close(linger=0)
        context.term()
        remove_ipc_socket(receiver.port, receiver.config)


def wire_batch(item):
    config = NapariDisplayConfig(channel_mode=NapariDimensionMode.LAYER)
    producer = StreamProducerIdentity.pipeline_output(
        output_kind="artifact", output_key="test", projection_key="test",
        step_name="saved ROI reopen", pipeline_position=0,
    )
    return json.dumps({
        "type": "batch",
        "images": [{**item, "producer_identity": producer.to_payload()}],
        "display_config": ViewerBatchDisplayPayload(
            component_modes=config.component_modes(),
            component_order=config.COMPONENT_ORDER,
            extra=config.display_payload_extra(),
        ).to_wire_mapping(),
        "component_value_domain": {
            "well": ["A01"], "site": [1], "channel": [1],
            "z_index": [1], "timepoint": [1],
        },
        "component_names_metadata": {},
    }, default=lambda value: value.tolist()).encode()


def image_item():
    return {
        "path": "A01.tif", "data_type": "image",
        "data": [[1, 2], [3, 4]], "dtype": "uint16", "shape": [2, 2],
        "metadata": {"well": "A01", "site": 1, "channel": 1,
                     "z_index": 1, "timepoint": 1},
    }


def settle(receiver):
    response = NapariSettleControlMessageAction().handle(receiver, {})
    return response, ViewerSettleProgress.from_response(ViewerControlResponse(response))


def saved_roi_item(tmp_path):
    archive = tmp_path / "aggregate_segmentation_masks_step1_rois.roi.zip"
    DiskStorageBackend()._save_rois([
        ROI([PolygonShape(np.array([[1, 1], [1, 4], [4, 4], [4, 1]]))],
            {"label": 1, "area": 9, "source_spatial_shape_yx": (6, 6)}),
    ], archive)
    shapes = NapariROIConverter.rois_to_shapes(load_rois_from_zip(archive))
    return {
        "path": str(archive), "data_type": "shapes", "shapes": shapes,
        "metadata": {"well": "A01"},
    }


def test_saved_roi_reopen_reports_pre_route_failure_and_recovers(
    receiver, wire_receiver, qtbot, tmp_path,
):
    assert wire_receiver(saved_roi_item(tmp_path))["status"] == "success"
    assert receiver.process_accepted_stream_messages() == 1
    assert not receiver.layer_route_state.layers
    assert not receiver.layer_route_state.layer_pending_updates
    response, progress = settle(receiver)
    assert response["status"] == "error"
    assert progress.phase is ViewerSettlePhase.FAILED
    assert "channel" in response["message"]

    # A new accepted batch starts the next existing settlement cycle. The
    # previous failed cycle must not become a permanent unrelated failure.
    assert wire_receiver(image_item())["status"] == "success"
    assert NapariSettleControlMessageAction().transport_thread_response(receiver, {}) is None
    receiver.process_accepted_stream_messages()
    settle(receiver)
    qtbot.waitUntil(lambda: settle(receiver)[1].phase is not ViewerSettlePhase.RUNNING,
                    timeout=5000)
    assert settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE
    assert len(receiver.viewer.layers) == 1


def test_previous_complete_cannot_settle_new_accepted_work(receiver):
    assert settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE
    assert receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()["status"] == "success"
    assert not receiver.accepted_stream_batches.empty()
    assert NapariSettleControlMessageAction().transport_thread_response(receiver, {}) is None


def test_payload_load_failure_is_rejected_before_route_creation(receiver):
    item = image_item()
    del item["data"]
    item["shm_name"] = "openhcs-missing-" + uuid.uuid4().hex
    response = receiver.accept_stream_message(wire_batch(item)).to_wire_mapping()
    assert response["status"] == "error"
    assert "not found" in response["message"]
    assert receiver.accepted_stream_batches.empty()
    assert not receiver.layer_route_state.layers


def test_pre_route_failure_survives_later_batch_before_settlement(receiver, qtbot, tmp_path):
    assert receiver.accept_stream_message(wire_batch(saved_roi_item(tmp_path))).to_wire_mapping()["status"] == "success"
    receiver.process_accepted_stream_messages()
    # No settlement has yet exposed the first failure. An additional accepted
    # batch cannot erase it even though its own native image mounts correctly.
    assert receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()["status"] == "success"
    receiver.process_accepted_stream_messages()
    settle(receiver)
    qtbot.waitUntil(lambda: settle(receiver)[1].phase is not ViewerSettlePhase.RUNNING,
                    timeout=5000)
    response, progress = settle(receiver)
    assert progress.phase is ViewerSettlePhase.FAILED
    assert "channel" in response["message"]
    assert len(receiver.viewer.layers) == 1


def test_clear_state_discards_pre_route_failure(receiver, tmp_path):
    assert receiver.accept_stream_message(wire_batch(saved_roi_item(tmp_path))).to_wire_mapping()["status"] == "success"
    receiver.process_accepted_stream_messages()
    receiver.clear_accumulated_stream_state()
    assert settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE
    assert receiver.layer_route_state.update_failure_message() is None


def test_active_settlement_rejects_admission_without_retaining_copies(
    receiver, monkeypatch,
):
    assert receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()["status"] == "success"
    receiver.process_accepted_stream_messages()
    assert settle(receiver)[1].phase is ViewerSettlePhase.RUNNING
    settlement = receiver.layer_route_state.layer_settlement
    original_accept = receiver._accept_single_image
    copied_arrays = []

    def observe_copy(*args):
        item = original_accept(*args)
        copied_arrays.append(weakref.ref(item.data))
        return item

    monkeypatch.setattr(receiver, "_accept_single_image", observe_copy)
    # pytest's capture/report handlers retain exception traceback frames.
    # Exclude those test-owned references from this receiver-lifetime check.
    monkeypatch.setattr(logging.getLogger(type(receiver).__module__), "disabled", True)
    response = receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()
    assert response["status"] == "error"
    assert "active Napari layer settlement" in response["message"]
    assert receiver.accepted_stream_batches.empty()
    assert receiver.layer_route_state.layer_settlement is settlement
    assert receiver.layer_route_state.update_failure_message() is None
    gc.collect()
    assert copied_arrays and all(reference() is None for reference in copied_arrays)
