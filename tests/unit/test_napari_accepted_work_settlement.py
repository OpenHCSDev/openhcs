"""Receiver integration checks for work acknowledged before Qt projection."""

from __future__ import annotations

import json
import uuid
import gc
import weakref
import logging
import os
import pickle
import time
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor

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
    socket.connect(
        get_zmq_transport_url(
            receiver.port,
            host="localhost",
            mode=receiver.transport_mode,
            config=receiver.config,
        )
    )

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
    items = item if isinstance(item, list) else [item]
    config = NapariDisplayConfig(channel_mode=NapariDimensionMode.LAYER)
    producer = StreamProducerIdentity.pipeline_output(
        output_kind="artifact",
        output_key="test",
        projection_key="test",
        step_name="saved ROI reopen",
        pipeline_position=0,
    )
    return json.dumps(
        {
            "type": "batch",
            "images": [{**row, "producer_identity": producer.to_payload()} for row in items],
            "display_config": ViewerBatchDisplayPayload(
                component_modes=config.component_modes(),
                component_order=config.COMPONENT_ORDER,
                extra=config.display_payload_extra(),
            ).to_wire_mapping(),
            "component_value_domain": {
                key: sorted({row["metadata"].get(key, value) for row in items})
                for key, value in image_item()["metadata"].items()
            },
            "component_names_metadata": {},
        },
        default=lambda value: value.tolist(),
    ).encode()


def image_item():
    return {
        "path": "A01.tif",
        "data_type": "image",
        "data": [[1, 2], [3, 4]],
        "dtype": "uint16",
        "shape": [2, 2],
        "metadata": {
            "well": "A01",
            "site": 1,
            "channel": 1,
            "z_index": 1,
            "timepoint": 1,
        },
    }


def settle(receiver):
    response = NapariSettleControlMessageAction().handle(receiver, {})
    return response, ViewerSettleProgress.from_response(ViewerControlResponse(response))


def saved_roi_item(tmp_path):
    archive = tmp_path / "aggregate_segmentation_masks_step1_rois.roi.zip"
    DiskStorageBackend()._save_rois(
        [
            ROI(
                [PolygonShape(np.array([[1, 1], [1, 4], [4, 4], [4, 1]]))],
                {"label": 1, "area": 9, "source_spatial_shape_yx": (6, 6)},
            ),
        ],
        archive,
    )
    shapes = NapariROIConverter.rois_to_shapes(load_rois_from_zip(archive))
    return {
        "path": str(archive),
        "data_type": "shapes",
        "shapes": shapes,
        "metadata": {"well": "A01"},
    }


def test_saved_roi_reopen_reports_pre_route_failure_and_recovers(
    receiver,
    wire_receiver,
    qtbot,
    tmp_path,
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
    admitted = ViewerSettleProgress.from_response(ViewerControlResponse(
        NapariSettleControlMessageAction().transport_thread_response(receiver, {})
    ))
    assert admitted.phase is ViewerSettlePhase.RUNNING
    assert admitted.total_update_count == 0
    receiver.process_accepted_stream_messages()
    settle(receiver)
    qtbot.waitUntil(
        lambda: settle(receiver)[1].phase is not ViewerSettlePhase.RUNNING, timeout=5000
    )
    assert settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE
    assert len(receiver.viewer.layers) == 1


def test_previous_complete_cannot_settle_new_accepted_work(receiver):
    assert settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE
    assert (
        receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()[
            "status"
        ]
        == "success"
    )
    assert not receiver.accepted_stream_batches.empty()
    admitted = ViewerSettleProgress.from_response(ViewerControlResponse(
        NapariSettleControlMessageAction().transport_thread_response(receiver, {})
    ))
    assert admitted.phase is ViewerSettlePhase.RUNNING
    assert admitted.total_update_count == 0


def test_initial_settlement_is_observable_before_qt_intake_and_completes(
    receiver, wire_receiver, qtbot, tmp_path,
):
    """Use actual transport, native layers and Qt service, without delayed mocks."""
    from qtpy.QtCore import QTimer
    from zmqruntime.transport import get_control_port
    from polystore.filemanager import FileManager
    from polystore.streaming.viewer_transport import ViewerTransportEndpoint
    from openhcs.core.streaming_config_declarations import ViewerType
    from openhcs.core.streaming_config_factory import StreamingViewerRuntimeConfig
    from openhcs.runtime.napari_stream_visualizer import NapariStreamVisualizer

    archive = os.environ.get("OPENHCS_SETTLEMENT_QUALIFICATION_ROI")
    if archive:
        rois = load_rois_from_zip(Path(archive))
        item = {
            "path": archive,
            "data_type": "shapes",
            "shapes": NapariROIConverter.rois_to_shapes(rois),
            "metadata": image_item()["metadata"],
        }
    else:
        item = image_item()
    directory = os.environ.get("OPENHCS_SETTLEMENT_QUALIFICATION_ROI_DIRECTORY")
    if directory:
        items = []
        for path in sorted(Path(directory).glob("*_rois.roi.zip")):
            parts = path.name.split("_")
            metadata = {**image_item()["metadata"], "well": parts[0],
                        "site": int(parts[1][1:]), "channel": int(parts[2][1:])}
            items.append({"path": str(path), "data_type": "shapes",
                          "shapes": NapariROIConverter.rois_to_shapes(load_rois_from_zip(path)),
                          "metadata": metadata})
        assert items
        item = items
    assert wire_receiver(item)["status"] == "success"
    assert not receiver.accepted_stream_batches.empty()
    assert not receiver.layer_route_state.layer_pending_updates

    context = zmq.Context()
    control = context.socket(zmq.REQ)
    control.setsockopt(zmq.LINGER, 0)
    control.setsockopt(zmq.RCVTIMEO, 2000)
    receiver.control_transport_pump.start()
    control_port = get_control_port(receiver.port, receiver.config)
    control.connect(get_zmq_transport_url(
        control_port, host="localhost", mode=receiver.transport_mode,
        config=receiver.config,
    ))
    service = QTimer()
    service.timeout.connect(receiver.process_accepted_stream_messages)
    service.timeout.connect(receiver.process_messages)
    client = NapariStreamVisualizer(
        filemanager=FileManager({}),
        runtime_config=StreamingViewerRuntimeConfig(
            transport_endpoint=ViewerTransportEndpoint(
                port=receiver.port, host="localhost", transport_mode=receiver.transport_mode,
            ), persistent=False, viewer_type=ViewerType.NAPARI,
        ),
    )
    client.lifecycle_state.mark_connected_external()
    observations = []
    client_worker = ThreadPoolExecutor(max_workers=1)
    late_observer = os.environ.get("OPENHCS_SETTLEMENT_QUALIFICATION_LATE_OBSERVER") == "true"
    client_started = []
    delivery = None

    def deliver():
        if late_observer:
            deadline = time.monotonic() + 90
            while True:
                progress = receiver.layer_route_state.existing_settlement_progress()
                if (progress is not None and progress.active_route is not None
                        and "channel_2" in progress.active_route
                        and progress.active_route_work_unit_active):
                    break
                if time.monotonic() >= deadline:
                    raise AssertionError("No real channel-2 native work was observed.")
                time.sleep(0.001)
        client_started.append(time.perf_counter())
        return client.settle_viewer_state(
            progress_callback=lambda progress: observations.append((time.perf_counter(), progress)),
        )

    def observe():
        control.send(pickle.dumps({"type": "settle"}))
        return ViewerSettleProgress.from_response(ViewerControlResponse(
            pickle.loads(control.recv())
        ))

    try:
        started = time.perf_counter()
        first = (receiver.layer_route_state.existing_settlement_progress()
                 if late_observer else observe())
        elapsed = time.perf_counter() - started
        assert first.phase is ViewerSettlePhase.RUNNING
        assert first.completed_update_count == first.total_update_count == 0
        cycle = receiver.layer_route_state.layer_settlement
        assert cycle.awaiting_updates
        if not late_observer:
            assert observe() == first
        assert receiver.layer_route_state.layer_settlement is cycle
        assert receiver.accepted_control_requests.empty()
        if not late_observer:
            with pytest.raises(RuntimeError, match="active.*settlement"):
                receiver.layer_route_state.reset_settlement()
            with pytest.raises(RuntimeError, match="active.*settlement"):
                receiver.layer_route_state.require_retirement_boundary()

        # New accepted input belongs to this admitted, not-yet-bound cycle.
        assert wire_receiver(image_item())["status"] == "success"
        assert receiver.layer_route_state.layer_settlement is cycle
        receiver.viewer.window.show()
        started_delivery = time.perf_counter()
        delivery = client_worker.submit(deliver)
        service.start(50)
        # The real client owns the no-progress deadline. A second wall-clock
        # deadline can interrupt moving native work and then manufacture an
        # idle timeout by joining that client while its Qt callbacks cannot run.
        while not delivery.done():
            qtbot.wait(50)
        assert delivery.result()
        final = observe()
        assert final.completed_update_count == final.total_update_count
        assert final.total_update_count > 0
        assert receiver.accepted_stream_batches.empty()
        assert receiver.viewer.layers
        assert final.processed_intake_item_count == (len(item) if isinstance(item, list) else 1) + 1
        awaiting = [(t, p) for t, p in observations
                    if p.phase is ViewerSettlePhase.RUNNING and p.total_update_count == 0]
        awaiting_seconds = (awaiting[-1][0] - awaiting[0][0]) if awaiting else 0
        receiver.viewer.screenshot(path=str(tmp_path / "native-settlement.png"))
        first_reply_seconds = observations[0][0] - client_started[0] if late_observer else elapsed
        print(f"native first settlement {first_reply_seconds:.4f}s; pending intake admitted; "
              f"terminal {final.completed_update_count}/{final.total_update_count}; "
              f"native layers {len(receiver.viewer.layers)}; archive={archive}; "
              f"intake items={final.processed_intake_item_count}; "
              f"client delivery={time.perf_counter() - started_delivery:.3f}s; "
              f"unbound observations={len(awaiting)} over {awaiting_seconds:.3f}s; "
              f"first={awaiting[0][1] if awaiting else None}; "
              f"last={awaiting[-1][1] if awaiting else None}")
        if late_observer:
            assert observations[0][1].active_route_work_unit_active
            assert awaiting_seconds > 30, f"Actual unbound work was only {awaiting_seconds:.3f}s"
    finally:
        # Preserve Qt service until the original observation reaches terminal;
        # never block its callback owner on the observer thread's join.
        while delivery is not None and not delivery.done():
            qtbot.wait(50)
        service.stop()
        client_worker.shutdown(wait=True)
        receiver.control_transport_pump.stop()
        control.close(linger=0)
        context.term()
        remove_ipc_socket(control_port, receiver.config)


def test_payload_load_failure_is_rejected_before_route_creation(receiver):
    item = image_item()
    del item["data"]
    item["shm_name"] = "openhcs-missing-" + uuid.uuid4().hex
    response = receiver.accept_stream_message(wire_batch(item)).to_wire_mapping()
    assert response["status"] == "error"
    assert "not found" in response["message"]
    assert receiver.accepted_stream_batches.empty()
    assert not receiver.layer_route_state.layers


def test_pre_route_failure_survives_later_batch_before_settlement(
    receiver, qtbot, tmp_path
):
    assert (
        receiver.accept_stream_message(
            wire_batch(saved_roi_item(tmp_path))
        ).to_wire_mapping()["status"]
        == "success"
    )
    receiver.process_accepted_stream_messages()
    # No settlement has yet exposed the first failure. An additional accepted
    # batch cannot erase it even though its own native image mounts correctly.
    assert (
        receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()[
            "status"
        ]
        == "success"
    )
    receiver.process_accepted_stream_messages()
    settle(receiver)
    qtbot.waitUntil(
        lambda: settle(receiver)[1].phase is not ViewerSettlePhase.RUNNING, timeout=5000
    )
    response, progress = settle(receiver)
    assert progress.phase is ViewerSettlePhase.FAILED
    assert "channel" in response["message"]
    assert len(receiver.viewer.layers) == 1


def test_clear_state_discards_pre_route_failure(receiver, tmp_path):
    assert (
        receiver.accept_stream_message(
            wire_batch(saved_roi_item(tmp_path))
        ).to_wire_mapping()["status"]
        == "success"
    )
    receiver.process_accepted_stream_messages()
    receiver.clear_accumulated_stream_state()
    assert settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE
    assert receiver.layer_route_state.update_failure_message() is None


def test_active_settlement_rejects_admission_without_retaining_copies(
    receiver,
    monkeypatch,
):
    assert (
        receiver.accept_stream_message(wire_batch(image_item())).to_wire_mapping()[
            "status"
        ]
        == "success"
    )
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
    response = receiver.accept_stream_message(
        wire_batch(image_item())
    ).to_wire_mapping()
    assert response["status"] == "error"
    assert "active settlement" in response["message"]
    assert receiver.accepted_stream_batches.empty()
    assert receiver.layer_route_state.layer_settlement is settlement
    assert receiver.layer_route_state.update_failure_message() is None
    gc.collect()
    assert copied_arrays and all(reference() is None for reference in copied_arrays)
