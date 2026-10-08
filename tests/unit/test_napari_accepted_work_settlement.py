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
    ViewerControlMessageRequest,
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

    def send(item, **options):
        socket.send(wire_batch(item, **options))
        return socket.recv_json()

    try:
        yield send
    finally:
        receiver._running = False
        receiver.data_transport_pump.stop()
        socket.close(linger=0)
        context.term()
        remove_ipc_socket(receiver.port, receiver.config)


def wire_batch(item, *, producer=None, domains=None):
    items = item if isinstance(item, list) else [item]
    config = NapariDisplayConfig(channel_mode=NapariDimensionMode.LAYER)
    producer = producer or StreamProducerIdentity.pipeline_output(
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
            "component_value_domain": domains or {
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


def test_native_boolean_intensity_window_preserves_persisted_mask(
    receiver, wire_receiver, qtbot,
):
    """Actual stream/control sockets and Qt; optional retained engineering input."""
    import hashlib
    import tifffile
    from qtpy.QtCore import QTimer
    from openhcs.runtime.viewer_controls import ViewerIntensityWindowControlOptions
    from openhcs.runtime.viewer_protocol import ViewerRuntimeEndpoint

    mask_path = os.environ.get("OPENHCS_INTENSITY_QUALIFICATION_MASK")
    if mask_path:
        original = Path(mask_path).read_bytes()
        pixels = tifffile.imread(mask_path)
        assert pixels.dtype == np.bool_
    else:
        original = None
        pixels = np.array([[False, True], [True, False]])
    assert pixels.any() and not pixels.all()
    pixel_hash = hashlib.sha256(pixels.tobytes()).hexdigest()
    item = {**image_item(), "path": mask_path or "native_mask.tif",
            "data": pixels, "dtype": str(pixels.dtype), "shape": list(pixels.shape)}
    assert wire_receiver(item)["status"] == "success"
    receiver.process_accepted_stream_messages()
    settle(receiver)
    qtbot.waitUntil(lambda: settle(receiver)[1].phase is ViewerSettlePhase.COMPLETE, timeout=5000)
    route_key, = receiver.component_groups
    layer = receiver.layer_route_state.layer(route_key)
    native_pixels = layer.data
    assert native_pixels.dtype == np.bool_
    np.testing.assert_array_equal(native_pixels.reshape(-1), pixels.reshape(-1))
    original_step = receiver.viewer.dims.current_step
    receiver.control_transport_pump.start()
    service = QTimer()
    service.timeout.connect(receiver.process_messages)
    service.start(10)
    try:
        request = ViewerControlMessageRequest(
            ViewerRuntimeEndpoint(receiver.endpoint, receiver.config), "apply_intensity_window",
            ViewerIntensityWindowControlOptions(route_key=route_key, low_percentile=0, high_percentile=100),
            timeout=5,
        )
        with ThreadPoolExecutor(max_workers=1) as worker:
            future = worker.submit(request.send)
            qtbot.waitUntil(future.done, timeout=10000)
            response = future.result()
        assert response.succeeded(), response.payload
        assert tuple(response.payload["resolved_limits"]) == (0.0, 1.0)
        assert response.payload["contributing_pixel_count"] == pixels.size
        assert response.payload["matched_payload_count"] == 1
        assert tuple(layer.contrast_limits) == (0.0, 1.0)
        assert layer.data is native_pixels and layer.data.dtype == np.bool_
        assert receiver.viewer.dims.current_step == original_step
        assert hashlib.sha256(pixels.tobytes()).hexdigest() == pixel_hash
        if original is not None:
            assert Path(mask_path).read_bytes() == original
        print(f"native Boolean window: source={mask_path or 'synthetic'}; pixels={pixels.size}; "
              "control success; native limits=(0,1); dtype/navigation/source bytes preserved")
    finally:
        service.stop()
        receiver.control_transport_pump.stop()


def settle(receiver):
    response = NapariSettleControlMessageAction().handle(receiver, {})
    return response, ViewerSettleProgress.from_response(ViewerControlResponse(response))


@pytest.mark.skipif(not os.environ.get("OPENHCS_TRIANGULATION_QUALIFICATION_ROI"),
                    reason="Explicit retained-archive native qualification")
def test_native_compiled_triangulation_retains_archive_and_control(
    receiver, wire_receiver, qtbot, tmp_path,
):
    """All retained contours, original transport, native control and capture."""
    import hashlib
    from importlib.metadata import version
    from qtpy.QtCore import QTimer
    from napari.utils.triangulation_backend import get_backend, TriangulationBackend
    from napari.layers.shapes._shapes_models.polygon import Polygon
    from openhcs.core.roi_source_metadata import ROIArchiveSourceMetadata
    from openhcs.core.steps.stream_component_semantics import (
        StreamImagePayloadMetadataProjector, StreamViewerComponentMetadataProjector,
    )
    from openhcs.runtime.viewer_controls import ViewerStateControlOptions, ViewerNavigationControlOptions
    from openhcs.runtime.viewer_protocol import ViewerRuntimeEndpoint
    from openhcs.runtime.napari_streaming_handlers import NapariStreamLayerItem
    from openhcs.agent.dto.execution import ExecutionConnectionSpec
    from openhcs.agent.dto.viewer import ViewerWindowSnapshotRequest

    assert get_backend() is TriangulationBackend.fastest_available
    archive = Path(os.environ["OPENHCS_TRIANGULATION_QUALIFICATION_ROI"])
    original_hash = hashlib.sha256(archive.read_bytes()).hexdigest()
    rois = load_rois_from_zip(archive)
    source = ROIArchiveSourceMetadata.decode(rois)
    assert source is not None
    # The existing archive source owner separates transported source metadata
    # from feature rows, while preserving every parent/member and contour.
    shapes = NapariROIConverter.rois_to_shapes(ROIArchiveSourceMetadata.geometry(rois))
    largest = max(shapes, key=lambda row: len(row["coordinates"]))
    coordinates = np.asarray(largest["coordinates"], dtype=np.float32)
    started = time.perf_counter()
    polygon = Polygon(coordinates)
    polygon_seconds = time.perf_counter() - started
    assert polygon._set_meshes.__name__ == "_set_meshes_compiled_bermuda"
    np.testing.assert_array_equal(polygon.data, coordinates)
    triangles = polygon._face_vertices[polygon._face_triangles].astype(np.float64)
    u, v = triangles[:, 1] - triangles[:, 0], triangles[:, 2] - triangles[:, 0]
    mesh_area = np.abs(u[:, 0] * v[:, 1] - u[:, 1] * v[:, 0]).sum() / 2
    points = coordinates.astype(np.float64)
    polygon_area = abs(np.sum(points[:, 0] * np.roll(points[:, 1], -1)
                              - points[:, 1] * np.roll(points[:, 0], -1))) / 2
    # This retained contour was independently checked as simple, and its
    # original and projected regions coincide. Preserve the original raster
    # reference rather than recomputing it with the candidate triangulator.
    from skimage.draw import polygon as raster_polygon
    with np.load(os.environ["OPENHCS_TRIANGULATION_QUALIFICATION_COVERAGE"]) as coverage:
        np.testing.assert_array_equal(coordinates, coverage["projected"])
        expected_coverage = coverage["expected"]
    mesh_coverage = np.zeros_like(expected_coverage)
    for triangle in triangles:
        rows, columns = raster_polygon(
            triangle[:, 0], triangle[:, 1], shape=mesh_coverage.shape,
        )
        mesh_coverage[rows, columns] = True

    fields = StreamImagePayloadMetadataProjector.item_fields_for_plane_components(source, ())
    components = StreamViewerComponentMetadataProjector.for_item_fields(
        NapariDisplayConfig.COMPONENT_ORDER, fields,
    ).project_required(index=0, metadata=source.source_provenance.source_component_metadata)
    item = {"path": str(archive), "data_type": "shapes", "shapes": shapes,
            "metadata": components, **fields}
    assert wire_receiver(item)["status"] == "success"
    assert not receiver.accepted_stream_batches.empty()
    endpoint = ViewerRuntimeEndpoint(receiver.endpoint, receiver.config)
    receiver.control_transport_pump.start()
    service = QTimer()
    service.timeout.connect(receiver.process_accepted_stream_messages)
    service.timeout.connect(receiver.process_messages)
    service.start(10)
    receiver.viewer.show()
    latencies, pending_observations = [], 0
    started = time.perf_counter()
    with ThreadPoolExecutor(max_workers=1) as worker:
        def control(kind, payload=None):
            sent = time.perf_counter()
            future = worker.submit(ViewerControlMessageRequest(endpoint, kind, payload, timeout=5).send)
            while not future.done():
                qtbot.wait(10)
            response = future.result()
            assert response.succeeded(), response.payload
            latencies.append(time.perf_counter() - sent)
            return response

        try:
            while True:
                progress = ViewerSettleProgress.from_response(control("settle"))
                assert progress.phase is not ViewerSettlePhase.FAILED
                control("state", ViewerStateControlOptions(
                    include_component_values=False, include_payload_summaries=False,
                ))
                if progress.phase is ViewerSettlePhase.COMPLETE:
                    break
                pending_observations += 1
            native_seconds = time.perf_counter() - started
            assert pending_observations > 0
            print(f"native materialization completed: {len(shapes)} contours in {native_seconds:.3f}s; "
                  f"pending observations={pending_observations}; maximum state/settle latency={max(latencies):.3f}s", flush=True)
            route_key, = receiver.component_groups
            layer = receiver.layer_route_state.layer(route_key)
            assert len(layer.data) == len(shapes) == len(rois)
            for native, shape in zip(layer.data, shapes, strict=True):
                np.testing.assert_array_equal(native[:, -2:], np.asarray(shape["coordinates"], dtype=np.float32))
            for column in ("label", "area", "perimeter"):
                np.testing.assert_array_equal(layer.features[column],
                                              [shape["metadata"][column] for shape in shapes])
            identities = tuple(layer.features[NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE])
            assert len(set(identities)) == len(shapes)
            assert tuple(layer.scale[-2:]) == source.source_voxel_spacing.values_zyx[-2:]
            records = receiver.component_groups.existing_items_for(route_key)
            assert records[0].image_metadata.to_viewer_image_metadata() == source.to_viewer_image_metadata()
            assert all(model._set_meshes.__name__ == "_set_meshes_compiled_bermuda"
                       for model in layer._data_view.shapes)
            if os.environ.get("OPENHCS_SHAPE_ACTIVATION_QUALIFICATION"):
                original_models = tuple(layer._data_view.shapes)
                original_mesh = layer._data_view._mesh
                original_faces = tuple(model._face_vertices for model in original_models)
                original_edges = tuple(model._edge_vertices for model in original_models)
                original_order = tuple(receiver.viewer.dims.order)
                assert len(original_order) > 3
                reordered = (*reversed(original_order[:-2]), *original_order[-2:])
                assert reordered != original_order
                layer.selected_data = {0}
                activation_times = []

                def reorder():
                    activation_start = time.perf_counter()
                    receiver.viewer.dims.order = reordered
                    activation_times.append(time.perf_counter() - activation_start)

                # Actual native dimension activation, with a real control request
                # awaiting Qt at the same time; no delayed or mocked work.
                QTimer.singleShot(0, reorder)
                control("state", ViewerStateControlOptions(
                    include_component_values=False, include_payload_summaries=False,
                ))
                assert activation_times
                assert layer.selected_data == {0}
                assert tuple(layer._data_view.shapes) == original_models
                assert layer._data_view._mesh is original_mesh
                assert all(model._face_vertices is faces and model._edge_vertices is edges
                           for model, faces, edges in zip(original_models, original_faces, original_edges, strict=True))
                for visible in (False, True):
                    control("navigate", ViewerNavigationControlOptions(route_key=route_key, visible=visible))
                    assert layer.visible is visible
                assert layer.selected_data == {0}
                assert tuple(layer.features[NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE]) == identities
                for native, shape in zip(layer.data, shapes, strict=True):
                    np.testing.assert_array_equal(native[:, -2:], np.asarray(shape["coordinates"], dtype=np.float32))
                print(f"native retained-scene activation: hidden dimension reorder={activation_times[0]:.3f}s; "
                      f"visibility off/on and real state controls succeeded within original 5s budgets; "
                      f"{len(shapes)} contours, Shape/Mesh identities, face/edge geometry and selection retained", flush=True)
            snapshot = ViewerWindowSnapshotRequest.from_fields(
                connection=ExecutionConnectionSpec(port=receiver.port, transport_mode=receiver.transport_mode),
                output_dir_path=str(tmp_path),
            )
            response = control("screenshot", snapshot)
            assert tuple(layer.features[NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE]) == identities
            assert hashlib.sha256(archive.read_bytes()).hexdigest() == original_hash
            print(f"bermuda={version('bermuda')}; napari={version('napari')}; "
                  f"largest={len(coordinates)} vertices triangulated in {polygon_seconds:.3f}s; "
                  f"native all {len(shapes)} members in {native_seconds:.3f}s; "
                  f"pending observations={pending_observations}; control max={max(latencies):.3f}s; "
                  f"terminal={progress.completed_update_count}/{progress.total_update_count}; "
                  f"geometry/labels/features/calibration/source retained; snapshot={response.payload}")
            assert mesh_area == pytest.approx(polygon_area, rel=1e-5)
            np.testing.assert_array_equal(mesh_coverage, expected_coverage)
        finally:
            service.stop()
            receiver.control_transport_pump.stop()


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
    control_observation = []
    inspect_pending_control = os.environ.get("OPENHCS_SETTLEMENT_QUALIFICATION_CONTROL") == "true"

    def deliver():
        if late_observer or inspect_pending_control:
            deadline = time.monotonic() + 90
            while True:
                progress = receiver.layer_route_state.existing_settlement_progress()
                if (progress is not None and progress.active_route is not None
                        and progress.active_route_work_unit_active
                        and ((inspect_pending_control and receiver.layer_route_state.layers)
                             or (late_observer and "channel_2" in progress.active_route))):
                    break
                if late_observer and time.monotonic() >= deadline:
                    raise AssertionError("No real channel-2 native work was observed.")
                time.sleep(0.001)
        if inspect_pending_control:
            from openhcs.runtime.viewer_controls import ViewerNavigationControlOptions
            route = next(key for key in receiver.layer_route_state.layers if "channel_1" in key)
            native_layer = receiver.layer_route_state.layers[route]
            started = time.perf_counter()
            try:
                reply = ViewerControlMessageRequest(
                    client.runtime_endpoint, "navigate",
                    ViewerNavigationControlOptions(route_key=route, visible=False), timeout=0.1,
                ).send()
                assert not reply.succeeded()
            except zmq.Again:
                pass  # The caller's original observation budget expired.
            expired_after = time.perf_counter() - started
            started = time.perf_counter()
            progress = ViewerSettleProgress.from_response(ViewerControlMessageRequest(
                client.runtime_endpoint, "settle", timeout=2,
            ).send())
            control_observation.append((native_layer, expired_after, time.perf_counter() - started, progress))
            assert progress.phase is ViewerSettlePhase.RUNNING
        client_started.append(time.perf_counter())
        return client.settle_viewer_state(
            progress_callback=lambda progress: observations.append((time.perf_counter(), progress)),
        )

    def observe():
        control.send(pickle.dumps(ViewerControlMessageRequest(
            client.runtime_endpoint, "settle", timeout=2,
        ).to_wire_mapping()))
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
        if inspect_pending_control:
            native_layer, expired_after, settlement_reply_seconds, pending = control_observation[0]
            assert not native_layer.visible  # Expiry did not cancel the real Qt mutation.
            print(f"native control expired after {expired_after:.3f}s; subsequent settlement "
                  f"reply {settlement_reply_seconds:.3f}s; pending={pending}; "
                  "original navigation applied after observation expiry")
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


def test_native_sparse_raw_domain_expands_and_preserves_source_frame(
    receiver, wire_receiver, qtbot, tmp_path,
):
    """Author103's sparse manual -> full pipeline domain, through native transport."""
    from qtpy.QtCore import QTimer
    from polystore.streaming.identity import FixedStreamProducerIdentityKind
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
    from openhcs.core.source_metadata import SourceVoxelSpacing
    from openhcs.runtime.viewer_controls import ViewerNavigationControlOptions, ViewerRoutedImageControlOptions
    from openhcs.runtime.napari_viewer_server import NapariMountedRouteControlMessageAction
    from openhcs.runtime.napari_streaming_handlers import NapariStreamLayerItem
    from openhcs.agent.dto.execution import ExecutionConnectionSpec
    from openhcs.agent.dto.viewer import ViewerWindowSnapshotRequest
    from openhcs.runtime.viewer_protocol import ViewerRuntimeEndpoint

    domains = {"site": [1, 3, 9], "channel": [1, 2], "z_index": [1],
               "timepoint": [1], "well": ["A01", "A02", "A03", "A04"]}
    selected = (("A01", 1), ("A02", 3), ("A03", 9), ("A04", 1))
    calibration = ImagePayloadMetadata(source_voxel_spacing=SourceVoxelSpacing((0.65, 0.65))).to_viewer_image_metadata()
    manual = StreamProducerIdentity.fixed_output(FixedStreamProducerIdentityKind.MANUAL, "selected_images_sparse")
    raw = [{"path": f"{well}_s{site}_w{channel}.tif", "data_type": "image",
            "data": np.full((16, 16), index * 10 + channel - 1, dtype=np.uint16).tolist(),
            "dtype": "uint16", "shape": [16, 16], "image_metadata": calibration,
            "metadata": {"well": well, "site": site, "channel": channel, "z_index": 1, "timepoint": 1}}
           for index, (well, site) in enumerate(selected) for channel in (1, 2)]
    endpoint = ViewerRuntimeEndpoint(receiver.endpoint, receiver.config)
    receiver.control_transport_pump.start()
    service = QTimer()
    service.timeout.connect(receiver.process_accepted_stream_messages)
    service.timeout.connect(receiver.process_messages)
    service.start(20)
    receiver.viewer.show()
    with ThreadPoolExecutor(max_workers=1) as worker:
        def control(kind, payload=None, timeout=5):
            future = worker.submit(ViewerControlMessageRequest(endpoint, kind, payload, timeout=timeout).send)
            while not future.done():
                qtbot.wait(20)
            return future.result()

        def terminal():
            while True:
                progress = ViewerSettleProgress.from_response(control("settle"))
                if progress.phase is ViewerSettlePhase.COMPLETE:
                    return progress
                assert progress.phase is ViewerSettlePhase.RUNNING
                qtbot.wait(20)

        try:
            assert wire_receiver(raw, producer=manual, domains=domains)["status"] == "success"
            terminal()
            raw_routes = {receiver.component_groups.existing_items_for(route)[0].address.components["channel"]: route
                          for route in receiver.layer_route_state.layers}
            primary, hidden = raw_routes[1], raw_routes[2]
            old_items = tuple(receiver.component_groups.existing_items_for(primary))
            source_buffers = tuple(item.data for item in old_items)
            raw_layer = receiver.layer_route_state.layer(primary)
            assert raw_layer.data.shape[:4] == (3, 1, 1, 4)
            raw_layer.contrast_limits, raw_layer.gamma, raw_layer.opacity = (0, 50), 0.8, 0.45
            receiver.layer_route_state.layer(hidden).visible = False
            assert control("navigate", ViewerNavigationControlOptions(
                route_key=primary, axis_indices={"site": 2, "well": 2}, selected=True,
            )).succeeded()
            geometry_routes = []
            for kind in ("points", "shapes"):
                row = {"path": f"A03_s9_{kind}.roi.zip", "data_type": kind,
                       "image_metadata": calibration, "metadata": {**raw[0]["metadata"], "well": "A03", "site": 9},
                       "shapes": [{"type": "points" if kind == "points" else "path",
                                   "coordinates": [[4, 4]] if kind == "points" else [[4, 4], [8, 8]],
                                   "metadata": {"label": 7}}]}
                assert wire_receiver(row, producer=StreamProducerIdentity.fixed_output(
                    FixedStreamProducerIdentityKind.MANUAL, f"selected_{kind}",
                ), domains=domains)["status"] == "success"
                terminal()
                route = next(key for key in receiver.layer_route_state.layers if f"selected_{kind}" in key)
                assert control("navigate", ViewerNavigationControlOptions(route_key=route, data_index=0, selected=True)).succeeded()
                layer = receiver.layer_route_state.layer(route)
                assert layer.selected_data == {0}
                layer.visible = kind == "shapes"
                geometry_routes.append((route, tuple(layer.features[NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE])))
            assert control("navigate", ViewerNavigationControlOptions(
                route_key=primary, axis_indices={"site": 2, "well": 2}, selected=True,
            )).succeeded()
            full_domains = {**domains, "site": list(range(1, 10))}
            normalized = [{**row, "path": f"normalized_{well}_s{site}.tif",
                           "data": np.full((16, 16), site / 10).tolist(), "dtype": "float32",
                           "metadata": {**row["metadata"], "well": well, "site": site, "channel": 1}}
                          for well in domains["well"] for site in full_domains["site"] for row in raw[:1]]
            assert wire_receiver(normalized, domains=full_domains)["status"] == "success"
            final = terminal()
            raw_layer = receiver.layer_route_state.layer(primary)
            state = receiver.layer_route_state.dimension_state_for(primary)
            assert raw_layer.data.shape[:4] == (9, 1, 1, 4)
            assert receiver.viewer.dims.current_step[0] == 8  # Source Site9, not old ordinal2.
            assert receiver.viewer.dims.current_step[3] == 2
            assert receiver.display_pipeline.native_frame_applied(include_hidden=True)
            assert not receiver.layer_route_state.layer(hidden).visible
            assert tuple(raw_layer.contrast_limits) == (0, 50) and raw_layer.gamma == 0.8 and raw_layer.opacity == 0.45
            assert tuple(raw_layer.scale[-2:]) == (0.65, 0.65)
            assert tuple(receiver.component_groups.existing_items_for(primary)) == old_items
            assert all(item.data is source for item, source in zip(old_items, source_buffers, strict=True))
            assert np.max(raw_layer._data_view) == 20
            for route, identities in geometry_routes:
                layer = receiver.layer_route_state.layer(route)
                assert layer.selected_data == {0}
                assert tuple(layer.features[NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE]) == identities
                assert tuple(layer.scale[-2:]) == (0.65, 0.65)
                assert layer.visible == ("selected_shapes" in route)
            # Real black source and unavailable padded frame are not the same record.
            def records(site):
                return NapariMountedRouteControlMessageAction.matched_image_records(
                    list(old_items), state, ViewerRoutedImageControlOptions(
                        route_key=primary, axis_indices={"site": site, "well": 0},
                    ),
                )
            assert len(records(0)) == 1 and np.count_nonzero(records(0)[0][1]) == 0
            assert not records(1)
            snapshot = ViewerWindowSnapshotRequest.from_fields(
                connection=ExecutionConnectionSpec(port=receiver.port, transport_mode=receiver.transport_mode),
                output_dir_path=str(tmp_path),
            )
            assert control("screenshot", snapshot).succeeded()
            print(f"native sparse->full: component shape3x1x1x4->9x1x1x4; source Site9/wellA03 retained; "
                  f"raw buffers unchanged; hidden route/calibration/presentation retained; "
                  f"black source=1 record, missing frame=0; snapshot saved; terminal={final.completed_update_count}/{final.total_update_count}")
        finally:
            service.stop()
            receiver.control_transport_pump.stop()


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
