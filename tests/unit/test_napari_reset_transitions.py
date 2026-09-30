"""Real Qt scheduling and native Napari model transitions, no server or GL canvas."""

import threading

import numpy as np
import pytest
from napari.components import ViewerModel
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming_constants import StreamingDataType
from qtpy.QtCore import QEventLoop, QTimer
from qtpy.QtWidgets import QApplication

from openhcs.core.config import NapariDimensionMode, NapariDisplayConfig, NapariVariableSizeHandling
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_metadata import SourceVoxelSpacing
from openhcs.runtime.napari_streaming_handlers import (
    NapariBatchProcessorStore,
    NapariComponentGroupStore,
    NapariLayerBatchDebouncePolicy,
    NapariLayerRouteStateStore,
    NapariStreamLayerAddress,
)
from openhcs.runtime.napari_viewer_server import (
    NapariComponentAwareDisplayCoordinator,
    NapariImagePayloadLayoutRole,
    NapariLayerDisplayPipeline,
    NapariShapesLayerDisplayHandler,
    NapariResultSelectionController,
    NapariStreamLayerContext,
    NapariViewerServer,
)
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsAuthority,
    ViewerComponentNameMetadata,
    ViewerComponentValueDomainPayload,
    ViewerMappingDisplayConfigInput,
    ViewerRouteComponentValueTracker,
)


@pytest.fixture
def receiver():
    app = QApplication.instance() or QApplication([])
    server = NapariViewerServer.__new__(NapariViewerServer)
    server.viewer = ViewerModel()
    server.replace_layers = False
    server.layer_route_state = NapariLayerRouteStateStore.empty()
    server.component_groups = NapariComponentGroupStore()
    server.component_values = ViewerRouteComponentValueTracker()
    server.component_name_metadata = ViewerComponentNameMetadata.empty()
    server.layer_update_lock = threading.Lock()
    server.layer_batch_processor_debounce_policy = NapariLayerBatchDebouncePolicy()
    server.batch_processors = NapariBatchProcessorStore()
    server.display_pipeline = NapariLayerDisplayPipeline(server)
    # Exercise native selection event binding, without mounting an unrelated Qt dock.
    server.result_selection_controller = NapariResultSelectionController(server)
    server.bind_result_selection_layer = server.result_selection_controller.bind
    yield server
    server.layer_route_state.drain_pending_updates()
    server.display_pipeline.clear_display_work()
    server.viewer.layers.clear()
    app.processEvents()


def enqueue(server, data, *, well="A01", producer="image", data_type=StreamingDataType.IMAGE,
            spacing=0.65, domain=None):
    config = NapariDisplayConfig(
        well_mode=NapariDimensionMode.STACK,
        site_mode=NapariDimensionMode.LAYER,
        channel_mode=NapariDimensionMode.LAYER,
        z_index_mode=NapariDimensionMode.LAYER,
        timepoint_mode=NapariDimensionMode.LAYER,
        variable_size_handling=NapariVariableSizeHandling.PAD_TO_MAX,
    )
    semantics = ViewerComponentAxisSemanticsAuthority.from_display_config(
        ViewerMappingDisplayConfigInput({"component_modes": config.component_modes(), "component_order": config.COMPONENT_ORDER}),
        ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
            {"well": domain or [well]}, context="synthetic transition"
        ),
    )
    context = NapariStreamLayerContext(
        entries=semantics.entries,
        layout=semantics.layout,
        producer=StreamProducerIdentity.pipeline_output(
            output_kind="main", output_key=producer, projection_key=producer,
            step_name=producer, pipeline_position=0,
        ),
        address=NapariStreamLayerAddress({"well": well, "site": 1, "channel": 1, "z_index": 1, "timepoint": 1}, f"{well}.tif", data_type),
        image_metadata=ImagePayloadMetadata(source_voxel_spacing=SourceVoxelSpacing((spacing, spacing))),
        plane_component_domain=ViewerComponentValueDomainPayload(()),
        display_config=config,
    )
    NapariComponentAwareDisplayCoordinator().display(data=data, stream_layer_context=context, server=server)
    route = context.layer_route(
        payload_layout_role=NapariImagePayloadLayoutRole.for_stream_layer_context(context),
        layer_route_state=server.layer_route_state,
    ).route_key
    return route, server.layer_route_state.pending_update_for(route)


def advance_in_qt(server, route, update, after=lambda: None):
    """Execute one real single-shot Qt callback and interrupt before its continuation."""
    loop = QEventLoop()
    errors = []

    def callback():
        try:
            update.stop_timer()
            server.display_pipeline.execute_scheduled_layer_update(route, update)
            server.layer_route_state.require_updates_succeeded()
            after()
        except BaseException as error:
            errors.append(error)
        finally:
            loop.quit()

    QTimer.singleShot(0, callback)
    loop.exec()
    if errors:
        raise errors[0]


@pytest.mark.parametrize("replace_layers", [False, True])
def test_clear_before_replacement_keeps_settled_pixels_inventory_and_calibration(receiver, replace_layers):
    receiver.replace_layers = replace_layers
    a = np.full((2, 2), 3, dtype=np.uint16)
    route, update = enqueue(receiver, a)
    advance_in_qt(receiver, route, update)
    native_a = receiver.layer_route_state.layer(route)
    items_a = receiver.component_groups.existing_items_for(route)
    domain_a = receiver.component_values.domain_for(route, ["well"])
    route_b, pending_b = enqueue(receiver, np.full((2, 2), 9, dtype=np.uint16), spacing=1.25, domain=["A01", "A14"])
    assert route_b == route
    receiver.clear_accumulated_stream_state()
    assert receiver.layer_route_state.layer(route) is native_a
    assert receiver.component_groups.existing_items_for(route)[0].data is a
    assert receiver.component_groups.existing_items_for(route) is items_a
    assert receiver.component_values.domain_for(route, ["well"]) is domain_a
    assert receiver.component_values.shared_values_for(["well"]) == {"well": ["A01"]}
    np.testing.assert_array_equal(native_a.data.squeeze(), a)
    assert tuple(native_a.scale[-2:]) == (0.65, 0.65)
    # A cancelled generation cannot publish from a callback already queued in Qt.
    advance_in_qt(receiver, route, pending_b)
    assert receiver.layer_route_state.layer(route) is native_a
    assert not receiver.layer_route_state.layer_pending_updates


def test_clear_between_replacement_shapes_chunks_preserves_settled_native_layer(receiver, monkeypatch):
    monkeypatch.setattr(NapariShapesLayerDisplayHandler, "MAX_SHAPES_PER_WORK_UNIT", 1)
    a = [{"type": "polygon", "coordinates": [[0, 0], [0, 1], [1, 1]], "metadata": {"label": 1}}]
    route, update_a = enqueue(receiver, a, producer="roi", data_type=StreamingDataType.SHAPES)
    advance_in_qt(receiver, route, update_a)
    native_a = receiver.layer_route_state.layer(route)
    items_a = receiver.component_groups.existing_items_for(route)
    domain_a = receiver.component_values.domain_for(route, ["well"])
    route_b, update_b = enqueue(receiver, a * 3, producer="roi", data_type=StreamingDataType.SHAPES,
                              spacing=1.25, domain=["A01", "A14"])
    assert route_b == route
    advance_in_qt(receiver, route, update_b, receiver.clear_accumulated_stream_state)
    assert receiver.layer_route_state.layer(route) is native_a
    assert receiver.component_groups.existing_items_for(route) is items_a
    assert native_a.visible and len(native_a.data) == 1
    assert tuple(native_a.scale[-2:]) == (0.65, 0.65)
    assert receiver.component_values.domain_for(route, ["well"]) is domain_a
    assert receiver.component_values.shared_values_for(["well"]) == {"well": ["A01"]}
    advance_in_qt(receiver, route, update_b)
    assert receiver.layer_route_state.layer(route) is native_a


def test_completed_shapes_publish_full_inventory_and_declared_domain(receiver, monkeypatch):
    monkeypatch.setattr(NapariShapesLayerDisplayHandler, "MAX_SHAPES_PER_WORK_UNIT", 1)
    shapes = [{"type": "polygon", "coordinates": [[0, 0], [0, 1], [1, 1]], "metadata": {"label": 1}}] * 3
    route, update = enqueue(receiver, shapes, producer="roi", data_type=StreamingDataType.SHAPES,
                            domain=["A01", "A02"])
    advance_in_qt(receiver, route, update)
    assert not receiver.viewer.layers
    assert not receiver.component_values.domains
    advance_in_qt(receiver, route, update)
    assert not receiver.viewer.layers
    advance_in_qt(receiver, route, update)
    layer = receiver.layer_route_state.layer(route)
    assert layer.visible and len(layer.data) == len(layer.features) == 3
    assert receiver.component_groups.existing_items_for(route)[0].data is shapes
    receiver.clear_accumulated_stream_state()
    assert receiver.layer_route_state.layer(route) is layer
    assert receiver.component_values.shared_values_for(["well"]) == {"well": ["A01", "A02"]}


def test_clear_between_shapes_chunks_does_not_retain_partial_native_payload(receiver, monkeypatch):
    monkeypatch.setattr(NapariShapesLayerDisplayHandler, "MAX_SHAPES_PER_WORK_UNIT", 1)
    shapes = [
        {"type": "polygon", "coordinates": [[0, 0], [0, 1], [1, 1]], "metadata": {"label": index}}
        for index in range(1, 4)
    ]
    route, update = enqueue(receiver, shapes, producer="roi", data_type=StreamingDataType.SHAPES)
    advance_in_qt(receiver, route, update, receiver.clear_accumulated_stream_state)
    assert not receiver.viewer.layers
    assert not receiver.layer_route_state.layers
    assert not receiver.component_groups.groups
    assert not receiver.component_values.domains
    advance_in_qt(receiver, route, update)
    assert not receiver.viewer.layers


def test_native_deletion_then_clear_reprojects_surviving_shared_axis(receiver):
    route_a, update_a = enqueue(receiver, np.ones((2, 2)), well="A01", producer="a")
    advance_in_qt(receiver, route_a, update_a)
    route_b, update_b = enqueue(receiver, np.full((2, 2), 2), well="A02", producer="b")
    advance_in_qt(receiver, route_b, update_b)
    native_b = receiver.layer_route_state.layer(route_b)
    assert native_b.translate[0] == 1
    receiver.viewer.layers.selection.active = native_b
    receiver.viewer.layers.remove(receiver.layer_route_state.layer(route_a))
    receiver.clear_accumulated_stream_state()
    assert receiver.component_values.shared_values_for(["well"]) == {"well": ["A02"]}
    assert native_b.translate[0] == 0
    presentation = receiver.layer_route_state.dimension_state_for(route_b).presentation
    assert presentation.axis_offset(0) == 0
    assert receiver.viewer.layers.selection.active is native_b
    assert tuple(native_b.scale[-2:]) == (0.65, 0.65)
