"""Real Qt scheduling and native Napari model transitions, no server or GL canvas."""

import threading
import asyncio
import pickle
import queue
import weakref
from contextlib import contextmanager
from dataclasses import replace

import numpy as np
import pytest
from napari.components import ViewerModel
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming_constants import StreamingDataType
from qtpy.QtCore import QEventLoop, QTimer
from qtpy.QtWidgets import QApplication

from openhcs.core.config import (
    NapariDimensionMode,
    NapariDisplayConfig,
    NapariVariableSizeHandling,
)
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
    NapariAcceptedControlRequest,
    NapariControlMessageAction,
    NapariComponentAwareDisplayCoordinator,
    NapariImagePayloadLayoutRole,
    NapariLayerDisplayPipeline,
    NapariImageLayerDisplayHandler,
    NapariImagePresentationRetention,
    NapariShapesLayerDisplayHandler,
    NapariPointsLayerDisplayHandler,
    NapariSelectablePresentationRetention,
    NapariNavigationControlMessageAction,
    NapariResultSelectionController,
    NapariResultSelectionGroupBinding,
    NapariStreamLayerContext,
    NapariViewerServer,
)
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.core.artifacts import ObjectArtifactSubjectBinding
from openhcs.runtime.napari_streaming_handlers import NapariStreamLayerItem
from openhcs.agent.dto.viewer import ViewerWindowLayerRetirementRequest
from openhcs.agent.services.viewer_window_service import (
    ViewerWindowService, ZMQViewerWindowGateway,
)
from openhcs.runtime.viewer_controls import (
    ViewerLayerRetirementControlOptions, ViewerNavigationControlOptions,
    ViewerPointCoordinateAuthority,
)
from openhcs.core.roi_point_metadata import ROIFractionalZ
from openhcs.runtime.viewer_protocol import (
    OpenHCSViewerControlMessageType, ViewerSettlePhase,
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
    server.accepted_stream_batches = queue.Queue()
    server.accepted_control_requests = queue.Queue()
    # Exercise native selection event binding, without mounting an unrelated Qt dock.
    server.result_selection_controller = NapariResultSelectionController(server)
    server.bind_result_selection_layer = server.result_selection_controller.bind
    yield server
    server.layer_route_state.drain_pending_updates()
    server.display_pipeline.clear_display_work()
    server.viewer.layers.clear()
    app.processEvents()


def enqueue(
    server,
    data,
    *,
    well="A01",
    producer="image",
    data_type=StreamingDataType.IMAGE,
    spacing=0.65,
    domain=None,
    z_domain=None,
    z_index=1,
):
    config = NapariDisplayConfig(
        well_mode=NapariDimensionMode.STACK,
        site_mode=NapariDimensionMode.LAYER,
        channel_mode=NapariDimensionMode.LAYER,
        z_index_mode=(NapariDimensionMode.STACK if z_domain else NapariDimensionMode.LAYER),
        timepoint_mode=NapariDimensionMode.LAYER,
        variable_size_handling=NapariVariableSizeHandling.PAD_TO_MAX,
    )
    semantics = ViewerComponentAxisSemanticsAuthority.from_display_config(
        ViewerMappingDisplayConfigInput(
            {
                "component_modes": config.component_modes(),
                "component_order": config.COMPONENT_ORDER,
            }
        ),
        ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
            {"well": domain or [well], **({"z_index": z_domain} if z_domain else {})},
            context="synthetic transition"
        ),
    )
    context = NapariStreamLayerContext(
        entries=semantics.entries,
        layout=semantics.layout,
        producer=StreamProducerIdentity.pipeline_output(
            output_kind="main",
            output_key=producer,
            projection_key=producer,
            step_name=producer,
            pipeline_position=0,
        ),
        address=NapariStreamLayerAddress(
            {"well": well, "site": 1, "channel": 1, "z_index": z_index, "timepoint": 1},
            f"{well}.tif",
            data_type,
        ),
        image_metadata=ImagePayloadMetadata(
            source_voxel_spacing=SourceVoxelSpacing((spacing, spacing))
        ),
        plane_component_domain=ViewerComponentValueDomainPayload(()),
        display_config=config,
    )
    NapariComponentAwareDisplayCoordinator().display(
        data=data, stream_layer_context=context, server=server
    )
    route = context.layer_route(
        payload_layout_role=NapariImagePayloadLayoutRole.for_stream_layer_context(
            context
        ),
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
def test_clear_before_replacement_keeps_settled_pixels_inventory_and_calibration(
    receiver, replace_layers
):
    receiver.replace_layers = replace_layers
    a = np.full((2, 2), 3, dtype=np.uint16)
    route, update = enqueue(receiver, a)
    advance_in_qt(receiver, route, update)
    native_a = receiver.layer_route_state.layer(route)
    items_a = receiver.component_groups.existing_items_for(route)
    domain_a = receiver.component_values.domain_for(route, ["well"])
    route_b, pending_b = enqueue(
        receiver,
        np.full((2, 2), 9, dtype=np.uint16),
        spacing=1.25,
        domain=["A01", "A14"],
    )
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


def test_clear_between_replacement_shapes_chunks_preserves_settled_native_layer(
    receiver, monkeypatch
):
    monkeypatch.setattr(NapariShapesLayerDisplayHandler, "MAX_SHAPES_PER_WORK_UNIT", 1)
    a = [
        {
            "type": "polygon",
            "coordinates": [[0, 0], [0, 1], [1, 1]],
            "metadata": {"label": 1},
        }
    ]
    route, update_a = enqueue(
        receiver, a, producer="roi", data_type=StreamingDataType.SHAPES
    )
    advance_in_qt(receiver, route, update_a)
    native_a = receiver.layer_route_state.layer(route)
    items_a = receiver.component_groups.existing_items_for(route)
    domain_a = receiver.component_values.domain_for(route, ["well"])
    route_b, update_b = enqueue(
        receiver,
        a * 3,
        producer="roi",
        data_type=StreamingDataType.SHAPES,
        spacing=1.25,
        domain=["A01", "A14"],
    )
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


def test_completed_shapes_publish_full_inventory_and_declared_domain(
    receiver, monkeypatch
):
    monkeypatch.setattr(NapariShapesLayerDisplayHandler, "MAX_SHAPES_PER_WORK_UNIT", 1)
    shapes = [
        {
            "type": "polygon",
            "coordinates": [[0, 0], [0, 1], [1, 1]],
            "metadata": {"label": 1},
        }
    ] * 3
    route, update = enqueue(
        receiver,
        shapes,
        producer="roi",
        data_type=StreamingDataType.SHAPES,
        domain=["A01", "A02"],
    )
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
    assert receiver.component_values.shared_values_for(["well"]) == {
        "well": ["A01", "A02"]
    }


def test_clear_between_shapes_chunks_does_not_retain_partial_native_payload(
    receiver, monkeypatch
):
    monkeypatch.setattr(NapariShapesLayerDisplayHandler, "MAX_SHAPES_PER_WORK_UNIT", 1)
    shapes = [
        {
            "type": "polygon",
            "coordinates": [[0, 0], [0, 1], [1, 1]],
            "metadata": {"label": index},
        }
        for index in range(1, 4)
    ]
    route, update = enqueue(
        receiver, shapes, producer="roi", data_type=StreamingDataType.SHAPES
    )
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


def test_pruning_interior_shared_value_rematerializes_from_settled_items(receiver):
    middle, update = enqueue(
        receiver, np.full((2, 2), 2), well="A02", producer="middle"
    )
    advance_in_qt(receiver, middle, update)
    left = np.full((2, 2), 1)
    right = np.full((2, 2), 3)
    sparse, _ = enqueue(
        receiver, left, well="A01", producer="sparse", domain=["A01", "A03"]
    )
    same_route, update = enqueue(
        receiver, right, well="A03", producer="sparse", domain=["A01", "A03"]
    )
    assert same_route == sparse
    advance_in_qt(receiver, sparse, update)
    old_native = receiver.layer_route_state.layer(sparse)
    original_items = receiver.component_groups.existing_items_for(sparse)
    original_policy = receiver.layer_route_state.dimension_state_for(
        sparse
    ).display_config
    assert old_native.data.shape == (3, 2, 2)
    receiver.viewer.layers.selection.active = old_native
    receiver.viewer.layers.remove(receiver.layer_route_state.layer(middle))
    receiver.clear_accumulated_stream_state()
    native = receiver.layer_route_state.layer(sparse)
    assert native is not old_native and old_native not in receiver.viewer.layers
    assert receiver.component_groups.existing_items_for(sparse) is original_items
    assert native.data.shape == (2, 2, 2)
    np.testing.assert_array_equal(native.data[0], left)
    np.testing.assert_array_equal(native.data[1], right)
    assert receiver.viewer.layers.selection.active is native
    assert tuple(native.scale[-2:]) == (0.65, 0.65)
    assert (
        receiver.layer_route_state.dimension_state_for(sparse).display_config
        is original_policy
    )
    assert receiver.component_values.shared_values_for(["well"]) == {
        "well": ["A01", "A03"]
    }
    receiver.clear_accumulated_stream_state()
    assert receiver.layer_route_state.layer(sparse) is native


def test_native_deletion_with_queued_replacement_clear_cannot_resurrect_route(receiver):
    route, update_a = enqueue(receiver, np.ones((2, 2)))
    advance_in_qt(receiver, route, update_a)
    _, update_b = enqueue(receiver, np.full((2, 2), 9))
    receiver.viewer.layers.remove(receiver.layer_route_state.layer(route))
    receiver.clear_accumulated_stream_state()
    advance_in_qt(receiver, route, update_b)
    assert not receiver.viewer.layers
    assert not receiver.layer_route_state.layers
    assert not receiver.layer_route_state.layer_titles
    assert not receiver.component_groups.groups
    assert not receiver.component_values.domains


def retirement_request(server, *routes):
    return ViewerWindowLayerRetirementRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584),
        expected_producers={
            route: [producer.to_payload() for producer in
                    server.component_groups.producer_identities_for(route)]
            for route in routes
        },
    )


class QueuedRetirementGateway(ZMQViewerWindowGateway):
    """Exercise the real gateway message hook and Qt queue, with no socket/server."""

    def __init__(self, server):
        self.server = server

    def _send_control_message(self, request, message):
        assert request.operation_deadline is not None
        assert request.control_deadline() is request.operation_deadline
        reply = queue.Queue(maxsize=1)
        self.server.accepted_control_requests.put(NapariAcceptedControlRequest(
            pickle.loads(pickle.dumps(message)), reply,
        ))
        loop = QEventLoop()
        def dispatch():
            self.server.process_messages()
            loop.quit()
        QTimer.singleShot(0, dispatch)
        loop.exec()
        response = pickle.loads(reply.get_nowait())
        assert reply.empty()
        return response


def test_selected_retirement_uses_registered_queue_and_releases_payloads(receiver):
    raw = np.full((2, 2), 4, dtype=np.uint16)
    keep, update = enqueue(receiver, raw, producer="raw")
    advance_in_qt(receiver, keep, update)
    doomed = np.full((2, 2), 9, dtype=np.uint16)
    payload_ref = weakref.ref(doomed)
    route, update = enqueue(receiver, doomed, producer="candidate")
    # Genuine original terminal settlement, not a manually fabricated complete flag.
    receiver.display_pipeline.settlement_progress()
    app = QApplication.instance()
    while receiver.layer_route_state.existing_settlement_progress().phase is ViewerSettlePhase.RUNNING:
        app.processEvents()
    assert receiver.layer_route_state.existing_settlement_progress().phase is ViewerSettlePhase.COMPLETE
    native = receiver.layer_route_state.layer(route)
    native_ref = weakref.ref(native)
    receiver.batch_processors.get_or_create(layer_key=route, napari_server=receiver)
    request = retirement_request(receiver, route)
    keep_native = receiver.layer_route_state.layer(keep)
    original_items = receiver.component_groups.existing_items_for(keep)
    del update, doomed, native
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(request)
    assert result.applied and not result.errors and result.observed
    assert result.retired_route_keys == (route,)
    assert result.remaining_route_keys == (keep,)
    assert route not in receiver.layer_route_state.layer_titles
    assert route not in receiver.layer_route_state.layer_dimension_states
    assert route not in receiver.batch_processors.processors
    assert route not in receiver.component_groups.groups
    assert not any(key[0] == route for key in receiver.component_values.domains)
    assert not receiver.layer_route_state.layer_settlement.updates
    assert receiver.layer_route_state.layer(keep) is keep_native
    assert receiver.component_groups.existing_items_for(keep) is original_items
    assert original_items[0].data is raw
    import gc
    gc.collect()
    assert payload_ref() is None and native_ref() is None
    app.processEvents()
    assert route not in receiver.layer_route_state.layers  # No late resurrection.


def test_real_fastmcp_retirement_decodes_identity_and_reaches_native_queue(receiver):
    from mcp.server.fastmcp.exceptions import ToolError
    from openhcs.mcp.context import OpenHCSAgentContext
    from openhcs.mcp.server import build_server

    raw = np.ones((2, 2), dtype=np.uint16)
    keep, update = enqueue(receiver, raw, producer='raw')
    advance_in_qt(receiver, keep, update)
    route, update = enqueue(receiver, np.full((2, 2), 9), producer='retired')
    advance_in_qt(receiver, route, update)
    keep_native = receiver.layer_route_state.layer(keep)
    context = OpenHCSAgentContext(
        viewer_window_service=ViewerWindowService(QueuedRetirementGateway(receiver)),
    )
    mcp = build_server(context=context)
    tool = mcp._tool_manager.get_tool('openhcs_retire_viewer_window_layers')
    arguments = retirement_request(receiver, route).as_tool_arguments()
    # Invalid schema never enters the native queue or mutates either layer.
    with pytest.raises(ToolError):
        asyncio.run(tool.run({**arguments, 'expected_producers': {route: [{}]}}))
    assert receiver.accepted_control_requests.empty()
    assert receiver.layer_route_state.layer(route) is not None
    assert receiver.layer_route_state.layer(keep) is keep_native
    result = asyncio.run(tool.run(arguments))
    assert result['applied'] and result['observed'] and not result['errors']
    assert result['retired_route_keys'] == [route]
    assert result['remaining_route_keys'] == [keep]
    assert receiver.layer_route_state.layer(keep) is keep_native
    assert receiver.component_groups.existing_items_for(keep)[0].data is raw
    assert route not in receiver.layer_route_state.layers


@pytest.mark.parametrize("data_type,payload", [
    (StreamingDataType.SHAPES, [{"type": "polygon", "coordinates": [[0, 0], [0, 1], [1, 1]],
                                "metadata": {"label": 7}}]),
    (StreamingDataType.POINTS, [{"type": "points", "coordinates": [[1, 2]],
                                "metadata": {"label": 7}}]),
])
def test_registered_geometry_family_retires_through_same_queue(receiver, data_type, payload):
    keep, update = enqueue(receiver, np.ones((2, 2)), producer="source")
    advance_in_qt(receiver, keep, update)
    original_items = receiver.component_groups.existing_items_for(keep)
    route, update = enqueue(receiver, payload, producer="geometry", data_type=data_type)
    advance_in_qt(receiver, route, update)
    layer_ref = weakref.ref(receiver.layer_route_state.layer(route))
    update_ref = weakref.ref(update)
    del update
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(
        retirement_request(receiver, route),
    )
    assert result.applied and not result.errors
    assert result.retired_route_keys == (route,) and result.remaining_route_keys == (keep,)
    assert receiver.component_groups.existing_items_for(keep) is original_items
    import gc
    gc.collect()
    assert layer_ref() is None and update_ref() is None
    QApplication.instance().processEvents()
    assert route not in receiver.layer_route_state.layers


@pytest.mark.parametrize("blocked", ["pending", "intake", "display", "running", "stale", "missing", "deadline"])
def test_retirement_prevalidates_entire_set_without_collateral_mutation(receiver, blocked):
    first, update = enqueue(receiver, np.ones((2, 2)), producer="first")
    advance_in_qt(receiver, first, update)
    second, update = enqueue(receiver, np.full((2, 2), 2), producer="second")
    advance_in_qt(receiver, second, update)
    request = retirement_request(receiver, first, second)
    if blocked == "pending":
        enqueue(receiver, np.full((2, 2), 3), producer="second")
    elif blocked == "intake":
        receiver.accepted_stream_batches.put(object())
    elif blocked == "display":
        receiver.display_pipeline._display_work_by_route[second] = (update, object())
    elif blocked == "running":
        enqueue(receiver, np.full((2, 2), 3), producer="second")
        receiver.layer_route_state.begin_settlement()
    elif blocked == "stale":
        items = receiver.component_groups.existing_items_for(second)
        items[0] = replace(items[0], producer=replace(items[0].producer, invocation_key="new-incarnation"))
    elif blocked == "missing":
        expected = dict(request.retirement.expected_producers)
        expected["foreign"] = expected[second]
        request = replace(request, retirement=ViewerLayerRetirementControlOptions(expected_producers=expected))
    elif blocked == "deadline":
        from zmqruntime.timeouts import OperationDeadline
        request = replace(request, operation_deadline=OperationDeadline("expired", 5000, 0))
    layers = tuple(receiver.viewer.layers)
    groups = dict(receiver.component_groups.groups)
    response = NapariControlMessageAction.for_message_type(
        OpenHCSViewerControlMessageType.RETIRE_LAYERS.value,
    ).handle(receiver, {"payload": request})
    assert response["status"] == "error"
    assert tuple(receiver.viewer.layers) == layers
    assert receiver.component_groups.groups == groups
    assert first in receiver.layer_route_state.layers and second in receiver.layer_route_state.layers
    # Dispose only this test's synthetic unsettled state through original owners.
    if blocked == "running":
        receiver.layer_route_state.layer_settlement.fail()


def test_terminal_failed_candidate_is_retirable_without_erasing_other_failure(receiver):
    keep, update = enqueue(receiver, np.ones((2, 2)), producer="keep")
    advance_in_qt(receiver, keep, update)
    route, update = enqueue(receiver, np.full((2, 2), 2), producer="failed")
    advance_in_qt(receiver, route, update)
    enqueue(receiver, np.full((2, 2), 3), producer="failed")
    settlement = receiver.layer_route_state.begin_settlement()
    claimed, _ = settlement.begin_next()
    settlement.begin_active_work_unit(claimed)
    settlement.fail_active(claimed)
    receiver.layer_route_state.record_update_error(route, ValueError("retained original failure"))
    receiver.layer_route_state.record_update_error(keep, ValueError("other original failure"))
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(retirement_request(receiver, route))
    assert result.applied and not result.errors
    assert settlement.phase is ViewerSettlePhase.FAILED
    assert not settlement.updates
    assert receiver.layer_route_state.layer_update_errors == {keep: "other original failure"}
    assert keep in receiver.layer_route_state.layers


def test_retirement_prunes_multiple_survivors_with_cooperative_presentation_hooks(receiver, monkeypatch):
    calls = []
    monkeypatch.setitem(NapariImageLayerDisplayHandler.__registry__, StreamingDataType.IMAGE, NapariImageLayerDisplayHandler)
    class IndependentPresentationCapability:
        @contextmanager
        def preserve_native_presentation(self, request):
            calls.append(("enter", request.presentation.route_key))
            with super().preserve_native_presentation(request):
                yield
            calls.append(("exit", request.presentation.route_key))
    class NewDeclaredImageHandler(IndependentPresentationCapability, NapariImageLayerDisplayHandler):
        streaming_data_type = StreamingDataType.IMAGE
    # Class declaration is the only new case; the original generic consumer is untouched.
    middle, update = enqueue(receiver, np.full((2, 2), 2), well="A02", producer="middle")
    advance_in_qt(receiver, middle, update)
    originals = {}
    for name in ("sparse-a", "sparse-b"):
        route, _ = enqueue(receiver, np.ones((2, 2)), well="A01", producer=name, domain=["A01", "A03"])
        route, update = enqueue(receiver, np.full((2, 2), 3), well="A03", producer=name, domain=["A01", "A03"])
        advance_in_qt(receiver, route, update)
        layer = receiver.layer_route_state.layer(route)
        layer.contrast_limits, layer.gamma = (0, 10), 0.7
        layer.opacity, layer.visible = 0.4, False
        layer.colormap = "magenta"
        originals[route] = receiver.component_groups.existing_items_for(route)
    receiver.viewer.camera.center = (0, 1, 1)
    receiver.viewer.camera.zoom = 31
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(retirement_request(receiver, middle))
    assert result.applied and not result.errors
    assert len(calls) == 4
    for route, items in originals.items():
        layer = receiver.layer_route_state.layer(route)
        assert layer.data.shape == (2, 2, 2)
        np.testing.assert_array_equal(layer.data[0], items[0].data)
        np.testing.assert_array_equal(layer.data[1], items[1].data)
        assert receiver.component_groups.existing_items_for(route) is items
        assert tuple(layer.scale[-2:]) == (0.65, 0.65)
        assert layer.gamma == 0.7 and tuple(layer.contrast_limits) == (0, 10)
        assert layer.opacity == 0.4 and not layer.visible
        assert layer.colormap.name == "magenta"
    assert receiver.viewer.camera.zoom == 31
    assert tuple(receiver.viewer.camera.center) == (0, 1, 1)
    assert receiver.component_values.shared_values_for(["well"]) == {"well": ["A01", "A03"]}
    assert issubclass(NewDeclaredImageHandler, NapariImagePresentationRetention)


@pytest.mark.parametrize("data_type", [StreamingDataType.POINTS, StreamingDataType.SHAPES])
@pytest.mark.parametrize("selected", [False, True])
@pytest.mark.parametrize("reorder", [False, True])
def test_retirement_retains_survivor_source_members_without_late_navigation(
    receiver, data_type, selected, reorder,
):
    middle, update = enqueue(receiver, np.ones((2, 2)), well="A02", producer="middle")
    advance_in_qt(receiver, middle, update)
    for well, subject_id in [("A01", 7), ("A03", 8)]:
        members = [
            {"type": "points" if data_type is StreamingDataType.POINTS else "path",
             "coordinates": [[i, i], [i + 1, i + 1]],
             "metadata": {"label": subject_id,
                          ObjectArtifactSubjectBinding.SUBJECT_FEATURE: "test-object",
                          ObjectArtifactSubjectBinding.SUBJECT_ID_FEATURE: subject_id}}
            for i in range(2)
        ]
        # Points metadata is not a declared cross-layer subject binding; its
        # source members are retained independently of the Shapes group owner.
        if data_type is StreamingDataType.POINTS:
            for member in members:
                member["metadata"] = {"label": subject_id}
        route, update = enqueue(receiver, members, well=well, producer="survivor",
                                data_type=data_type, domain=["A01", "A03"])
    advance_in_qt(receiver, route, update)
    old = receiver.layer_route_state.layer(route)
    receiver.viewer.layers.selection.active = old
    if selected:
        old.selected_data = {0, 1}
    # The public retirement boundary follows earlier accepted selection work.
    # Its original zero-delay navigation must settle before choosing visibility.
    QApplication.instance().processEvents()
    feature = NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE
    retained = set(old.features.iloc[list(old.selected_data)][feature])
    source_items = receiver.component_groups.existing_items_for(route)
    if reorder:
        source_items.reverse()
    old.opacity, old.visible = 0.35, False
    receiver.viewer.camera.center = (0, 2, 3)
    receiver.viewer.camera.zoom = 19
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(
        retirement_request(receiver, middle)
    )
    assert result.applied and not result.errors
    native = receiver.layer_route_state.layer(route)
    assert native is not old and old not in receiver.viewer.layers
    assert set(native.features.iloc[list(native.selected_data)][feature]) == retained
    if reorder and selected:
        assert native.selected_data != {0, 1}
    assert receiver.component_groups.existing_items_for(route) is source_items
    assert tuple(native.scale[-2:]) == (0.65, 0.65)
    assert native.opacity == 0.35 and not native.visible
    assert receiver.viewer.layers.selection.active is native
    assert receiver.viewer.camera.zoom == 19
    assert tuple(receiver.viewer.camera.center) == (0, 2, 3)
    step = receiver.viewer.dims.current_step
    QApplication.instance().processEvents()
    assert receiver.viewer.dims.current_step == step
    assert set(native.features.iloc[list(native.selected_data)][feature]) == retained
    assert receiver.viewer.layers.selection.active is native


def test_new_selectable_capability_executes_cooperative_retention_hooks(receiver, monkeypatch):
    calls = []
    monkeypatch.setitem(NapariPointsLayerDisplayHandler.__registry__, StreamingDataType.POINTS,
                        NapariPointsLayerDisplayHandler)

    class IndependentPresentationCapability:
        @contextmanager
        def preserve_native_presentation(self, request):
            calls.append("enter")
            with super().preserve_native_presentation(request):
                yield
            calls.append("exit")

    class NewDeclaredPointsHandler(IndependentPresentationCapability, NapariPointsLayerDisplayHandler):
        streaming_data_type = StreamingDataType.POINTS

    middle, update = enqueue(receiver, np.ones((2, 2)), well="A02", producer="middle")
    advance_in_qt(receiver, middle, update)
    for well in ("A01", "A03"):
        route, update = enqueue(receiver, [{"type": "points", "coordinates": [[1, 2]],
                                           "metadata": {}}], well=well, producer="new-case",
                                data_type=StreamingDataType.POINTS, domain=["A01", "A03"])
    advance_in_qt(receiver, route, update)
    old = receiver.layer_route_state.layer(route)
    old.selected_data = {1}
    old.opacity = 0.2
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(
        retirement_request(receiver, middle)
    )
    assert result.applied and not result.errors
    native = receiver.layer_route_state.layer(route)
    assert calls == ["enter", "exit"]
    assert native.selected_data == {1} and native.opacity == 0.2
    assert issubclass(NewDeclaredPointsHandler, NapariSelectablePresentationRetention)


def test_controller_remount_retains_linked_subject_members_and_binding(receiver):
    viewer = receiver.viewer
    paths = [np.asarray([[i, i], [i + 1, i + 1]], dtype=float) for i in range(3)]
    feature = NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE
    old = viewer.add_shapes(paths, shape_type="path",
                            features={feature: ["a", "b", "c"], "owner": [8, 8, 9]})
    linked = viewer.add_shapes(paths[:2], shape_type="path",
                               features={feature: ["x", "y"], "owner": [8, 9]})
    controller = receiver.result_selection_controller
    binding = NapariResultSelectionGroupBinding("independent-subject", "owner")
    controller.bind(old, binding)
    controller.bind(linked, binding)
    controller.select(old, 0)
    assert old.selected_data == {0, 1} and linked.selected_data == {0}
    receiver.layer_route_state.set_layer("retained-selection", old)
    with controller.preserve_selection("retained-selection"):
        viewer.layers.remove(old)
        replacement = viewer.add_shapes(paths[::-1], shape_type="path",
                                        features={feature: ["c", "b", "a"], "owner": [9, 8, 8]})
        receiver.layer_route_state.set_layer("retained-selection", replacement)
    QApplication.instance().processEvents()
    assert replacement.selected_data == {1, 2} and linked.selected_data == {0}
    assert not controller.is_bound_result_layer(old)
    old.selected_data = {2}
    assert linked.selected_data == {0}
    controller.select(replacement, 0)
    assert replacement.selected_data == {0} and linked.selected_data == {1}


@pytest.mark.parametrize("identities", [None, ["duplicate", "duplicate"]])
def test_controller_refuses_unidentified_members_before_remount(receiver, identities):
    features = {} if identities is None else {
        NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE: identities,
    }
    old = receiver.viewer.add_points([[1, 2], [3, 4]], features=features)
    receiver.layer_route_state.set_layer("retained-selection", old)
    with pytest.raises(ValueError, match="source element identities"):
        with receiver.result_selection_controller.preserve_selection("retained-selection"):
            pytest.fail("Invalid member identity must be rejected before mutation.")
    assert old in receiver.viewer.layers


def test_controller_retains_empty_native_geometry_without_invented_identity(receiver):
    old = receiver.viewer.add_shapes(ndim=2)
    receiver.layer_route_state.set_layer("retained-selection", old)
    with receiver.result_selection_controller.preserve_selection("retained-selection"):
        receiver.viewer.layers.remove(old)
        replacement = receiver.viewer.add_shapes(ndim=2)
        receiver.layer_route_state.set_layer("retained-selection", replacement)
    assert not replacement.selected_data


@pytest.mark.parametrize("data_type", [StreamingDataType.POINTS, StreamingDataType.SHAPES])
def test_controller_refuses_off_slice_remapped_selection_before_native_assignment(
    receiver, data_type,
):
    viewer = receiver.viewer
    viewer.add_image(np.zeros((2, 8, 8), dtype=np.uint8))
    feature = NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE
    coordinates = [np.asarray([[0, i, i], [0, i + 1, i + 1]], dtype=float) for i in range(2)]

    def mount(z_index):
        data = [path + [z_index, 0, 0] for path in coordinates]
        features = {feature: ["a", "b"], "owner": [8, 8]}
        if data_type is StreamingDataType.POINTS:
            return viewer.add_points([path[0] for path in data], features=features)
        return viewer.add_shapes(data, shape_type="path", features=features)

    old = mount(0)
    viewer.dims.current_step = (0, 0, 0)
    controller = receiver.result_selection_controller
    controller.bind(old, NapariResultSelectionGroupBinding("retained-subject", "owner"))
    controller.select(old, 0)
    assert old.selected_data == {0, 1}
    receiver.layer_route_state.set_layer("retained-selection", old)
    with pytest.raises(ValueError, match="selected source members have no displayed geometry"):
        with controller.preserve_selection("retained-selection"):
            viewer.layers.remove(old)
            replacement = mount(1)
            receiver.layer_route_state.set_layer("retained-selection", replacement)
    assert not replacement.selected_data
    assert tuple(replacement.features[feature]) == ("a", "b")
    assert viewer.dims.current_step == (0, 0, 0)
    step = viewer.dims.current_step
    QApplication.instance().processEvents()
    assert viewer.dims.current_step == step and not replacement.selected_data


def test_controller_preservation_cancels_queued_navigation_without_unmount(receiver):
    feature = NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE
    layer = receiver.viewer.add_shapes([[[0, 0], [1, 1]]], shape_type="path",
                                        features={feature: ["member"]})
    controller = receiver.result_selection_controller
    controller.bind(layer)
    layer.selected_data = {0}
    layer.visible = False
    generation = controller._pending_generation
    step = receiver.viewer.dims.current_step
    receiver.layer_route_state.set_layer("retained-selection", layer)
    with controller.preserve_selection("retained-selection"):
        pass
    assert controller._pending_generation > generation
    QApplication.instance().processEvents()
    assert not layer.visible and layer.selected_data == {0}
    assert receiver.viewer.dims.current_step == step


@pytest.mark.parametrize("pair", [("y", "x"), ("z_index", "x"), ("z_index", "y")])
def test_fractional_spatial_selection_survives_real_qt_rematerialization(receiver, pair):
    middle, update = enqueue(receiver, np.ones((5, 6)), well="A02", producer="middle")
    advance_in_qt(receiver, middle, update)
    receiver.layer_route_state.layer(middle).visible = False
    for well in ("A01", "A03"):
        for z_index in (1, 2, 3, 4):
            raw, update = enqueue(
                receiver, np.ones((5, 6)), well=well, producer="raw-frames",
                domain=["A01", "A03"], z_domain=[1, 2, 3, 4], z_index=z_index,
            )
    advance_in_qt(receiver, raw, update)
    payloads = []
    for well in ("A01", "A03"):
        payload = [{"type": "points", "coordinates": [[1.5, 2.5]],
                    "metadata": {ROIFractionalZ.FIELD: 1.5, "label": 7}}]
        payloads.append(payload)
        route, update = enqueue(
            receiver, payload, well=well, producer="fractional-survivor",
            data_type=StreamingDataType.POINTS, domain=["A01", "A03"],
            z_domain=[1, 2, 3, 4],
        )
    advance_in_qt(receiver, route, update)
    receiver.raise_result_selection_surface = lambda: None  # No dock/socket shell in this fixture.
    old = receiver.layer_route_state.layer(route)
    feature = NapariStreamLayerItem.ELEMENT_IDENTITY_FEATURE
    identity = old.features.iloc[1][feature]
    presentation = receiver.layer_route_state.dimension_state_for(route).presentation
    spatial_dimensions = tuple(
        presentation.axis_labels.index(axis) for axis in presentation.spatial_axis_labels
    )
    original_coordinates = old.data[1, spatial_dimensions].copy()
    sources = receiver.component_groups.existing_items_for(route)
    navigation = NapariNavigationControlMessageAction()

    def select_and_check(layer):
        member = tuple(layer.features[feature]).index(identity)
        prepared = navigation.prepare(receiver, ViewerNavigationControlOptions(
            route_key=route, data_index=member, visible=True, selected=True,
            display_axes=pair,
        ))
        presentation = receiver.layer_route_state.dimension_state_for(route).presentation
        hidden_spatial = next(axis for axis in presentation.spatial_axis_labels if axis not in pair)
        assert prepared.request.axis_indices[hidden_spatial] == (
            3 if hidden_spatial == "x" else 2
        )
        navigation.apply_prepared(receiver, prepared)
        QApplication.instance().processEvents()  # Exercise the original selection callback too.
        assert tuple(receiver.viewer.dims.displayed) == tuple(
            presentation.axis_labels.index(axis) for axis in pair
        )
        assert set(layer.features.iloc[list(layer.selected_data)][feature]) == {identity}
        np.testing.assert_array_equal(layer.data[member, spatial_dimensions], original_coordinates)
        # Implicit displayed dimensions and explicit pair overrides have the same contract.
        assert navigation.result_element_axis_indices(receiver, layer, route, member) == (
            prepared.request.axis_indices
        )
        assert tuple(layer.scale[-2:]) == (0.65, 0.65)

    select_and_check(old)
    sources.reverse()  # Same source identity, deliberately different native row position.
    result = ViewerWindowService(QueuedRetirementGateway(receiver)).presentation(
        retirement_request(receiver, middle)
    )
    assert result.applied and not result.errors
    native = receiver.layer_route_state.layer(route)
    assert native is not old and native.selected_data == {0}
    assert receiver.component_groups.existing_items_for(route) is sources
    select_and_check(native)
    assert payloads == [[{"type": "points", "coordinates": [[1.5, 2.5]],
                         "metadata": {ROIFractionalZ.FIELD: 1.5, "label": 7}}]] * 2


def test_declared_point_coordinate_capability_executes_cooperative_hooks(receiver, monkeypatch):
    admitted = []
    monkeypatch.setitem(NapariPointsLayerDisplayHandler.__registry__, StreamingDataType.POINTS,
                        NapariPointsLayerDisplayHandler)

    class CoordinateAdmissionRecording:
        @classmethod
        def _coordinate_value(cls, value, *, axis_label):
            admitted.append(axis_label)
            return super()._coordinate_value(value, axis_label=axis_label)

    class RecordedPointCoordinates(CoordinateAdmissionRecording, ViewerPointCoordinateAuthority):
        pass

    class RecordedPointsHandler(NapariPointsLayerDisplayHandler):
        streaming_data_type = StreamingDataType.POINTS
        result_coordinate_authority = RecordedPointCoordinates

    route, update = enqueue(receiver, [{"type": "points", "coordinates": [[1.5, 2.5]],
                                       "metadata": {ROIFractionalZ.FIELD: 1.5}}],
                            producer="new-coordinate-case", data_type=StreamingDataType.POINTS,
                            z_domain=[1, 2, 3, 4])
    advance_in_qt(receiver, route, update)
    layer = receiver.layer_route_state.layer(route)
    presentation = receiver.layer_route_state.dimension_state_for(route).presentation
    action = NapariNavigationControlMessageAction()
    for pair in (("y", "x"), ("z_index", "x"), ("z_index", "y")):
        action.result_element_axis_indices(
            receiver, layer, route, 0,
            displayed_axis_indices=tuple(presentation.axis_labels.index(axis) for axis in pair),
        )
    assert admitted.count("z_index") == admitted.count("y") == admitted.count("x") == 1
    np.testing.assert_array_equal(layer.data[0, tuple(
        presentation.axis_labels.index(axis) for axis in presentation.spatial_axis_labels
    )], (1.5, 1.5, 2.5))
    assert RecordedPointsHandler.result_coordinate_authority is RecordedPointCoordinates
