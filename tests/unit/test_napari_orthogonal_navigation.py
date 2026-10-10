"""Extra-axis semantic planes use the existing native navigation authority."""

from types import SimpleNamespace

import numpy as np
import pytest
from napari.components import ViewerModel
from qtpy.QtCore import Qt

from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import ViewerWindowNavigationRequest
from openhcs.runtime.napari_streaming_handlers import (
    NapariAxisPresentation,
    NapariComponentGroupStore,
    NapariDimensionLayerState,
    NapariLayerRouteStateStore,
)
from openhcs.runtime.napari_viewer_server import (
    NapariNavigationControlAction,
    NapariResultSelectionController,
    NapariViewerStateProjection,
)
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsFactory,
    ViewerComponentLayout,
    ViewerLayerAxisProjection,
)
from openhcs.runtime.viewer_controls import (
    ViewerNavigationControlOptions,
    ViewerResultElementCoordinates,
)
from openhcs.runtime.viewer_display import NapariSlots
from tests.unit.viewer_axes_fixture import STREAM_AXES


class NativeHarness(SimpleNamespace):
    """Only the transport/server shell is replaced; native layers and Dims are real."""


def mount(server, route, layer, components, offsets=None, payload_axes=()):
    offsets = offsets or (0,) * len(components)
    semantics = ViewerComponentAxisSemanticsFactory.empty()
    values = {
        axis: list(range(layer.data.shape[index]))
        for index, axis in enumerate(components)
    }
    presentation = NapariAxisPresentation(
        entries=semantics.entries,
        layout=ViewerComponentLayout.from_parts(
            component_modes={axis: NapariSlots.Stack.wire_value for axis in components},
            component_order=components,
            declared_axes=STREAM_AXES,
        ),
        route_key=route,
        projection=ViewerLayerAxisProjection(
            projected_axis_components=components,
            component_values=values,
            routed_component_values=values,
            axis_offsets=offsets,
        ),
        payload_axis_labels=payload_axes,
    )
    server.layer_route_state.set_title(route, route)
    server.layer_route_state.set_layer(route, layer)
    server.layer_route_state.set_dimension_state(
        route,
        NapariDimensionLayerState(
            labels={axis: tuple(map(str, value)) for axis, value in values.items()},
            presentation=presentation,
        ),
    )
    return presentation


def harness(viewer):
    server = NativeHarness(
        viewer=viewer,
        layer_route_state=NapariLayerRouteStateStore.empty(),
        component_groups=NapariComponentGroupStore(),
        display_pipeline=SimpleNamespace(
            dimension_label_overlay=SimpleNamespace(refresh=lambda: None)
        ),
        napari_window_title="Synthetic native planes",
    )
    server.result_selection_controller = NapariResultSelectionController(server)
    return server


@pytest.mark.parametrize("leading", [(2, 2, 2, 2), (1, 2, 1, 2)])
@pytest.mark.parametrize("pair", [("y", "x"), ("z_index", "x"), ("z_index", "y")])
def test_native_planes_preserve_extra_axes_world_identity_and_alignment(leading, pair):
    components = ("site", "channel", "z_index", "timepoint", "well")
    axes = components + ("y", "x")
    shape = (leading[0], leading[1], 3, leading[2], leading[3], 4, 5)
    pixels = np.arange(np.prod(shape), dtype=np.float32).reshape(shape)
    labels = pixels.astype(np.uint32) + 1
    scale = (1, 1, 2.5, 1, 1, 0.8, 0.9)
    translate = (10, 20, 17, 30, 40, -2, 4)
    viewer = ViewerModel()
    image = viewer.add_image(
        pixels, rgb=False, scale=scale, translate=translate, gamma=0.75
    )
    dense = viewer.add_labels(labels, scale=scale, translate=translate)
    anchor = (leading[0] - 1, leading[1] - 1, 1, leading[2] - 1, leading[3] - 1, 2, 3)
    point = viewer.add_points(
        np.array([anchor], dtype=float), scale=scale, translate=translate
    )
    server = harness(viewer)
    mount(server, "raw", image, components)
    mount(server, "labels", dense, components)
    # Coordinate layers have the same semantic presentation, not array-shape extents.
    server.layer_route_state.set_title("points", "points")
    server.layer_route_state.set_layer("points", point)
    server.layer_route_state.set_dimension_state(
        "points", server.layer_route_state.dimension_state_for("raw")
    )
    viewer.dims.axis_labels = axes
    viewer.dims.point = image.data_to_world(anchor)
    previous_point = tuple(viewer.dims.point)
    response = NapariNavigationControlAction().handle(
        server,
        {"payload": ViewerNavigationControlOptions(route_key="raw", display_axes=pair)},
    )
    assert response["status"] == "success", response
    displayed = tuple(axes.index(axis) for axis in pair)
    assert tuple(viewer.dims.displayed) == displayed
    assert tuple(viewer.dims.point) == previous_point
    assert response["native_dimensions"]["displayed_axes"] == pair
    for first in range(shape[displayed[0]]):
        for second in range(shape[displayed[1]]):
            coordinate = list(anchor)
            coordinate[displayed[0]], coordinate[displayed[1]] = first, second
            world = image.data_to_world(coordinate)
            assert (
                image.get_value(world, world=True, dims_displayed=list(displayed))
                == pixels[tuple(coordinate)]
            )
            assert (
                dense.get_value(world, world=True, dims_displayed=list(displayed))
                == labels[tuple(coordinate)]
            )
    assert (
        point.get_value(previous_point, world=True, dims_displayed=list(displayed)) == 0
    )
    assert image.data is pixels and dense.data is labels
    assert tuple(image.scale) == scale and tuple(image.translate) == translate
    assert image.gamma == 0.75


@pytest.mark.parametrize("pair", [("channel", "x"), ("band", "x"), ("missing", "y")])
def test_nonspatial_or_missing_axes_reject_before_any_mutation(pair):
    viewer = ViewerModel()
    layer = viewer.add_image(np.zeros((2, 3, 4, 5, 6)), rgb=False)
    server = harness(viewer)
    mount(server, "raw", layer, ("channel", "z_index"), payload_axes=("band",))
    previous = (
        layer.visible,
        tuple(viewer.dims.order),
        tuple(viewer.dims.current_step),
        viewer.layers.selection.active,
    )
    reply = NapariNavigationControlAction().handle(
        server,
        {
            "payload": ViewerNavigationControlOptions(
                route_key="raw",
                display_axes=pair,
                visible=False,
                selected=False,
                axis_indices={"channel": 1},
            )
        },
    )
    assert reply["status"] == "error"
    assert previous == (
        layer.visible,
        tuple(viewer.dims.order),
        tuple(viewer.dims.current_step),
        viewer.layers.selection.active,
    )


def test_visible_planar_shapes_reject_cross_section_but_hidden_shapes_allow_raw():
    viewer = ViewerModel()
    image = viewer.add_image(np.zeros((3, 4, 5)), rgb=False)
    roi = viewer.add_shapes(
        [np.array([[1, 0, 0], [1, 0, 2], [1, 2, 2]], dtype=float)], shape_type="polygon"
    )
    server = harness(viewer)
    mount(server, "raw", image, ("z_index",))
    before = tuple(viewer.dims.order)
    action = NapariNavigationControlAction()
    request = ViewerNavigationControlOptions(
        route_key="raw", display_axes=("z_index", "x")
    )
    reply = action.handle(server, {"payload": request})
    assert reply["status"] == "error" and "planar Shapes" in reply["message"]
    assert tuple(viewer.dims.order) == before and roi.visible
    roi.visible = False
    assert action.handle(server, {"payload": request})["status"] == "success"


@pytest.mark.parametrize(
    "displayed, expected",
    [
        ((2, 3), {"channel": 1, "z_index": 2}),
        ((1, 3), {"channel": 1, "y": 4}),
        ((1, 2), {"channel": 1, "x": 7}),
    ],
)
def test_hidden_indices_use_actual_displayed_dimensions(displayed, expected):
    assert (
        ViewerResultElementCoordinates.axis_indices(
            coordinates=(1, 2, 4, 7),
            axis_labels=("channel", "z_index", "y", "x"),
            displayed_axis_indices=displayed,
            spatial_axis_labels=("z_index", "y", "x"),
        )
        == expected
    )


def test_displayed_z_may_be_fractional_and_span_slices_but_hidden_y_must_not():
    assert ViewerResultElementCoordinates.axis_indices(
        coordinates=((1, 2.25, 4, 7), (1, 3.5, 4, 8)),
        axis_labels=("channel", "z_index", "y", "x"),
        displayed_axis_indices=(1, 3),
        spatial_axis_labels=("z_index", "y", "x"),
    ) == {"channel": 1, "y": 4}
    with pytest.raises(ValueError, match="spans multiple 'y'"):
        ViewerResultElementCoordinates.axis_indices(
            coordinates=((1, 2.25, 4, 7), (1, 3.5, 5, 8)),
            axis_labels=("channel", "z_index", "y", "x"),
            displayed_axis_indices=(1, 3),
            spatial_axis_labels=("z_index", "y", "x"),
        )


def test_generated_mcp_signature_derives_display_axes_from_existing_request():
    from openhcs.agent.capabilities import agent_capabilities

    capability = agent_capabilities.navigate_viewer_window
    assert capability.input_contract is ViewerWindowNavigationRequest
    parameters = capability.invocation.option_parameters(ViewerWindowNavigationRequest)
    assert "display_axes" in {parameter.name for parameter in parameters}
    request = ViewerWindowNavigationRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5982),
        route_key="raw",
        display_axes=("z_index", "x"),
    )
    assert request.as_tool_arguments()["display_axes"] == ["z_index", "x"]


@pytest.mark.parametrize("pair", [("x", "x"), ("y",), "xy", ("", "x"), (True, "x")])
def test_invalid_pairs_are_rejected_at_typed_boundary(pair):
    with pytest.raises((TypeError, ValueError)):
        ViewerNavigationControlOptions(route_key="raw", display_axes=pair)


def test_shared_route_offsets_survive_orientation_and_local_navigation():
    viewer = ViewerModel()
    image = viewer.add_image(np.zeros((2, 3, 4, 5)), rgb=False, translate=(4, 16, 0, 0))
    other = viewer.add_image(np.zeros((3, 5, 4, 5)), rgb=False)
    server = harness(viewer)
    mount(server, "raw", image, ("channel", "z_index"), (4, 16))
    mount(server, "other", other, ("channel", "z_index"))
    action = NapariNavigationControlAction()
    reply = action.handle(
        server,
        {
            "payload": ViewerNavigationControlOptions(
                route_key="raw",
                display_axes=("z_index", "x"),
                axis_indices={"channel": 1, "z_index": 2},
            )
        },
    )
    assert reply["status"] == "success", reply
    assert tuple(viewer.dims.current_step[:2]) == (5, 18)
    assert tuple(image.translate) == (4, 16, 0, 0)


def test_state_reflects_user_order_and_does_not_cache_requested_pair():
    viewer = ViewerModel()
    viewer.add_image(np.zeros((3, 4, 5)), rgb=False)
    viewer.dims.axis_labels = ("z_index", "y", "x")
    first = NapariViewerStateProjection.native_dimensions(viewer)
    viewer.dims.order = (2, 0, 1)
    second = NapariViewerStateProjection.native_dimensions(viewer)
    assert first.displayed_axes == ("y", "x") and second.displayed_axes == (
        "z_index",
        "y",
    )
    assert second.order == (2, 0, 1) and second.canvas_size is None


def test_lower_rank_presentation_maps_to_right_aligned_viewer_dimensions():
    viewer = ViewerModel()
    viewer.add_image(np.zeros((2, 3, 4, 5)), rgb=False)
    image = viewer.add_image(np.zeros((3, 4, 5)), rgb=False)
    server = harness(viewer)
    presentation = mount(server, "raw", image, ("z_index",))
    assert presentation.viewer_dimension_indices(4) == (1, 2, 3)
    order = presentation.display_order(("z_index", "x"), tuple(viewer.dims.order))
    assert order[-2:] == (1, 3)
    step = NapariNavigationControlAction().axis_step(
        server,
        image,
        ViewerNavigationControlOptions(route_key="raw", axis_indices={"z_index": 2}),
    )
    assert step[1] == 2 and step[0] == viewer.dims.current_step[0]


def test_plugin_choices_and_button_use_same_native_navigation_owner(qtbot, monkeypatch):
    from openhcs.runtime.napari_orthogonal_widget import OpenHCSOrthogonalWidget

    viewer = ViewerModel()
    image = viewer.add_image(np.zeros((2, 3, 4, 5)), rgb=False)
    viewer.dims.axis_labels = ("channel", "z_index", "y", "x")
    server = harness(viewer)
    presentation = mount(server, "raw", image, ("channel", "z_index"))
    widget = OpenHCSOrthogonalWidget(server)
    qtbot.addWidget(widget)
    pairs = tuple(
        widget.planes.itemData(index) for index in range(widget.planes.count())
    )
    assert pairs == (("z_index", "y"), ("z_index", "x"), ("y", "x"))
    assert all(set(pair).issubset(presentation.spatial_axis_labels) for pair in pairs)
    original = NapariNavigationControlAction.handle
    submitted = []

    def record(action, owner, message):
        submitted.append(message["payload"])
        return original(action, owner, message)

    monkeypatch.setattr(NapariNavigationControlAction, "handle", record)
    widget.planes.setCurrentIndex(pairs.index(("z_index", "x")))
    qtbot.mouseClick(widget.apply_button, Qt.LeftButton)
    assert submitted == [
        ViewerNavigationControlOptions(route_key="raw", display_axes=("z_index", "x"))
    ]
    assert tuple(viewer.dims.displayed) == (1, 3)
    viewer.dims.order = (0, 3, 1, 2)
    assert "z_index / y" in widget.status.text()


def test_bundled_plugin_factory_rejects_unmanaged_viewer(qtbot):
    from napari import Viewer
    from openhcs.runtime.napari_orthogonal_widget import make_orthogonal_widget

    viewer = Viewer(show=False)
    try:
        with pytest.raises(ValueError, match="managed viewer"):
            make_orthogonal_widget(viewer)
    finally:
        viewer.close()


def test_plugin_late_native_mount_populates_routes_without_polling(qtbot):
    from openhcs.runtime.napari_orthogonal_widget import OpenHCSOrthogonalWidget

    viewer = ViewerModel()
    server = harness(viewer)
    widget = OpenHCSOrthogonalWidget(server)
    qtbot.addWidget(widget)
    assert widget.routes.count() == 0 and not widget.apply_button.isEnabled()
    # Native insertion fires BEFORE the route owner records the mounted layer.
    image = viewer.add_image(np.zeros((3, 4, 5)), rgb=False)
    mount(server, "late-raw", image, ("z_index",))
    qtbot.waitUntil(lambda: widget.routes.currentData() == "late-raw", timeout=1000)
    assert widget.apply_button.isEnabled() and widget.planes.count() == 3
    server.layer_route_state.purge_route("late-raw")
    viewer.layers.remove(image)
    qtbot.waitUntil(lambda: widget.routes.count() == 0, timeout=1000)
    assert not widget.apply_button.isEnabled()
