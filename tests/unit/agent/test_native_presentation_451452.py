"""Original display admission and detached native presentation boundaries."""

from dataclasses import dataclass
from types import SimpleNamespace

import pytest

from openhcs.agent.dto.plate import PlateFileStreamRequest
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.core.config import (
    FijiStreamingConfig,
    NapariDisplayConfig,
    NapariDimensionMode,
    NapariStreamingConfig,
)


def test_stream_admits_original_display_declaration_without_changing_endpoint():
    display = NapariDisplayConfig(
        channel_mode=NapariDimensionMode.LAYER, colormap="green"
    )
    request = PlateFileStreamRequest.from_fields(
        plate_path="/synthetic",
        display_config=display,
        port=6004,
    )
    config = PlateStreamingService._streaming_config(request)
    assert config.channel_mode is NapariDimensionMode.LAYER
    assert config.colormap == "green"
    assert config.port == 6004
    assert request.as_tool_arguments()["display_config"]["channel_mode"] == "layer"
    assert isinstance(config, NapariDisplayConfig)


def test_missing_display_preserves_default_and_wrong_viewer_fails_closed():
    config = NapariStreamingConfig()
    assert config.with_display_config(None) is config
    with pytest.raises(TypeError, match="selected viewer"):
        FijiStreamingConfig().with_display_config(NapariDisplayConfig())


def test_new_display_leaf_uses_existing_admission_without_consumer_edits():
    @dataclass(frozen=True)
    class IndependentPalette:
        palette_label: str = "new palette"

        def display_payload_extra(self):
            return {
                **super().display_payload_extra(),
                "palette_label": self.palette_label,
            }

    @dataclass(frozen=True)
    class NewDisplay(IndependentPalette, NapariDisplayConfig):
        pass

    @dataclass(frozen=True)
    class NewStreaming(NapariStreamingConfig, NewDisplay):
        pass

    config = NewStreaming(port=6004).with_display_config(
        NewDisplay(palette_label="new")
    )
    assert config.palette_label == "new"
    assert config.port == 6004
    assert config.component_modes()["channel"] == "stack"
    assert config.display_payload_extra()["palette_label"] == "new"
    assert config.display_payload_extra()["colormap"] == "gray"


def test_channel_carrier_title_describes_identity_not_rgb_cardinality():
    from openhcs.runtime.napari_viewer_server import NapariImagePayloadLayoutRole

    role = NapariImagePayloadLayoutRole.COLOR_PLANE
    assert role.title("selected_images") == "selected_images source channels"
    assert role.route_key("selected_images") == "selected_images_color_plane"
    assert NapariImagePayloadLayoutRole.SCALAR_PLANE.title("raw") == "raw"


def test_two_physical_channel_layers_share_spatial_view_without_remapping_pixels():
    import numpy as np
    from napari.components import ViewerModel
    from polystore.streaming.identity import StreamProducerIdentity
    from polystore.streaming_constants import StreamingDataType
    from openhcs.runtime.napari_streaming_handlers import NapariLayerRouteStateStore
    from openhcs.core.runtime_image_values import ImagePayloadMetadata
    from openhcs.core.source_metadata import SourceVoxelSpacing
    from openhcs.core.source_spatial_domain import SourceSpatialDomain
    from openhcs.runtime.napari_viewer_server import (
        NapariLayerDisplayPipeline,
        NapariPendingLayerUpdate,
    )
    from openhcs.runtime.viewer_component_system import (
        ViewerComponentAxisSemantics,
        ViewerComponentNameMetadata,
        ViewerObjectDisplayConfigInput,
    )
    from tests.unit.test_napari_streaming_handlers import (
        _FakeNapariServer,
        _FakeTimer,
        _layer_item,
        _component_value_domain,
    )

    config = PlateStreamingService._streaming_config(
        PlateFileStreamRequest.from_fields(
            plate_path="/synthetic",
            display_config=NapariDisplayConfig(
                channel_mode=NapariDimensionMode.LAYER,
            ),
        )
    )
    server = _FakeNapariServer()
    server.viewer = ViewerModel()
    server.layer_route_state = NapariLayerRouteStateStore.empty()
    pipeline = NapariLayerDisplayPipeline(server)
    items = []
    for channel in (1, 3):
        route = f"physical-C{channel}"
        pixels = np.full((8, 8), channel * 1000, dtype=np.uint16)
        item = _layer_item(
            {
                "site": 1,
                "channel": channel,
                "z_index": 1,
                "timepoint": 1,
                "well": "A01",
            },
            data=pixels,
            producer=StreamProducerIdentity("manual", "image", "raw", "raw"),
            image_metadata=ImagePayloadMetadata(
                source_voxel_spacing=SourceVoxelSpacing((0.12353054911059548,) * 2),
                source_spatial_domain=SourceSpatialDomain((0, 0), (8, 8)),
            ),
        )
        items.append((item, pixels.copy()))
        semantics = ViewerComponentAxisSemantics(
            entries=_component_value_domain(
                {
                    component: [value]
                    for component, value in item.address.components.items()
                }
            ).entries,
            layout=ViewerObjectDisplayConfigInput(config).layout(),
        )
        server.layer_route_state.set_title(route, route)
        work = pipeline.display_layer_batch(
            layer_key=route,
            items=[item],
            display_payload=NapariPendingLayerUpdate.from_semantics(
                timer=_FakeTimer(),
                data_type=StreamingDataType.IMAGE,
                semantics=semantics,
                display_config=config,
            ),
            component_names_metadata=ViewerComponentNameMetadata.empty(),
        )
        assert work.advance()
    left, right = server.viewer.layers
    assert left.visible and right.visible
    assert "channel" not in server.viewer.dims.axis_labels
    assert left.data_to_world((0,) * left.ndim) == right.data_to_world(
        (0,) * right.ndim
    )
    assert tuple(left.scale) == tuple(right.scale)
    assert tuple(left.scale[-2:]) == (0.12353054911059548,) * 2
    for layer, (item, original) in zip(server.viewer.layers, items, strict=True):
        np.testing.assert_array_equal(item.data, original)
        np.testing.assert_array_equal(layer.data[(0,) * (layer.ndim - 2)], original)
    assert [item.address.components["channel"] for item, _ in items] == [1, 3]


class NativeWindowFixture:
    """Qt property fixture only; actual installed window proof is parent-owned."""

    def __init__(self, x=0):
        from qtpy.QtCore import QRect

        self.rectangle = QRect(x, 30, 400, 300)
        self.visible = True
        self.active = False
        self.minimized = True
        self.focus_calls = []

    def geometry(self):
        return self.rectangle

    def setGeometry(self, rectangle):
        self.rectangle = rectangle

    def screen(self):
        from qtpy.QtCore import QRect

        return SimpleNamespace(availableGeometry=lambda: QRect(0, 0, 1920, 1080))

    def minimumWidth(self):
        return 100

    def minimumHeight(self):
        return 100

    def isVisible(self):
        return self.visible

    def isActiveWindow(self):
        return self.active

    def isMinimized(self):
        return self.minimized

    def isMaximized(self):
        return False

    def showNormal(self):
        self.minimized = False
        self.focus_calls.append("restore")

    def show(self):
        self.visible = True
        self.focus_calls.append("show")

    def raise_(self):
        self.focus_calls.append("raise")

    def activateWindow(self):
        self.active = True
        self.focus_calls.append("activate")


def native_server():
    import numpy as np
    from napari.components import ViewerModel
    from openhcs.runtime.napari_streaming_handlers import NapariLayerRouteStateStore

    viewer = ViewerModel()
    routes = NapariLayerRouteStateStore.empty()
    for route, channel in (("C1", 1), ("C3", 3)):
        image = viewer.add_image(
            np.full((8, 8), channel * 1000, dtype=np.uint16), rgb=False
        )
        routes.set_layer(route, image)
    window = NativeWindowFixture()
    native_viewer = SimpleNamespace(
        layers=viewer.layers,
        camera=viewer.camera,
        dims=viewer.dims,
        window=SimpleNamespace(qt_viewer=SimpleNamespace(window=lambda: window)),
    )
    return SimpleNamespace(viewer=native_viewer, layer_route_state=routes), window


def test_color_native_action_preserves_units_and_has_one_reply_and_route_owner():
    import numpy as np
    from openhcs.runtime.napari_viewer_server import (
        NapariControlMessageAction,
        NapariMountedRouteControlMessageAction,
        NapariPresentationControlMessageAction,
    )
    from openhcs.runtime.viewer_protocol import (
        OpenHCSViewerControlMessageType,
        ViewerImageColorControlOptions,
        ViewerNativeImageColorPresentation,
    )

    server, _ = native_server()
    action = NapariControlMessageAction.for_message_type(
        OpenHCSViewerControlMessageType.IMAGE_COLOR.value
    )
    assert isinstance(action, NapariMountedRouteControlMessageAction)
    assert isinstance(action, NapariPresentationControlMessageAction)
    originals = [layer.data.copy() for layer in server.viewer.layers]
    camera = (server.viewer.camera.center, server.viewer.camera.zoom)
    for route, colormap in (("C1", "blue"), ("C3", "green")):
        reply = action.handle(
            server,
            {
                "payload": ViewerImageColorControlOptions(
                    route,
                    ViewerNativeImageColorPresentation(colormap, "additive"),
                )
            },
        )
        assert reply["status"] == "success"
        assert reply["native_image_color"] == {
            "colormap": colormap,
            "blending": "additive",
        }
    for layer, pixels in zip(server.viewer.layers, originals, strict=True):
        np.testing.assert_array_equal(layer.data, pixels)
    assert camera == (server.viewer.camera.center, server.viewer.camera.zoom)
    from polystore.streaming.receivers.napari.image_presentation import (
        NapariNativeImageIntensityPresentation,
    )
    from zmqruntime.viewer_protocol import ViewerNativeImageIntensityPresentation

    for layer, limits in zip(server.viewer.layers, ((0, 1500), (0, 4000)), strict=True):
        control = NapariNativeImageIntensityPresentation.for_layer(layer)
        control.apply(ViewerNativeImageIntensityPresentation(limits, 1))
        assert control.snapshot().contrast_limits == limits
    assert (
        server.viewer.layers[0].contrast_limits
        != server.viewer.layers[1].contrast_limits
    )
    for route, colormap, blending in (
        ("missing", "green", "additive"),
        ("C1", "green", "invalid"),
        ("C1", "invalid-no-registry-name", "additive"),
    ):
        previous = server.viewer.layers[0].colormap.name
        reply = action.handle(
            server,
            {
                "payload": ViewerImageColorControlOptions(
                    route,
                    ViewerNativeImageColorPresentation(colormap, blending),
                )
            },
        )
        assert reply["status"] == "error"
        assert server.viewer.layers[0].colormap.name == previous
    assert action.handle(server, {"payload": {"route_key": "C1"}})["status"] == "error"
    from napari.layers import Image, Points

    for route, layer in (
        ("RGB", Image(np.ones((8, 8, 3)), rgb=True)),
        ("RGBA", Image(np.ones((8, 8, 4)), rgb=True)),
        ("points", Points(np.zeros((1, 2)))),
    ):
        server.viewer.layers.append(layer)
        server.layer_route_state.set_layer(route, layer)
        reply = action.handle(
            server,
            {
                "payload": ViewerImageColorControlOptions(
                    route,
                    ViewerNativeImageColorPresentation("blue", "additive"),
                )
            },
        )
        assert reply["status"] == "error"


def test_window_action_reads_actual_state_focuses_only_its_window_and_bounds_geometry():
    from openhcs.runtime.napari_viewer_server import NapariControlMessageAction
    from openhcs.runtime.viewer_protocol import (
        OpenHCSViewerControlMessageType,
        ViewerNativeWindowControlOptions,
        ViewerNativeWindowGeometry,
        ViewerNativeWindowState,
    )

    server, window = native_server()
    other = NativeWindowFixture(x=900)
    action = NapariControlMessageAction.for_message_type(
        OpenHCSViewerControlMessageType.WINDOW_PRESENTATION.value
    )
    before = action.handle(server, {"payload": ViewerNativeWindowControlOptions()})
    assert before["status"] == "success" and window.focus_calls == []
    geometry = ViewerNativeWindowGeometry(30, 30, 600, 450)
    changed = action.handle(
        server, {"payload": ViewerNativeWindowControlOptions(geometry, True)}
    )
    native = ViewerNativeWindowState.from_wire_mapping(changed["native_window"])
    assert native.geometry == geometry and native.active
    assert window.focus_calls == ["restore", "show", "raise", "activate"]
    assert other.focus_calls == [] and other.geometry().x() == 900
    for invalid in (
        ViewerNativeWindowGeometry(-10, 0, 600, 450),
        ViewerNativeWindowGeometry(0, 0, 30, 30),
    ):
        reply = action.handle(
            server, {"payload": ViewerNativeWindowControlOptions(invalid, True)}
        )
        assert reply["status"] == "error" and window.geometry().width() == 600
    assert action.transport_thread_response(server, {}) is None


@pytest.mark.parametrize("width", (True, 0, -1, 16777216))
def test_geometry_rejects_invalid_declarations(width):
    from openhcs.runtime.viewer_protocol import ViewerNativeWindowGeometry

    with pytest.raises((TypeError, ValueError)):
        ViewerNativeWindowGeometry(0, 0, width, 100)


def test_independent_new_native_capability_composes_real_cooperative_mro():
    from openhcs.runtime.napari_viewer_server import (
        NapariControlMessageAction,
        NapariImageColorControlMessageAction,
    )
    from openhcs.runtime.viewer_protocol import (
        ViewerImageColorControlOptions,
        ViewerNativeImageColorPresentation,
    )

    calls = []

    class IndependentReadbackCapability:
        def apply_presentation(self, server, request):
            calls.append("before")
            result = super().apply_presentation(server, request)
            calls.append(("after", result.colormap))
            return result

    class NewColorDeclaration(
        IndependentReadbackCapability, NapariImageColorControlMessageAction
    ):
        message_type = "source-test-independent-color"

    server, _ = native_server()
    try:
        action = NapariControlMessageAction.for_message_type(
            NewColorDeclaration.message_type
        )
        reply = action.handle(
            server,
            {
                "payload": ViewerImageColorControlOptions(
                    "C1",
                    ViewerNativeImageColorPresentation("blue", "additive"),
                )
            },
        )
        assert reply["status"] == "success"
        assert calls == ["before", ("after", "blue")]
        assert NewColorDeclaration.__mro__.index(
            IndependentReadbackCapability
        ) < NewColorDeclaration.__mro__.index(NapariImageColorControlMessageAction)
    finally:
        NapariControlMessageAction.__registry__.pop(NewColorDeclaration.message_type)
