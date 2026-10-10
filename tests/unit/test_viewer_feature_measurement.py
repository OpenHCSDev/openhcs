"""Native model/route/math contracts; no Qt window, MCP process or JVM launched."""

import asyncio
import json
import pickle
from dataclasses import replace
from types import SimpleNamespace

import numpy as np
import pytest
from napari.components import ViewerModel
from polystore.streaming.identity import (
    FixedStreamProducerIdentityKind,
    StreamProducerIdentity,
)
from polystore.streaming_constants import StreamingDataType
from python_introspect import dataclass_from_mapping, to_jsonable
from zmqruntime.viewer_protocol import ViewerComponentMode

from openhcs.agent.capabilities import (
    AgentCapabilitySearchRequest,
    get_capability_registry,
)
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import (
    ViewerWindowPolylineMeasurementRequest,
    ViewerWindowPolylineMeasurementResult,
    ViewerWindowRegionMeasurementRequest,
)
from openhcs.agent.services.viewer_window_service import (
    ViewerWindowService,
    ZMQViewerWindowGateway,
)
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.runtime.napari_streaming_handlers import (
    NapariAxisPresentation,
    NapariComponentGroupStore,
    NapariDimensionLayerState,
    NapariLayerRouteStateStore,
    NapariStreamLayerAddress,
    NapariStreamLayerItem,
)
from openhcs.runtime.napari_viewer_server import NapariControlMessageAction
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsAuthority,
    ViewerComponentLayout,
    ViewerComponentValueDomainPayload,
    ViewerLayerAxisProjection,
)
from openhcs.runtime.viewer_controls import (
    ViewerPolylineControlOptions,
    ViewerRegionControlOptions,
)
from openhcs.runtime.viewer_measurements import NativeImageMeasurement
from openhcs.runtime.viewer_protocol import OpenHCSViewerControlMessageType


def native_route():
    raw = (np.arange(64)[:, None] * 10 + np.arange(64)[None, :]).astype(np.uint16)
    viewer = ViewerModel()
    layer = viewer.add_image(
        np.stack((raw, raw + 1000)),
        rgb=False,
        name="source",
        axis_labels=("channel", "y", "x"),
        scale=(1, 2, 3),
        translate=(0, 7, 11),
        units=("dimensionless",) * 3,
        contrast_limits=(30, 400),
        gamma=0.8,
    )
    projection = ViewerLayerAxisProjection(
        projected_axis_components=("channel",),
        component_values={"channel": [1, 2]},
        routed_component_values={"channel": [1, 2]},
        axis_offsets=(0,),
        scalar_component_values={},
    )
    presentation = NapariAxisPresentation(
        route_key="source",
        projection=projection,
        entries=ViewerComponentAxisSemanticsAuthority.empty().entries,
        layout=ViewerComponentLayout.from_parts(
            component_modes={"channel": ViewerComponentMode.STACK},
            component_order=("channel",),
        ),
    )
    routes = NapariLayerRouteStateStore.empty()
    routes.set_title("source", "Source")
    routes.set_layer("source", layer)
    routes.set_dimension_state(
        "source",
        NapariDimensionLayerState(
            labels={"channel": ["DNA", "Actin"]}, presentation=presentation
        ),
    )
    groups = NapariComponentGroupStore()
    for channel, data in ((1, raw), (2, raw + 1000)):
        data.setflags(write=False)
        groups.items_for("source").append(
            NapariStreamLayerItem(
                data=data,
                producer=StreamProducerIdentity.fixed_output(
                    FixedStreamProducerIdentityKind.MANUAL, "native"
                ),
                address=NapariStreamLayerAddress(
                    {"channel": channel, "site": 1},
                    f"/source/w{channel}.tif",
                    StreamingDataType.IMAGE,
                ),
                image_metadata=ImagePayloadMetadata(
                    source_spatial_domain=SourceSpatialDomain((0, 0), (64, 64)),
                    source_voxel_spacing=SourceVoxelSpacing(
                        (2, 3), unit=SourceVoxelSpacingUnit.RELATIVE
                    ),
                ),
                plane_component_domain=ViewerComponentValueDomainPayload(()),
            )
        )
    return (
        SimpleNamespace(
            viewer=viewer, layer_route_state=routes, component_groups=groups
        ),
        layer,
        raw,
    )


def dispatch(server, kind, request):
    # Same pickle boundary and registered action used by the Qt control ingress.
    message = pickle.loads(pickle.dumps({"type": kind.value, "payload": request}))
    return NapariControlMessageAction.for_message_type(kind.value).handle(
        server, message
    )


def presentation(viewer, layer):
    return (
        tuple(viewer.camera.center),
        viewer.camera.zoom,
        tuple(viewer.dims.point),
        tuple(viewer.dims.order),
        viewer.dims.ndisplay,
        tuple(layer.scale),
        tuple(layer.translate),
        tuple(layer.contrast_limits),
        layer.gamma,
        layer.visible,
        viewer.layers.selection.active,
        id(layer.data),
        tuple(viewer.layers),
        tuple(layer.axis_labels),
        tuple(layer.units),
        layer.affine.affine_matrix.tobytes(),
    )


def line(**changes):
    return ViewerPolylineControlOptions(
        route_key="source",
        axis_indices={"channel": 0},
        vertices_yx=((10.0, 10.0), (10.0, 19.0), (19.0, 19.0)),
        **changes,
    )


def test_native_polyline_profile_scaled_translated_anisotropy_is_readonly():
    server, layer, raw = native_route()
    before = presentation(server.viewer, layer)
    pixels = raw.copy()
    response = dispatch(
        server, OpenHCSViewerControlMessageType.MEASURE_POLYLINE, line()
    )
    assert response["status"] == "success", response
    result = response["measurement"]
    assert result["data_length"] == 18
    assert result["data_chord_length"] == pytest.approx(np.sqrt(162))
    assert result["world_length"] == 45
    assert result["world_chord_length"] == pytest.approx(np.hypot(18, 27))
    np.testing.assert_array_equal(
        result["profile_values"], np.r_[raw[10, 10:20], raw[11:20, 19]]
    )
    assert result["world_vertices"] == [
        [0.0, 27.0, 41.0],
        [0.0, 27.0, 68.0],
        [0.0, 45.0, 68.0],
    ]
    coordinates = response["coordinates"]
    assert coordinates["components"] == {"channel": 1, "site": 1}
    assert coordinates["source_path"] == "/source/w1.tif"
    assert coordinates["source_spacing"]["unit"] == "relative"
    assert coordinates["physical_calibration_verified"] is False
    assert presentation(server.viewer, layer) == before
    np.testing.assert_array_equal(raw, pixels)


def test_width_reduction_bilinear_and_nearest_are_explicit_source_values():
    raw = np.arange(400, dtype=float).reshape(20, 20)
    plane = NativeImageMeasurement(raw, (0, 0), lambda p: p)
    result = plane.polyline(
        ViewerPolylineControlOptions(
            route_key="p", vertices_yx=((4.5, 3.0), (4.5, 8.0)), line_width=3
        )
    )
    np.testing.assert_allclose(result.profile_values, raw[4, 3:9] + 10)
    assert result.statistics.count == 6
    nearest = plane.polyline(
        ViewerPolylineControlOptions(
            route_key="p", vertices_yx=((4.2, 3.0), (4.2, 8.0)), interpolation_order=0
        )
    )
    np.testing.assert_array_equal(nearest.profile_values, raw[4, 3:9])
    assert result.reduction.startswith("mean")


def test_source_crop_origin_excludes_display_padding_and_keeps_world_coordinates():
    raw = np.arange(100, dtype=np.uint16).reshape(10, 10)
    plane = NativeImageMeasurement(
        raw, (100, 200), lambda p: (p[0] * 2 + 7, p[1] * 3 + 11)
    )
    result = plane.polyline(
        ViewerPolylineControlOptions(
            route_key="crop", vertices_yx=((102.0, 202.0), (102.0, 205.0))
        )
    )
    assert result.profile_values == (22.0, 23.0, 24.0, 25.0)
    assert result.world_vertices[0] == (211.0, 617.0)
    with pytest.raises(ValueError, match="padding/out-of-bounds"):
        plane.polyline(
            ViewerPolylineControlOptions(
                route_key="crop", vertices_yx=((0.0, 0.0), (2.0, 2.0))
            )
        )


def test_independent_region_background_geometry_raw_support_and_readonly():
    raw = np.full((64, 64), 5.0, dtype=float)
    raw[10:20, 10:20] = 80
    raw[10, 10] = 5
    plane = NativeImageMeasurement(raw, (0, 0), lambda p: (2 * p[0] + 7, 3 * p[1] + 11))
    vertices = ((10.0, 10.0), (10.0, 19.0), (19.0, 19.0), (19.0, 10.0))
    background = ((30.0, 30.0), (30.0, 34.0), (34.0, 34.0), (34.0, 30.0))
    original = raw.copy()
    result = plane.region(
        ViewerRegionControlOptions(
            route_key="p", vertices_yx=vertices, background_vertices_yx=background
        )
    )
    assert result.polygon.area == 81
    assert result.polygon.perimeter == 36
    assert result.polygon.extent == 1
    assert result.polygon.roundness == pytest.approx(pi_over_four := np.pi / 4)
    assert result.raster.area_pixels == 100
    assert result.raster.bbox_yx == (10, 10, 20, 20)
    assert result.raster.centroid_yx == (14.5, 14.5)
    assert result.world_area == 486
    assert result.world_perimeter == 90
    assert result.world_roundness != pytest.approx(pi_over_four)
    assert result.statistics.mean == 79.25
    assert result.background_statistics.count == 25
    assert result.background_statistics.standard_deviation == 0
    assert result.support_threshold == 5
    assert result.support_count == 99
    assert result.support_fraction == 0.99
    assert result.foreground_minus_background_mean == 74.25
    np.testing.assert_array_equal(raw, original)
    explicit = plane.region(
        ViewerRegionControlOptions(
            route_key="p", vertices_yx=vertices, support_threshold=79.0
        )
    )
    assert explicit.support_count == 99
    assert explicit.background_statistics is None


def test_region_registered_route_dispatch_and_native_affine():
    server, layer, _ = native_route()
    before = presentation(server.viewer, layer)
    request = ViewerRegionControlOptions(
        route_key="source",
        axis_indices={"channel": 1},
        vertices_yx=((10.0, 10.0), (10.0, 19.0), (19.0, 19.0), (19.0, 10.0)),
        support_threshold=1100.0,
    )
    response = dispatch(server, OpenHCSViewerControlMessageType.MEASURE_REGION, request)
    assert response["status"] == "success", response
    assert response["coordinates"]["components"]["channel"] == 2
    assert response["measurement"]["statistics"]["minimum"] == 1110
    assert presentation(server.viewer, layer) == before
    affine = np.eye(4)
    affine[1, 2] = 0.5
    layer.affine = affine
    result = dispatch(server, OpenHCSViewerControlMessageType.MEASURE_REGION, request)
    assert result["status"] == "success", result
    assert result["measurement"]["world_area"] == pytest.approx(486)
    assert result["measurement"]["world_perimeter"] > 90


@pytest.mark.parametrize(
    "changes",
    [
        {"axis_indices": {}},
        {"axis_indices": {"channel": 2}},
        {"axis_indices": {"z_index": 0}},
        {"route_key": "absent"},
    ],
)
def test_wrong_missing_or_outside_route_axes_rejected_without_presentation_change(
    changes,
):
    server, layer, _ = native_route()
    before = presentation(server.viewer, layer)
    response = dispatch(
        server,
        OpenHCSViewerControlMessageType.MEASURE_POLYLINE,
        replace(line(), **changes),
    )
    assert response["status"] == "error"
    assert presentation(server.viewer, layer) == before


def test_sparse_padding_duplicate_and_unmounted_route_are_not_source_measurements():
    server, layer, _ = native_route()
    items = server.component_groups.items_for("source")
    items.pop()
    request = replace(line(), axis_indices={"channel": 1})
    assert (
        dispatch(server, OpenHCSViewerControlMessageType.MEASURE_POLYLINE, request)[
            "status"
        ]
        == "error"
    )
    items.append(items[0])
    assert (
        dispatch(server, OpenHCSViewerControlMessageType.MEASURE_POLYLINE, line())[
            "status"
        ]
        == "error"
    )
    server.viewer.layers.remove(layer)
    assert (
        dispatch(server, OpenHCSViewerControlMessageType.MEASURE_POLYLINE, line())[
            "status"
        ]
        == "error"
    )


@pytest.mark.parametrize(
    "changes",
    [
        {"vertices_yx": ((np.nan, 2.0), (3.0, 4.0))},
        {"vertices_yx": ((np.inf, 2.0), (3.0, 4.0))},
        {"vertices_yx": ((True, 2.0), (3.0, 4.0))},
        {"vertices_yx": ((1.0, 2.0, 3.0), (3.0, 4.0, 5.0))},
        {"vertices_yx": ((1.0, 2.0),) * 65},
        {"line_width": True},
        {"line_width": 32},
        {"interpolation_order": 2},
        {"interpolation_order": True},
        {"max_samples": 4097},
        {"max_pixels": 262145},
        {"axis_indices": {"channel": -1}},
        {"axis_indices": {"channel": True}},
    ],
)
def test_invalid_coordinates_and_bounds_fail_at_control_boundary(changes):
    with pytest.raises((ValueError, TypeError)):
        replace(line(), **changes)


@pytest.mark.parametrize(
    "changes",
    [
        {"vertices_yx": ((1.0, 1.0), (1.0, 1.0))},
        {"vertices_yx": ((1.0, 1.0), (1e100, 1.0))},
        {"vertices_yx": ((0.0, 0.0), (0.0, 10.0)), "line_width": 3},
        {"max_samples": 3},
        {"max_pixels": 3},
    ],
)
def test_failure_limits_before_pixel_read_or_interpolation(monkeypatch, changes):
    import openhcs.runtime.viewer_measurements as math

    def forbidden(*args, **kwargs):
        raise AssertionError("Array/interpolation started before admission")

    monkeypatch.setattr(math.NativeMeasurementWindow, "read", forbidden)
    monkeypatch.setattr(math, "profile_line", forbidden)
    plane = NativeImageMeasurement(np.ones((64, 64)), (0, 0), lambda p: p)
    with pytest.raises(ValueError):
        plane.polyline(replace(line(), **changes))


@pytest.mark.parametrize(
    "vertices,budget",
    [
        (((1.0, 1.0), (10.0, 10.0), (1.0, 10.0), (10.0, 1.0)), 262144),
        (((1.0, 1.0), (2.0, 2.0), (3.0, 3.0)), 262144),
        (((1.0, 1.0), (10.0, 1.0), (10.0, 10.0), (1.0, 10.0)), 2),
        (((-1.0, 1.0), (10.0, 1.0), (10.0, 10.0), (1.0, 10.0)), 262144),
    ],
)
def test_region_rejection_precedes_mask_allocation(monkeypatch, vertices, budget):
    import openhcs.runtime.viewer_measurements as math

    monkeypatch.setattr(
        math,
        "grid_points_in_poly",
        lambda *a, **kw: pytest.fail("allocated region before admission"),
    )
    with pytest.raises(ValueError):
        NativeImageMeasurement(np.ones((64, 64)), (0, 0), lambda p: p).region(
            ViewerRegionControlOptions(
                route_key="p", vertices_yx=vertices, max_pixels=budget
            )
        )


def test_nonfinite_pixels_unsupported_rank_and_background_overlap_rejected():
    with pytest.raises(ValueError):
        NativeImageMeasurement(np.ones((2, 4, 4)), (0, 0), lambda p: p)
    raw = np.ones((64, 64))
    raw[10, 12] = np.nan
    plane = NativeImageMeasurement(raw, (0, 0), lambda p: p)
    with pytest.raises(ValueError, match="nonfinite"):
        plane.polyline(line())
    vertices = ((10.0, 10.0), (10.0, 19.0), (19.0, 19.0), (19.0, 10.0))
    with pytest.raises(ValueError, match="overlap"):
        NativeImageMeasurement(np.ones((64, 64)), (0, 0), lambda p: p).region(
            ViewerRegionControlOptions(
                route_key="p", vertices_yx=vertices, background_vertices_yx=vertices
            )
        )


class InProcessMeasurementGateway(ZMQViewerWindowGateway):
    """Source-level native ingress test, not claimed as live transport acceptance."""

    def __init__(self, server):
        self.server = server

    def _send_control_message(self, request, message):
        return NapariControlMessageAction.for_message_type(message["type"]).handle(
            self.server, pickle.loads(pickle.dumps(message))
        )


def service_request():
    return ViewerWindowPolylineMeasurementRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5981),
        route_key="source",
        axis_indices={"channel": 0},
        vertices_yx=[(10.0, 10.0), (10.0, 19.0), (19.0, 19.0)],
    )


def test_service_dto_serialization_provenance_and_response_identity_rejection():
    server, _, _ = native_route()
    gateway = InProcessMeasurementGateway(server)
    service = ViewerWindowService(gateway=gateway)
    result = service.measure_polyline(service_request())
    assert result.observed, result.errors
    assert result.measurement.world_length == 45
    restored = dataclass_from_mapping(
        ViewerWindowPolylineMeasurementResult,
        json.loads(json.dumps(to_jsonable(result))),
    )
    assert restored == result
    assert pickle.loads(pickle.dumps(service_request())) == service_request()
    original = gateway._send_control_message

    def corrupt(request, message):
        response = original(request, message)
        response["coordinates"]["route_key"] = "foreign"
        return response

    gateway._send_control_message = corrupt
    failure = service.measure_polyline(service_request())
    assert not failure.observed
    assert failure.errors[0].code == "viewer_feature_measurement_failed"


def test_automatic_registry_and_mcp_projection_are_readonly_and_strict():
    from openhcs.mcp.server import build_server

    server, _, _ = native_route()
    context = SimpleNamespace(
        viewer_window_service=ViewerWindowService(
            gateway=InProcessMeasurementGateway(server)
        )
    )
    built = build_server(context)
    tools = asyncio.run(built.list_tools())
    selected = {
        tool.name: tool
        for tool in tools
        if tool.name.startswith("openhcs_measure_viewer_")
    }
    assert set(selected) == {
        "openhcs_measure_viewer_polyline",
        "openhcs_measure_viewer_region",
    }
    assert all(tool.annotations.readOnlyHint is True for tool in selected.values())
    discovery = get_capability_registry().search(
        AgentCapabilitySearchRequest(text="native", has_side_effects=False, limit=50)
    )
    assert set(selected) <= {c.name for c in discovery.capabilities}
    schema = selected["openhcs_measure_viewer_polyline"].inputSchema
    assert {"route_key", "axis_indices", "vertices_yx"} <= set(schema["required"])

    async def journey():
        good = await built.call_tool(
            "openhcs_measure_viewer_polyline", service_request().as_tool_arguments()
        )
        structured = good[1] if isinstance(good, tuple) else good.structuredContent
        assert structured["measurement"]["data_length"] == 18, structured
        region_arguments = ViewerWindowRegionMeasurementRequest.from_fields(
            connection=ExecutionConnectionSpec(port=5981),
            route_key="source",
            axis_indices={"channel": 0},
            vertices_yx=[(10.0, 10.0), (10.0, 19.0), (19.0, 19.0), (19.0, 10.0)],
            background_vertices_yx=[
                (30.0, 30.0),
                (30.0, 34.0),
                (34.0, 34.0),
                (34.0, 30.0),
            ],
        ).as_tool_arguments()
        region = await built.call_tool(
            "openhcs_measure_viewer_region", region_arguments
        )
        structured_region = (
            region[1] if isinstance(region, tuple) else region.structuredContent
        )
        assert structured_region["measurement"]["raster"]["area_pixels"] == 100
        assert structured_region["measurement"]["background_statistics"]["count"] == 25
        bad = service_request().as_tool_arguments()
        bad["line_width"] = True
        with pytest.raises(Exception, match="integer|validation"):
            await built.call_tool("openhcs_measure_viewer_polyline", bad)

    asyncio.run(journey())


@pytest.mark.parametrize(
    "transform",
    [
        lambda p: (0, 0),
        lambda p: (float("inf"), p[1]),
        lambda p: (p[0] * 1e307, p[1] * 1e307),
    ],
)
def test_invalid_world_geometry_rejected_before_pixel_reads(monkeypatch, transform):
    from openhcs.runtime.viewer_measurements import NativeMeasurementWindow

    def forbidden(*args):
        pytest.fail("world admission must precede reading source pixels")

    monkeypatch.setattr(NativeMeasurementWindow, "read", forbidden)
    plane = NativeImageMeasurement(np.ones((64, 64)), (0, 0), transform)
    with pytest.raises(ValueError, match="transform"):
        plane.polyline(line())
    with pytest.raises(ValueError, match="transform"):
        plane.region(
            ViewerRegionControlOptions(
                route_key="p",
                vertices_yx=((10.0, 10.0), (10.0, 19.0), (19.0, 19.0), (19.0, 10.0)),
            )
        )


def test_non_spatial_display_and_unsupported_source_rank_fail_readonly():
    server, layer, _ = native_route()
    server.viewer.dims.order = (1, 0, 2)
    before = presentation(server.viewer, layer)
    result = dispatch(server, OpenHCSViewerControlMessageType.MEASURE_POLYLINE, line())
    assert result["status"] == "error"
    assert "spatial display axes" in result["message"]
    assert presentation(server.viewer, layer) == before
    with pytest.raises(ValueError, match="2D"):
        NativeImageMeasurement(np.ones((2, 3, 4)), (0, 0), lambda p: p)
    with pytest.raises(TypeError, match="real numeric"):
        NativeImageMeasurement(np.ones((3, 4), dtype=complex), (0, 0), lambda p: p)


def test_live_journey_fixture_uses_real_persisted_known_source_planes(tmp_path):
    import importlib.util
    from pathlib import Path
    from openhcs.core.image_file_serialization import ImageFileFormat

    script = (
        Path(__file__).resolve().parents[1]
        / "diagnostics/check_viewer_feature_measurement_live.py"
    )
    spec = importlib.util.spec_from_file_location("measurement_live_fixture", script)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    paths = module.make_fixture(tmp_path / "fixture")
    assert len(paths) == 2
    gradient = ImageFileFormat.require_path(paths[0]).read(paths[0])
    region = ImageFileFormat.require_path(paths[1]).read(paths[1])
    assert gradient.shape == (64, 64) and gradient.dtype == np.uint16
    np.testing.assert_array_equal(gradient[10, 10:20], np.arange(110, 120))
    assert region[10:20, 10:20].mean() == 79.25
    assert region[30:35, 30:35].mean() == 5
    assert (paths[0].parent / "openhcs_metadata.json").is_file()
