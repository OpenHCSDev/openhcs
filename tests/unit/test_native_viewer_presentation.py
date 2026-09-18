"""Native viewer calibration and camera contracts, without external UI calls."""

import json
from dataclasses import fields, replace
from types import SimpleNamespace

import numpy as np
import pytest
from napari.components import ViewerModel
from napari.layers import Image, Points, Shapes
from polystore.streaming.identity import (
    FixedStreamProducerIdentityKind,
    StreamProducerIdentity,
)
from polystore.streaming.receivers.core.viewport_presentation import (
    NativeViewportPresentationABC,
)
from polystore.streaming.receivers.napari.viewport_presentation import (
    NapariNativeViewportPresentation,
)
from polystore.streaming_constants import StreamingDataType
from zmqruntime.viewer_protocol import ViewerNativeViewportPresentation, ViewerWireField

from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import ViewerWindowViewportRequest
from openhcs.agent.services.viewer_window_service import (
    ViewerWindowGatewayABC,
    ViewerWindowService,
)
from openhcs.core.config import NapariDisplayConfig
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_metadata import SourceVoxelSpacing, SourceVoxelSpacingUnit
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.steps.stream_component_semantics import (
    StreamImagePayloadMetadataProjector,
)
from openhcs.runtime.napari_streaming_handlers import (
    NapariAxisPresentation,
    NapariStreamLayerAddress,
    NapariStreamLayerItem,
)
from openhcs.runtime.napari_viewer_server import (
    NapariControlMessageAction,
    NapariStreamLayerContext,
    PayloadMap,
)
from openhcs.runtime.viewer_component_system import (
    ViewerComponentAxisSemanticsAuthority,
    ViewerComponentLayout,
    ViewerComponentValueDomainPayload,
    ViewerLayerAxisProjection,
)
from openhcs.runtime.viewer_protocol import (
    ViewerControlMessageType,
    ViewerControlResponseField,
)


def presentation():
    semantics = ViewerComponentAxisSemanticsAuthority.empty()
    return NapariAxisPresentation(
        entries=semantics.entries,
        layout=ViewerComponentLayout.from_parts(component_modes={}, component_order=()),
        route_key="paired",
        projection=ViewerLayerAxisProjection(
            projected_axis_components=(),
            component_values={},
            routed_component_values={},
            axis_offsets=(),
            scalar_component_values={},
        ),
    )


def layer_item(metadata):
    return NapariStreamLayerItem(
        data=np.zeros((4, 5), dtype=np.uint16),
        producer=StreamProducerIdentity.fixed_output(
            FixedStreamProducerIdentityKind.MANUAL, "paired"
        ),
        address=NapariStreamLayerAddress({}, "paired.tif", StreamingDataType.IMAGE),
        image_metadata=metadata,
        plane_component_domain=ViewerComponentValueDomainPayload(()),
    )


def test_selected_metadata_wire_derives_declarations_and_preserves_batch_compatibility():
    metadata = ImagePayloadMetadata(
        source_path="/source/one.tif",
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
        source_spatial_domain=SourceSpatialDomain((0, 0), (4, 5)),
    )
    wire = StreamImagePayloadMetadataProjector.item_fields(metadata, ())
    selected = wire[ViewerWireField.IMAGE_METADATA.value]
    assert set(selected) == {
        member.name
        for member in fields(ImagePayloadMetadata)
        if member.metadata.get(ViewerWireField.IMAGE_METADATA, False)
    }
    restored = ImagePayloadMetadata.from_viewer_image_metadata(
        json.loads(json.dumps(selected))
    )
    assert restored.source_voxel_spacing == metadata.source_voxel_spacing
    assert restored.source_spatial_domain == metadata.source_spatial_domain
    assert restored.source_path is None
    other = metadata.replace_fields(source_path="/source/two.tif")
    assert StreamImagePayloadMetadataProjector.item_fields(other, ()) == wire
    producer = layer_item(metadata).producer
    context = NapariStreamLayerContext.from_payload_map(
        PayloadMap(
            {
                **wire,
                "producer_identity": producer.to_payload(),
                "metadata": {},
                "path": "paired.tif",
            },
            "test",
        ),
        ViewerComponentAxisSemanticsAuthority.empty(),
        NapariDisplayConfig(),
    )
    assert context.image_metadata.source_voxel_spacing == metadata.source_voxel_spacing
    legacy = dict(wire)
    legacy.pop(ViewerWireField.IMAGE_METADATA.value)
    context = NapariStreamLayerContext.from_payload_map(
        PayloadMap(
            {
                **legacy,
                "producer_identity": producer.to_payload(),
                "metadata": {},
                "path": "paired.tif",
            },
            "test",
        ),
        ViewerComponentAxisSemanticsAuthority.empty(),
        NapariDisplayConfig(),
    )
    assert not context.image_metadata.source_voxel_spacing.has_values
    assert context.image_metadata.source_spatial_domain.source_shape_yx == (4, 5)


@pytest.mark.parametrize(
    "value",
    (
        None,
        [],
        {"source_path": "/hidden"},
        {"source_voxel_spacing": {"values_zyx": [-1, 1]}},
    ),
)
def test_malformed_new_metadata_never_falls_back_to_legacy(value):
    item = layer_item(ImagePayloadMetadata())
    with pytest.raises((TypeError, ValueError)):
        NapariStreamLayerContext.from_payload_map(
            PayloadMap(
                {
                    "producer_identity": item.producer.to_payload(),
                    "metadata": {},
                    "path": "paired.tif",
                    "image_metadata": value,
                    "spatial_origin_yx": [0, 0],
                },
                "test",
            ),
            ViewerComponentAxisSemanticsAuthority.empty(),
            NapariDisplayConfig(),
        )


@pytest.mark.parametrize(
    "spacing",
    (
        SourceVoxelSpacing((0.5, 1.25)),
        SourceVoxelSpacing(),
        SourceVoxelSpacing((1, 2), unit=SourceVoxelSpacingUnit.RELATIVE),
    ),
)
def test_native_image_shapes_and_graph_points_share_calibrated_world_domain(spacing):
    metadata = ImagePayloadMetadata(source_voxel_spacing=spacing)
    kwargs = presentation().spatial_layer_kwargs([layer_item(metadata)])
    pixels = np.zeros((4, 5), dtype=np.uint16)
    image = Image(pixels, **kwargs)
    shapes = Shapes(
        [np.array([[0, 0], [0, 3], [3, 3]])], shape_type="polygon", **kwargs
    )
    points = Points(np.array([[2, 3]]), **kwargs)
    assert image.data is pixels
    assert tuple(image.scale) == spacing.spacing_for_ndim(2)
    assert tuple(image.units) == tuple(shapes.units) == tuple(points.units)
    assert (
        image.data_to_world((2, 3))
        == shapes.data_to_world((2, 3))
        == points.data_to_world((2, 3))
    )
    rgb = Image(np.zeros((4, 5, 3), dtype=np.uint8), rgb=True, **kwargs)
    assert rgb.ndim == 2 and tuple(rgb.scale) == tuple(image.scale)


def test_conflicting_route_calibration_fails_closed():
    with pytest.raises(ValueError, match="consistent"):
        presentation().spatial_layer_kwargs(
            [
                layer_item(
                    ImagePayloadMetadata(
                        source_voxel_spacing=SourceVoxelSpacing((1, 1))
                    )
                ),
                layer_item(
                    ImagePayloadMetadata(
                        source_voxel_spacing=SourceVoxelSpacing((2, 2))
                    )
                ),
            ]
        )


def test_native_display_handlers_apply_shared_calibration_after_wire_roundtrip():
    from openhcs.runtime.napari_streaming_handlers import (
        NapariImagePayloadAxisLabelPolicy,
        NapariLayerRouteStateStore,
    )
    from openhcs.runtime.napari_viewer_server import (
        NapariImageLayerDisplayHandler,
        NapariLayerDisplayRequest,
        NapariPointsLayerDisplayHandler,
        NapariShapesLayerDisplayHandler,
    )

    viewer = ViewerModel()
    routes = NapariLayerRouteStateStore.empty()
    server = SimpleNamespace(
        viewer=viewer,
        layer_route_state=routes,
        bind_result_selection_layer=lambda layer: None,
    )
    pipeline = SimpleNamespace(
        server=server,
        payload_axis_policy=NapariImagePayloadAxisLabelPolicy(),
        dimension_label_store=SimpleNamespace(apply=lambda value: None),
        dimension_label_overlay=SimpleNamespace(setup_for_layer=lambda route: None),
    )
    metadata = ImagePayloadMetadata(
        source_voxel_spacing=SourceVoxelSpacing((1.3556, 1.3556)),
        source_spatial_domain=SourceSpatialDomain((0, 0), (4, 5)),
    )
    restored = ImagePayloadMetadata.from_viewer_image_metadata(
        json.loads(json.dumps(metadata.to_viewer_image_metadata()))
    )
    image_item = layer_item(restored)
    for route, handler, data_type, data in (
        (
            "neurite",
            NapariImageLayerDisplayHandler(),
            StreamingDataType.IMAGE,
            np.zeros((4, 5), dtype=np.uint16),
        ),
        (
            "nucleus",
            NapariImageLayerDisplayHandler(),
            StreamingDataType.IMAGE,
            np.ones((4, 5), dtype=np.uint16),
        ),
        (
            "roi",
            NapariShapesLayerDisplayHandler(),
            StreamingDataType.SHAPES,
            [
                {
                    "type": "polygon",
                    "coordinates": [[0, 0], [0, 3], [3, 3]],
                    "metadata": {"source_spatial_shape_yx": [4, 5]},
                }
            ],
        ),
        (
            "graph",
            NapariPointsLayerDisplayHandler(),
            StreamingDataType.POINTS,
            [{"type": "points", "coordinates": [[2, 3]], "metadata": {}}],
        ),
    ):
        routes.set_title(route, route)
        item = replace(
            image_item,
            data=data,
            address=NapariStreamLayerAddress({}, route, data_type),
        )
        handler.handle(
            NapariLayerDisplayRequest(
                pipeline=pipeline,
                items=[item],
                presentation=replace(presentation(), route_key=route),
                display_config=NapariDisplayConfig(),
            )
        )
    assert len(viewer.layers) == 4
    for layer in viewer.layers:
        np.testing.assert_array_equal(layer.scale, (1.3556, 1.3556))
        assert layer.data_to_world((2, 3)) == (2.7112, 4.0668)
        assert tuple(str(unit) for unit in layer.units) == ("micrometer", "micrometer")


def test_two_dimensional_calibration_does_not_calibrate_component_z_axis():
    from zmqruntime.viewer_protocol import ViewerComponentMode

    axis = replace(
        presentation(),
        layout=ViewerComponentLayout.from_parts(
            component_modes={"z_index": ViewerComponentMode.STACK},
            component_order=("z_index",),
        ),
    )
    kwargs = axis.spatial_layer_kwargs(
        [
            layer_item(
                ImagePayloadMetadata(source_voxel_spacing=SourceVoxelSpacing((0.5, 1)))
            )
        ]
    )
    assert kwargs["scale"] == (1, 0.5, 1)
    assert kwargs["units"] == ("dimensionless", "micrometer", "micrometer")


@pytest.mark.parametrize(
    "center, zoom",
    (
        ([1, 2], 1),
        ([True, 2, 3], 1),
        ([0, 1, float("inf")], 1),
        ([0, 1, 2], False),
        ([0, 1, 2], 0),
        ([0, 1, 2], float("nan")),
    ),
)
def test_viewport_contract_rejects_invalid_values(center, zoom):
    with pytest.raises((TypeError, ValueError)):
        ViewerNativeViewportPresentation(center, zoom)


def test_native_camera_registered_action_readback_preserves_other_state():
    viewer = ViewerModel()
    pixels = np.arange(20, dtype=np.uint16).reshape(4, 5)
    layer = viewer.add_image(pixels, scale=(1.3556, 1.3556))
    original_step = viewer.dims.current_step
    original_axes = viewer.dims.axis_labels
    original_selection = tuple(viewer.layers.selection)
    original_angles = viewer.camera.angles
    control = NapariNativeViewportPresentation.for_viewer(viewer)
    assert isinstance(control, NativeViewportPresentationABC)
    desired = ViewerNativeViewportPresentation((0, 2.5, 3.75), 2)
    assert (
        ViewerNativeViewportPresentation.from_wire_mapping(desired.to_wire_mapping())
        == desired
    )
    action = NapariControlMessageAction.for_message_type(
        ViewerControlMessageType.VIEWPORT.value
    )
    assert action.transport_thread_response(SimpleNamespace(viewer=viewer), {}) is None
    reply = action.handle(
        SimpleNamespace(viewer=viewer),
        {ViewerControlResponseField.PAYLOAD.value: desired},
    )
    assert reply["status"] == "success"
    assert (
        ViewerNativeViewportPresentation.from_wire_mapping(reply["native_viewport"])
        == control.snapshot()
        == desired
    )
    viewer.camera.zoom = 3
    assert control.snapshot().zoom == 3  # no cached request mirror
    assert layer.data is pixels
    np.testing.assert_array_equal(layer.scale, (1.3556, 1.3556))
    assert viewer.dims.current_step == original_step
    assert viewer.dims.axis_labels == original_axes
    assert tuple(viewer.layers.selection) == original_selection
    assert viewer.camera.angles == original_angles
    viewer.dims.ndisplay = 3
    assert (
        action.handle(SimpleNamespace(viewer=viewer), {"payload": desired})["status"]
        == "error"
    )
    with pytest.raises(ValueError, match="2D"):
        control.apply(desired)


def test_generic_viewport_receiver_import_does_not_load_napari_or_pydantic():
    import os
    import subprocess
    import sys

    environment = dict(os.environ, PYTHONPATH=os.pathsep.join(sys.path))
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            "import sys; from polystore.streaming.receivers.core.viewport_presentation import NativeViewportPresentationABC; assert 'napari' not in sys.modules; assert 'pydantic' not in sys.modules",
        ],
        env=environment,
        capture_output=True,
        text=True,
        timeout=20,
    )
    assert result.returncode == 0, result.stderr


class CameraGateway(ViewerWindowGatewayABC):
    def close_window(self, request):
        raise AssertionError(request)

    def viewport(self, request):
        return {
            "status": "success",
            "native_viewport": ViewerNativeViewportPresentation(
                (0, 9, 11), 4
            ).to_wire_mapping(),
        }

    def image_intensity(self, request):
        raise AssertionError(request)

    def snapshot_window(self, request):
        raise AssertionError(request)

    def window_state(self, request):
        raise AssertionError(request)

    def window_payloads(self, request):
        raise AssertionError(request)

    def navigate_window(self, request):
        raise AssertionError(request)

    def isolate_layers(self, request):
        raise AssertionError(request)


def test_service_returns_native_acknowledgement_not_requested_echo():
    request = ViewerWindowViewportRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5585),
        presentation=ViewerNativeViewportPresentation((0, 1, 2), 2),
    )
    result = ViewerWindowService(gateway=CameraGateway()).viewport(request)
    assert result.applied
    assert result.native_viewport == ViewerNativeViewportPresentation((0, 9, 11), 4)


def test_mcp_viewport_schema_and_invocation_are_derived_from_typed_contract():
    import asyncio
    import inspect

    from mcp.server.fastmcp.exceptions import ToolError

    from openhcs.mcp.context import OpenHCSAgentContext
    from openhcs.mcp.server import build_server

    class NativeGateway(CameraGateway):
        def __init__(self):
            self.viewer = ViewerModel()
            self.calls = 0
            self.intensity_calls = 0

        def viewport(self, request):
            self.calls += 1
            control = NapariNativeViewportPresentation(self.viewer)
            control.apply(request.presentation)
            return {
                "status": "success",
                "native_viewport": control.snapshot().to_wire_mapping(),
            }

        def image_intensity(self, request):
            self.intensity_calls += 1
            raise AssertionError("Malformed presentation reached the native adapter")

    gateway = NativeGateway()
    built = build_server(
        OpenHCSAgentContext(viewer_window_service=ViewerWindowService(gateway=gateway))
    )
    listed = built.list_tools()
    tools = asyncio.run(listed) if inspect.isawaitable(listed) else listed
    schema = next(
        tool.inputSchema for tool in tools if tool.name == "openhcs_set_viewer_viewport"
    )
    assert "presentation" in schema["properties"]
    declaration = schema["properties"]["presentation"]
    properties = schema["$defs"][declaration["$ref"].rsplit("/", 1)[-1]]["properties"]
    assert set(properties) == {
        member.name for member in fields(ViewerNativeViewportPresentation)
    }
    request = ViewerWindowViewportRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5585),
        presentation=ViewerNativeViewportPresentation((0, 1, 2), 2),
    )
    response = asyncio.run(
        built.call_tool("openhcs_set_viewer_viewport", request.as_tool_arguments())
    )
    _content, structured = response
    assert structured["applied"] is True
    assert structured["native_viewport"] == {
        "center": [0, 1, 2],
        "zoom": 2,
    }
    previous = NapariNativeViewportPresentation(gateway.viewer).snapshot()
    for presentation in (
        {"center": [0, 1, 2], "zoom": True},
        {"center": [0, True, 2], "zoom": 1},
    ):
        with pytest.raises(ToolError):
            asyncio.run(
                built.call_tool(
                    "openhcs_set_viewer_viewport",
                    {
                        "port": 5585,
                        "presentation": presentation,
                    },
                )
            )
    for presentation in (
        {"contrast_limits": [0, True], "gamma": 1},
        {"contrast_limits": [0, 1], "gamma": True},
    ):
        with pytest.raises(ToolError):
            asyncio.run(
                built.call_tool(
                    "openhcs_set_viewer_image_intensity",
                    {
                        "port": 5585,
                        "route_key": "image",
                        "presentation": presentation,
                    },
                )
            )
    assert gateway.calls == 1
    assert gateway.intensity_calls == 0
    assert NapariNativeViewportPresentation(gateway.viewer).snapshot() == previous


@pytest.mark.parametrize("well", ("A01", "1"))
def test_selected_file_stream_restores_persisted_crop_calibration_and_native_batching(
    tmp_path, monkeypatch, well
):
    from polystore.disk import DiskStorageBackend
    from polystore.filemanager import FileManager
    from polystore.streaming.viewer_transport import ViewerStreamKwarg
    from polystore.virtual_workspace import SourcePixelRef

    from openhcs.constants.constants import Microscope
    from openhcs.core.config import NapariStreamingConfig
    from openhcs.core.image_file_serialization import ImageFileFormat
    from openhcs.core.source_image_provenance import (
        SourceImageProvenance,
        SourceImageProvenanceContributor,
        SourceImageProvenancePlaneRecord,
        SourceImageProvenancePlanes,
    )
    from openhcs.core.source_projection import (
        OpenHCSPlaneAddress,
        SourcePlaneProjection,
        SourceProjectionSet,
    )
    from openhcs.core.viewer_streaming_service import (
        ImageStreamingRequest,
        StreamingService,
    )
    from openhcs.core.virtual_workspace_metadata import AtomicMetadataWriter
    from openhcs.microscopes.microscope_base import create_microscope_handler
    from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

    filemanager = FileManager({"disk": DiskStorageBackend()})
    parser = SourceSchemaFilenameParser()
    projections = []
    arrays = []
    spacing = SourceVoxelSpacing((1.3556, 1.3556))
    domain = SourceSpatialDomain((7, 11), (20, 30), 0, "Retained crop")
    for channel in (1, 2):
        address = OpenHCSPlaneAddress.from_values(well, 1, channel, 1, 1)
        component_metadata = {
            component.value: value
            for component, value in address.component_values().items()
        }
        contributors = tuple(
            SourceImageProvenancePlaneRecord(
                path=str(tmp_path / f"synthetic-site{site}-channel{channel}.tif"),
                component_metadata={**component_metadata, "site": site},
                identity_kind=SourceImageProvenanceContributor.identity_kind,
                source_image_name="neurite" if channel == 1 else "nucleus",
            )
            for site in range(1, 10)
        )
        metadata = ImagePayloadMetadata(
            source_voxel_spacing=spacing,
            source_spatial_domain=domain,
            source_provenance=SourceImageProvenance(
                source_component_metadata=component_metadata,
                source_image_names=("neurite" if channel == 1 else "nucleus",),
                source_image_provenance_planes=SourceImageProvenancePlanes.from_records(
                    contributors
                ),
            ),
        )
        path = tmp_path / f"stored-channel{channel}.tif"
        array = np.full((4, 5), channel, dtype=np.uint16)
        image_format = ImageFileFormat.require_path(path)
        payload = metadata.payload_with(array, None)
        image_format.write(path, payload)
        projections.append(
            SourcePlaneProjection(
                address,
                SourcePixelRef("disk", path.name),
                image_metadata=image_format.persisted_metadata(path, payload),
            )
        )
        arrays.append(array)
    subdirectory = SourceProjectionSet(tuple(projections)).metadata_dict(
        parser=parser,
        microscope_handler_name=Microscope.SOURCE_BINDINGS.value,
        source_filename_parser_name=type(parser).__name__,
        grid_dimensions=[],
        pixel_size=1.3556,
        main=True,
    )
    AtomicMetadataWriter().replace_subdirectory_metadata(
        tmp_path / "openhcs_metadata.json", ".", subdirectory
    )
    handler = create_microscope_handler("auto", tmp_path, filemanager)
    input_dir = handler.initialize_workspace(tmp_path, filemanager)
    service = StreamingService(filemanager, handler, input_dir)
    paths = tuple(subdirectory["image_files"])
    projection = service.source.source_workspace_projection()
    components = service.source.image_component_metadata_by_path(list(paths))
    loaded = tuple(
        service.source.load_image(
            path,
            "virtual_workspace",
            source_projection=projection,
            component_metadata=components[path],
        )
        for path in paths
    )
    for payload, array in zip(loaded, arrays, strict=True):
        assert payload.metadata.source_voxel_spacing == spacing
        assert payload.metadata.source_spatial_domain == domain
        assert payload.metadata.source_image_names in (("neurite",), ("nucleus",))
        assert (
            len(payload.metadata.source_provenance.represented_source_identities) == 9
        )
        assert payload.metadata.plane_axis is None
        np.testing.assert_array_equal(payload.data, array)

    # Native image secondaries have their own stored pixels, not the main-image
    # projection or a fabricated channel-plane declaration.
    artifact_path = input_dir / f"{well}_s001_w1_z001_t001_objects_step1.labels.tif"
    label_pixels = np.arange(2 * 8 * 9, dtype=np.int64).reshape(2, 8, 9)
    ImageFileFormat.require_path(artifact_path).write(artifact_path, label_pixels)
    artifact_components = service.source.image_component_metadata_by_path(
        [str(artifact_path)]
    )
    artifact = service.source.load_image(
        str(artifact_path),
        "disk",
        source_projection=projection,
        component_metadata=artifact_components[str(artifact_path)],
    )
    np.testing.assert_array_equal(artifact.data, label_pixels)
    assert artifact.metadata.source_dtype == "int64"
    assert artifact.metadata.source_channel_axis is None
    assert artifact.metadata.plane_axis is None
    assert artifact.metadata.source_spatial_domain.source_shape_yx == (8, 9)
    assert (
        artifact_components[str(artifact_path)]["well"] == components[paths[0]]["well"]
    )

    batches = []
    monkeypatch.setattr(
        filemanager,
        "save_batch",
        lambda data, paths, backend, **kwargs: batches.append((data, paths, kwargs)),
    )
    monkeypatch.setattr(service, "_wait_for_viewer_ready", lambda *_: None)
    monkeypatch.setattr(service, "_require_viewer_settled", lambda *_: None)
    service.stream_images(
        ImageStreamingRequest(
            viewer=SimpleNamespace(port=5585),
            config=NapariStreamingConfig(),
            status_callback=lambda _: None,
            error_callback=lambda _: None,
            filenames=paths,
            read_backend="virtual_workspace",
        )
    )
    assert len(batches) == 1  # Channel aliases/provenance must not split equal layout.
    data, streamed_paths, kwargs = batches[0]
    assert tuple(streamed_paths) == paths
    for actual, expected in zip(data, arrays, strict=True):
        np.testing.assert_array_equal(actual, expected)
    wire_metadata = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value].source.item_fields[
        "image_metadata"
    ]
    restored = ImagePayloadMetadata.from_viewer_image_metadata(wire_metadata)
    assert restored.source_voxel_spacing == spacing
    assert restored.source_spatial_domain == domain
    assert restored.plane_axis is None
    stream_request = kwargs[ViewerStreamKwarg.STREAM_REQUEST.value]
    declared_domain = stream_request.message_extra["component_value_domain"]
    projected_metadata = stream_request.source.metadata.metadata_by_path
    assert declared_domain["well"] == [well]
    assert {values["well"] for values in projected_metadata.values()} == {well}
    from openhcs.runtime.viewer_component_system import (
        ViewerLayerAxisProjectionRequest,
        ViewerLayerAxisProjector,
    )

    route_domain = {
        component: list(
            dict.fromkeys(values[component] for values in projected_metadata.values())
        )
        for component in declared_domain
    }
    axis_projection = ViewerLayerAxisProjector().project(
        ViewerLayerAxisProjectionRequest.from_component_values(
            projected_axis_components=tuple(declared_domain),
            route_component_values=route_domain,
            viewer_component_values=route_domain,
            declared_component_values=declared_domain,
        )
    )
    assert axis_projection.scalar_component_values["well"] == [well]
