"""Receipt-backed presentation uses original domains, never file-page inference."""

from dataclasses import replace
from dataclasses import fields
import asyncio
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest
from polystore import FileManager
from polystore.disk import DiskStorageBackend
from polystore.virtual_workspace import SourcePixelRef
from polystore.streaming.identity import (
    FixedStreamProducerIdentityKind,
    StreamProducerIdentity,
)
from zmqruntime.viewer_protocol import ViewerNativeLayerTransform

from openhcs.agent.dto.common import AgentResourceRef, SCHEMA_VERSION
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.plate import PlateFileStreamRequest
from openhcs.agent.dto.plate import PlateFileStreamResult
from openhcs.agent.dto.viewer import (
    ViewerWindowDescriptor,
    ViewerWindowLayerState,
    ViewerWindowStateResult,
)
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.plate_inspection_service import PlateInspectionService
from openhcs.agent.services.plate_streaming_service import PlateStreamingService
from openhcs.constants.constants import AllComponents
from openhcs.core.runtime_image_values import image_payload_metadata, image_payload_data
from openhcs.core.source_image_provenance import SourceImageProvenancePlanes
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.core.viewer_streaming_service import ViewerStreamingSource
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.core.plate_image_inventory import PlateFileRecord
from openhcs.serialization.json import to_jsonable


def receipt_state(path):
    fixed = {
        component.value: 1
        for component in AllComponents
        if component is not AllComponents.CHANNEL
    }
    fixed[AllComponents.WELL.value] = "1"
    summary = dict(
        path=str(path),
        data_type="image",
        components=fixed,
        aggregate_component_values={"channel": [2, 1]},
        shape=[2, 8, 9],
        source_spatial_shape_yx=[8, 9],
        spatial_origin_yx=[0, 0],
        dtype="int32",
    )
    layer = ViewerWindowLayerState(
        route_key="native_historical_labels",
        title="Labels",
        mounted=True,
        item_count=1,
        producer_identities=(
            StreamProducerIdentity.fixed_output(
                FixedStreamProducerIdentityKind.MANUAL, "synthetic_fixture"
            ),
        ),
        data_types=("image",),
        payload_summaries=(summary,),
        payload_summary_count=1,
        native_transform=ViewerNativeLayerTransform(scale=(1,) * 7, translate=(0,) * 7),
    )
    return ViewerWindowStateResult(
        schema_version=SCHEMA_VERSION,
        connection=ExecutionConnectionSpec(port=5631),
        observed=True,
        viewer=ViewerWindowDescriptor(ViewerType.NAPARI, "Synthetic"),
        viewer_ndim=7,
        layers=(layer,),
        layer_count=1,
    )


def test_receipt_codec_and_exact_path_admission(tmp_path):
    state = receipt_state(tmp_path / "aggregate.labels.tif")
    decoded = ViewerWindowStateResult.from_mapping(to_jsonable(state))
    record = decoded.image_payload_record_for(str(tmp_path / "aggregate.labels.tif"))
    assert record.components["well"] == "1"
    assert record.summary["aggregate_component_values"] == {"channel": [2, 1]}
    assert decoded.layers[0].producer_identities == state.layers[0].producer_identities
    with pytest.raises(ValueError, match="exactly one"):
        decoded.image_payload_record_for("another.labels.tif")
    with pytest.raises(ValueError, match="exactly one"):
        replace(
            decoded, layers=(*decoded.layers, *decoded.layers)
        ).image_payload_record_for(record.path)
    with pytest.raises((TypeError, ValueError)):
        ViewerWindowStateResult.from_mapping(
            {**to_jsonable(state), "invented_field": 1}
        )


@pytest.mark.parametrize(
    "change", ["transform", "truncated", "window", "shape", "producer", "bool_origin"]
)
def test_receipt_incomplete_or_conflicting_facts_refuse(tmp_path, change):
    state = receipt_state(tmp_path / "aggregate.labels.tif")
    layer = state.layers[0]
    if change == "transform":
        layer = replace(layer, native_transform=ViewerNativeLayerTransform())
    elif change == "truncated":
        layer = replace(layer, payload_summaries_truncated=True)
    elif change == "producer":
        layer = replace(layer, producer_identities=())
    else:
        summary = dict(layer.payload_summaries[0])
        if change == "bool_origin":
            summary["spatial_origin_yx"] = [False, 0]
        else:
            summary["spatial_origin_yx" if change == "window" else "shape"] = (
                [1, 0] if change == "window" else [True, 8, 9]
            )
        layer = replace(layer, payload_summaries=(summary,))
    with pytest.raises(ValueError):
        replace(state, layers=(layer,)).image_payload_record_for(
            str(tmp_path / "aggregate.labels.tif")
        )


@pytest.mark.parametrize(
    "values", [[2, 2], [1, "1"], [1, 1.0], [True, 2], [2], [float("nan"), 2]]
)
def test_declared_plane_domain_conflicts_fail_closed(tmp_path, values):
    record = receipt_state(tmp_path / "aggregate.labels.tif").image_payload_record_for(
        str(tmp_path / "aggregate.labels.tif")
    )
    with pytest.raises(ValueError):
        SourceImageProvenancePlanes.from_component_domain(
            path=record.path,
            fixed_components=record.components,
            aggregate_components={"channel": values},
            plane_count=2,
        )


def test_observed_and_declared_wire_domains_have_distinct_order_contracts():
    from openhcs.runtime.viewer_component_system import (
        ViewerComponentValueDomainPayload,
    )

    observed = ViewerComponentValueDomainPayload.from_wire_mapping(
        {"channel": ["2", 1, 2]}, context="observed"
    )
    assert observed.to_wire_mapping() == {"channel": [1, 2]}
    declared = ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
        {"channel": ["2", 1]}, context="declared"
    )
    assert declared.to_wire_mapping() == {"channel": [2, 1]}
    with pytest.raises(ValueError, match="unique after normalization"):
        ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
            {"channel": ["01", 1]}, context="malformed declared"
        )


def test_native_persisted_aggregate_source_projection_preserves_order(tmp_path):
    path = tmp_path / "aggregate.labels.tif"
    expected = np.arange(2 * 8 * 9, dtype=np.int64).reshape(2, 8, 9)
    manager = FileManager({"disk": DiskStorageBackend()})
    manager.save(expected, path, "disk")
    state = receipt_state(path)
    data = json.dumps(to_jsonable(state), sort_keys=True).encode()
    resource_path = tmp_path / "canonical-viewer-state.json"
    resource_path.write_bytes(data)
    resource = AgentResourceRef(
        uri=resource_path.as_uri(),
        title="Synthetic native receipt",
        path=str(resource_path),
        size_bytes=len(data),
        sha256=hashlib.sha256(data).hexdigest(),
    )
    inspection = PlateInspectionService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=()
        )
    )
    service = PlateStreamingService(inspection, object())
    context = SimpleNamespace(plate_path=tmp_path, filemanager=manager)
    request = PlateFileStreamRequest(plate_path=str(tmp_path), source_receipt=resource)
    source_record = PlateFileRecord(
        kind=PlateFileKind.IMAGE,
        key=str(path),
        source_ref=SourcePixelRef(backend="disk", backend_address=str(path)),
    )
    projection, producer = service._receipt_source_projection(
        request, (source_record,), context
    )
    assert producer is not None
    assert producer.identities == state.layers[0].producer_identities
    from openhcs.microscopes.source_schema import SourceSchemaFilenameParser

    source = ViewerStreamingSource(
        plate_path=str(tmp_path),
        filemanager=manager,
        microscope_handler=SimpleNamespace(parser=SourceSchemaFilenameParser()),
    )
    components = source.image_component_metadata_by_path([str(path)], projection)
    image = source.load_image(
        str(path),
        "disk",
        source_projection=projection,
        component_metadata=components[str(path)],
    )
    source.require_projected_image_window(str(path), image, projection)
    np.testing.assert_array_equal(image_payload_data(image), expected)
    metadata = image_payload_metadata(image)
    assert metadata.source_dtype == "int64"
    from openhcs.runtime.viewer_component_system import (
        ViewerComponentValueDomainPayload,
    )

    domain = ViewerComponentValueDomainPayload.from_ordered_wire_mapping(
        metadata.retained_plane_component_values(), context="native receipt domain"
    )
    assert domain.to_wire_mapping() == {"channel": [2, 1]}
    source_items = source.image_source_metadata_items(
        (str(path),), components, projection
    )
    component_order = tuple(component.value for component in AllComponents)
    assert tuple(
        item["channel"] for item in source_items.domain_metadata_items(component_order)
    ) == (2, 1)
    from openhcs.core.config import NapariDisplayConfig
    from openhcs.core.steps.stream_component_semantics import (
        StreamImagePayloadMetadataProjector,
    )
    from openhcs.runtime.napari_streaming_handlers import (
        NapariAggregateAxisBindingAuthority,
        NapariStreamLayerItem,
    )
    from openhcs.runtime.napari_viewer_server import (
        NapariStreamLayerContext,
        PayloadMap,
        _build_nd_image_array,
    )
    from openhcs.runtime.viewer_component_system import (
        ViewerComponentAxisSemanticsAuthority,
        ViewerLayerAxisProjection,
        ViewerMappingDisplayConfigInput,
    )
    from zmqruntime.viewer_protocol import ViewerWirePayload

    observed = ViewerComponentValueDomainPayload.from_wire_mapping(
        {"channel": [1, 2]}, context="observed stack domain"
    )
    semantics = ViewerComponentAxisSemanticsAuthority.from_display_config(
        ViewerMappingDisplayConfigInput(
            {"component_modes": {"channel": "stack"}, "component_order": ["channel"]}
        ),
        observed,
    )
    producer = StreamProducerIdentity.fixed_output(
        FixedStreamProducerIdentityKind.MANUAL, "selected_images"
    )
    native_context = NapariStreamLayerContext.from_payload_map(
        PayloadMap(
            ViewerWirePayload.mapping(
                {
                    **StreamImagePayloadMetadataProjector.item_fields(
                        metadata, component_order
                    ),
                    "producer_identity": producer.to_payload(),
                    "metadata": components[str(path)],
                    "path": str(path),
                },
                context="native receipt fixture",
            ),
            "receipt test",
        ),
        semantics,
        NapariDisplayConfig(),
    )
    assert native_context.plane_component_domain.to_wire_mapping() == {
        "channel": [2, 1]
    }
    item = NapariStreamLayerItem(
        **{
            member.name: getattr(native_context, member.name)
            for member in fields(NapariStreamLayerItem)
            if member.name != "data"
        },
        data=image_payload_data(image),
    )
    bindings = NapariAggregateAxisBindingAuthority.bindings([item], semantics)
    assert bindings.component_values == {"channel": [2, 1]}
    display_projection = ViewerLayerAxisProjection(
        projected_axis_components=("channel",),
        component_values={"channel": [1, 2]},
        routed_component_values={"channel": [1, 2]},
        axis_offsets=(0,),
        scalar_component_values={},
    )
    displayed = _build_nd_image_array([item], display_projection, bindings)
    np.testing.assert_array_equal(displayed[0], expected[1])
    np.testing.assert_array_equal(displayed[1], expected[0])
    assert not metadata.source_voxel_spacing.has_values
    assert metadata.source_channel_axis is None
    with pytest.raises(ValueError, match="window conflicts"):
        source.require_projected_image_window(
            str(path), metadata.payload_with(expected[:, :-1]), projection
        )
    with pytest.raises(ValueError, match="window conflicts"):
        source.require_projected_image_window(
            str(path), metadata.payload_with(expected[:1]), projection
        )
    with pytest.raises(ValueError, match="SHA256"):
        service._receipt_source_projection(
            replace(request, source_receipt=replace(resource, sha256="0" * 64)),
            (source_record,),
            context,
        )


def test_receipt_projection_refuses_unowned_image_source(tmp_path):
    path = tmp_path / "aggregate.labels.tif"
    state = receipt_state(path)
    data = json.dumps(to_jsonable(state), sort_keys=True).encode()
    resource_path = tmp_path / "canonical-viewer-state.json"
    resource_path.write_bytes(data)
    resource = AgentResourceRef(
        uri=resource_path.as_uri(),
        title="Synthetic native receipt",
        path=str(resource_path),
        size_bytes=len(data),
        sha256=hashlib.sha256(data).hexdigest(),
    )
    inspection = PlateInspectionService(
        path_policy=AgentPathPolicy.with_roots(
            readable_roots=(tmp_path,), writable_roots=()
        )
    )
    service = PlateStreamingService(inspection, object())
    context = SimpleNamespace(
        plate_path=tmp_path,
        filemanager=FileManager({"disk": DiskStorageBackend()}),
    )
    with pytest.raises(ValueError, match="inventory source reference"):
        service._receipt_source_projection(
            PlateFileStreamRequest(plate_path=str(tmp_path), source_receipt=resource),
            (PlateFileRecord(kind=PlateFileKind.IMAGE, key=str(path)),),
            context,
        )


def test_standalone_mcp_streaming_uses_declared_receipt_and_explicit_bridge(tmp_path):
    from openhcs.mcp.context import OpenHCSAgentContext
    from openhcs.mcp.server import build_server

    class RecordingService:
        def __init__(self):
            self.calls = []

        def stream_files(self, request, *, ui_bridge_connection):
            self.calls.append((request, ui_bridge_connection))
            return PlateFileStreamResult(
                schema_version=SCHEMA_VERSION,
                plate_path=request.plate_path,
                requested_microscope_type=request.microscope_type,
                viewer_config_key=request.viewer_config_key,
                connection=request.connection,
            )

    service = RecordingService()
    server = build_server(OpenHCSAgentContext(plate_streaming_service=service))
    tools = asyncio.run(server.list_tools())
    schema = next(
        tool.inputSchema
        for tool in tools
        if tool.name == "openhcs_stream_plate_files_to_viewer"
    )
    assert "connection" in schema["properties"]
    assert "source_receipt" in schema["properties"]
    resource_schema = schema["$defs"]["AgentResourceRef"]["properties"]
    assert set(resource_schema) == {member.name for member in fields(AgentResourceRef)}
    receipt = AgentResourceRef(
        uri=(tmp_path / "receipt.json").as_uri(),
        title="Fixture",
        path=str(tmp_path / "receipt.json"),
        sha256="0" * 64,
    )
    request = PlateFileStreamRequest.from_fields(
        plate_path=str(tmp_path), port=5631, source_receipt=receipt
    )
    arguments = {
        **request.as_tool_arguments(),
        "connection": {"descriptor_file_path": str(tmp_path / "exact-ui.json")},
    }
    asyncio.run(server.call_tool("openhcs_stream_plate_files_to_viewer", arguments))
    admitted_request, admitted_connection = service.calls[0]
    assert admitted_request.source_receipt == receipt
    assert admitted_request.connection.port == 5631
    assert admitted_connection.descriptor_file_path == str(tmp_path / "exact-ui.json")
