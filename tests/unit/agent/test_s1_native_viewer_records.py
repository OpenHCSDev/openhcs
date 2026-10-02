"""Pure synthetic native projection -> service -> public typed rendering."""

from dataclasses import dataclass
from types import SimpleNamespace

import numpy as np
import pytest
from pydantic import StrictInt
from polystore.streaming.identity import StreamProducerIdentity
from polystore.streaming_constants import StreamingDataType

from openhcs.agent.capabilities import (
    GetViewerWindowStateCapability, GetViewerWindowPayloadsCapability,
    SampleViewerWindowImageCapability, SummarizeViewerWindowRoisCapability,
)
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import (
    ViewerWindowDescriptor, ViewerWindowImageSampleRequest,
    ViewerWindowLayerState, ViewerWindowPayloadRequest,
    ViewerWindowRoiSummaryRequest, ViewerWindowStateResult,
    ViewerWindowPayloadRecord,
)
from openhcs.agent.services.viewer_window_service import ViewerWindowService
from openhcs.core.runtime_image_values import ImagePayloadMetadata
from openhcs.core.source_spatial_domain import SourceSpatialDomain
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity, McpDevToolBatchResponse, McpDevToolResult,
)
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer, ViewerImageSampleRenderOptions
from openhcs.runtime.napari_streaming_handlers import NapariStreamLayerAddress, NapariStreamLayerItem
from openhcs.runtime.napari_viewer_server import (
    NapariViewerStateProjection, NapariViewerPayloadProjection, _NapariShapePayloadBudget,
)
from openhcs.runtime.viewer_component_system import ViewerComponentValueDomainPayload
from openhcs.runtime.viewer_protocol import (
    ViewerArrayValueSummary, ViewerPayloadSummary, ViewerProjectionRecord,
    ViewerPayloadControlOptions, ViewerPayloadProjectionOptions,
)
from openhcs.serialization.json import to_jsonable


def item(data, *, kind=StreamingDataType.IMAGE):
    return NapariStreamLayerItem(
        data=data,
        producer=StreamProducerIdentity.pipeline_output(
            output_kind="main", output_key="main", projection_key="main",
            step_name="Synthetic", pipeline_position=0, step_scope_id="synthetic",
        ),
        address=NapariStreamLayerAddress(
            components={"channel": 2}, path="synthetic-only", stream_layer_data_type=kind,
        ),
        image_metadata=ImagePayloadMetadata(source_spatial_domain=SourceSpatialDomain(
            origin_yx=(0, 0), source_shape_yx=(4, 4),
        )),
        plane_component_domain=ViewerComponentValueDomainPayload(()),
    )


def native_record(payload, **controls):
    projection = NapariViewerPayloadProjection(
        server=None, viewer=None,
        request=ViewerPayloadProjectionOptions(controls=ViewerPayloadControlOptions(**controls)),
    )
    return projection.record_for_item(payload, "route", (), (), None, _NapariShapePayloadBudget(None))


def service_for(wire, payload):
    """Only the transport is synthetic; original bridge/service algorithms run."""
    response = {
        "status": "success", "type": "payloads_ack", "viewer": {"type": "napari", "title": "Synthetic"},
        "layer_count": 1, "layers": ({
            "route_key": "route", "title": "Synthetic", "mounted": True, "item_count": 1,
            "producer_identities": (payload.producer.to_payload(),),
            "axis_labels": ("y", "x"), "stack_axes": (), "pending_update": False,
            "payloads": (wire,),
        },),
    }
    return ViewerWindowService(gateway=SimpleNamespace(window_payloads=lambda request: response)), response


def rendered(capability, value, options=None):
    wire = to_jsonable(McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="source-only", module="openhcs.mcp"),
        results=(McpDevToolResult(capability.name, False, (value,)),),
    ))
    decoded = McpDevToolBatchResponse.for_rendering(wire)
    binding = McpDevOutputRenderer.for_output_contract(capability.output_contract)
    return decoded.payload_for(capability.to_spec()), binding.render_result(
        decoded, options or binding.renderer_type.render_options_type(),
    ), wire


def test_summary_sparse_wire_keeps_null_zero_false_empty_and_rejects_unknown():
    wire = {"components": {}, "min": None, "max": False, "nonzero_count": 0,
            "nonzero_example_coordinates": []}
    record = ViewerPayloadSummary.from_wire_mapping(wire)
    assert record.known_nonzero_count == 0
    assert to_jsonable(record) == wire
    assert to_jsonable(ViewerPayloadSummary()) == {}
    assert ViewerPayloadSummary().known_nonzero_count is None
    with pytest.raises(ValueError, match="undeclared"):
        ViewerPayloadSummary.from_wire_mapping({"unknown": 0})


@pytest.mark.parametrize("bad", (True, 1.5, "1"))
@pytest.mark.parametrize("field", ("nonzero_count", "spatial_origin_yx", "shape"))
def test_original_exact_integer_domain_and_count_controls(field, bad):
    value = bad if field == "nonzero_count" else (bad, 4)
    with pytest.raises((TypeError, ValueError)):
        ViewerPayloadSummary.from_wire_mapping({field: value})


def test_native_array_materializes_one_typed_authority_through_public_sample():
    payload = item(np.arange(16, dtype=np.uint16).reshape(4, 4))
    wire = native_record(payload, include_array_values=True, max_array_elements=4,
                         array_slices=((1, 3), (2, 4)))
    assert wire["array_values"] == ((6, 7), (10, 11))
    assert wire["array_value_summary"]["slice_ranges"] == ((1, 3), (2, 4))
    service, response = service_for(wire, payload)
    connection = ExecutionConnectionSpec(port=5992)
    result = service.window_payloads(ViewerWindowPayloadRequest(connection=connection))
    assert not result.errors
    record = result.layers[0].payloads[0]
    assert isinstance(record.summary, ViewerPayloadSummary)
    assert isinstance(record.array_value_summary, ViewerArrayValueSummary)
    assert record.array_value_summary.sample_included
    assert to_jsonable(record) == to_jsonable(wire)
    decoded, compact, _ = rendered(GetViewerWindowPayloadsCapability, result)
    assert decoded.layers[0].payloads[0].summary.nonzero_count == 15
    assert "nonzero=15" in compact and "components=channel=2" in compact
    sample = service.sample_image(ViewerWindowImageSampleRequest(
        connection=connection, route_key="route", y=1, x=2, height=2, width=2,
    ))
    assert not sample.errors
    assert sample.records[0].summary.nonzero_count == 15
    assert sample.records[0].array_value_summary.sample_included
    assert sample.sample_included_count == 1
    decoded, compact, raw = rendered(SampleViewerWindowImageCapability, sample)
    assert decoded.records[0].array_values == ([6, 7], [10, 11])
    assert "sample values: [[6, 7], [10, 11]]" in compact
    assert "source_spatial_shape_yx" in raw["results"][0]["payloads"][0]["records"][0]["summary"]
    assert response["layers"][0]["payloads"][0] is wire


def test_native_omission_budget_zero_and_explicit_false_remain_distinct():
    payload = item(np.ones((4, 4), dtype=np.uint8))
    wire = native_record(payload, include_array_values=True, max_array_elements=0)
    service, _ = service_for(wire, payload)
    result = service.sample_image(ViewerWindowImageSampleRequest(
        connection=ExecutionConnectionSpec(port=5992), route_key="route",
        y=0, x=0, height=4, width=4,
    ))
    sample = result.records[0].array_value_summary
    assert sample.protocol_supported and not sample.sample_included
    assert sample.max_array_elements == 0
    assert sample.shape_element_count == 16
    _, compact, _ = rendered(SampleViewerWindowImageCapability, result,
                            ViewerImageSampleRenderOptions(include_array_values_requested=False))
    assert "reason=array_values_not_requested" in compact
    assert "max_elements=0" in compact and "--max-array-elements 16" in compact
    assert sample.omitted_reason == "max_array_elements_exceeded"
    _, compact, _ = rendered(SampleViewerWindowImageCapability, result,
                            ViewerImageSampleRenderOptions(include_array_values_requested=True))
    assert "reason=max_array_elements_exceeded" in compact
    assert "rerun_max_elements=16" in compact
    assert to_jsonable(ViewerArrayValueSummary(requested=False, included=False)) == {
        "requested": False, "included": False,
    }


def test_original_roi_geometry_semantic_dedup_stats_and_bounds_flow_to_typed_presentation():
    metadata = {"label": 0, "area": 0.0, "perimeter": 4.0, "centroid": [0.0, 0.0],
                "bbox": [0, 0, 1, 1], "source_spatial_shape_yx": (4, 4)}
    shape = {"type": "polygon", "coordinates": [[-0.5, -0.5], [0.5, -0.5], [0.5, 0.5]],
             "metadata": metadata}
    payload = item([shape, shape], kind=StreamingDataType.SHAPES)
    wire = native_record(payload)
    assert wire["summary"]["shape_out_of_source_bounds_count"] == 0
    service, _ = service_for(wire, payload)
    result = service.summarize_rois(ViewerWindowRoiSummaryRequest(
        connection=ExecutionConnectionSpec(port=5992), route_key="route",
    ))
    assert not result.errors
    summary = result.payloads[0]
    assert summary.roi_count == 1 and summary.roi_member_count == 2
    assert summary.roi_duplicate_member_count == 1 and summary.roi_count_exact
    assert summary.area.min == 0.0
    assert summary.bounds_yx.min_yx == (-0.5, -0.5)
    assert summary.coordinate_count == 6 and summary.out_of_source_bounds_count == 0
    decoded, compact, _ = rendered(SummarizeViewerWindowRoisCapability, result)
    assert decoded.payloads[0].bounds_yx.coordinate_count == 6
    assert "duplicate_members=1" in compact and "out_of_bounds=0" in compact
    assert "area=min=0.0" in compact and "example label=0 area=0.0" in compact


def test_independent_native_capability_executes_cooperative_validation_and_wire_hooks():
    calls = []

    @dataclass(frozen=True, kw_only=True)
    class AuditCapability(ViewerProjectionRecord):
        audit_label: str = "declared"

        def validate_record(self):
            calls.append("validate-audit")
            super().validate_record()
            assert self.source_domain.source_shape_yx == (4, 4)

        def wire_overrides(self):
            calls.append("wire-audit")
            return super().wire_overrides() | {"audit_label": self.audit_label.upper()}

    @dataclass(frozen=True, kw_only=True)
    class AuditedSummary(AuditCapability, ViewerPayloadSummary):
        pass

    class AuditedProjection(NapariViewerStateProjection):
        payload_summary_type = AuditedSummary

    @dataclass(frozen=True, kw_only=True)
    class AuditedLayer(ViewerWindowLayerState):
        payload_summaries: tuple[AuditedSummary, ...] = ()

    @dataclass(frozen=True, kw_only=True)
    class AuditedState(ViewerWindowStateResult):
        layers: tuple[AuditedLayer, ...] = ()

    class AuditedStateCapability(GetViewerWindowStateCapability):
        name = "openhcs_s1_native_audited_state"
        cli_command = "s1-native-audited-state"
        output_contract = AuditedState

    payload = item([{"type": "polygon", "coordinates": [[0, 0], [1, 1]],
                     "metadata": {"source_spatial_shape_yx": (4, 4)}}], kind=StreamingDataType.SHAPES)
    record = AuditedProjection.payload_summary(payload, payload.address.components, payload.data)
    assert calls == ["validate-audit"]
    wire = record.to_wire_mapping()
    assert calls == ["validate-audit", "wire-audit"]
    assert wire["audit_label"] == "DECLARED"
    assert wire["shape_coordinate_bounds_yx"]["coordinate_count"] == 2
    result = AuditedState(
        schema_version=SCHEMA_VERSION, connection=ExecutionConnectionSpec(port=5992), observed=True,
        viewer=ViewerWindowDescriptor(ViewerType.NAPARI, "Synthetic"),
        layers=(AuditedLayer(route_key="route", title="Synthetic", mounted=True, item_count=1,
                             payload_summaries=(record,), payload_summary_count=1),),
    )
    decoded, compact, raw = rendered(AuditedStateCapability, result)
    assert type(decoded.layers[0].payload_summaries[0]) is AuditedSummary
    assert decoded.layers[0].payload_summaries[0].audit_label == "DECLARED"
    assert '"audit_label": "DECLARED"' in compact
    assert '"shape_coordinate_bounds_yx"' in compact
    assert calls.count("validate-audit") >= 2 and calls.count("wire-audit") >= 2
    assert raw["results"][0]["payloads"][0]["layers"][0]["payload_summaries"][0]["audit_label"] == "DECLARED"
    with pytest.raises(ValueError, match="must not be empty"):
        AuditedSummary(spatial_origin_yx=(0, 0), source_spatial_shape_yx=(4, 4),
                       aggregate_component_values={"channel": ()})


def test_independent_roi_capability_contributes_through_original_service_factory_and_mro():
    calls = []

    class RoiFamilyCapability:
        @property
        def roi_payload_records(self):
            calls.append("roi-family")
            return (*super().roi_payload_records, self)

    @dataclass(frozen=True, kw_only=True)
    class DeclaredRoiRecord(RoiFamilyCapability, ViewerWindowPayloadRecord):
        pass

    class DeclaredRoiService(ViewerWindowService):
        payload_record_type = DeclaredRoiRecord

    payload = item([{"type": "polygon", "coordinates": [[0, 0], [1, 1]],
                     "metadata": {"label": 0, "source_spatial_shape_yx": (4, 4)}}],
                   kind=StreamingDataType.ROIS)
    wire = native_record(payload)
    service, _ = service_for(wire, payload)
    extended = DeclaredRoiService(gateway=service._gateway)
    request = ViewerWindowRoiSummaryRequest(connection=ExecutionConnectionSpec(port=5992), route_key="route")
    assert service.summarize_rois(request).roi_payload_count == 0
    result = extended.summarize_rois(request)
    assert calls == ["roi-family"]
    assert result.payload_type_counts == {"rois": 1}
    assert result.roi_payload_count == 1 and result.total_roi_count == 1
    decoded, compact, _ = rendered(SummarizeViewerWindowRoisCapability, result)
    assert decoded.payloads[0].example_rois[0].label == 0
    assert "roi_count=1" in compact and "example label=0" in compact
