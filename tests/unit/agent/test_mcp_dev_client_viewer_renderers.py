"""Compact viewer/runtime renderers over typed DTO fixtures; never launch a viewer."""

from __future__ import annotations

import pytest
from python_introspect import dataclass_from_mapping

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError, AgentWarning
from openhcs.agent.dto.execution import (
    ExecutionConnectionSpec,
    RuntimeExecutionStatus,
    RuntimeServerInfo,
    RuntimeServerScanResult,
)
from openhcs.agent.dto.ui_bridge import UiWindowSnapshotResult
from openhcs.agent.dto.viewer import (
    ViewerWindowDescriptor,
    ViewerWindowImageSampleResult,
    ViewerWindowLayerIsolationResult,
    ViewerWindowNavigationResult,
    ViewerWindowPayloadResult,
    ViewerWindowProbeResult,
    ViewerWindowRoiSummaryResult,
    ViewerWindowSnapshotResult,
    ViewerWindowStateResult,
    ViewerWindowValidationSummaryResult,
)
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.mcp.dev_client import McpDevCommandSpec, _build_parser
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer
from openhcs.mcp.dev_client_renderers.viewer import (
    RuntimeExecutionStatusRenderer,
    ViewerResultRenderer,
)

PORT = {"connection": {"port": 5555}}


def batch(capability, *payloads) -> McpDevToolBatchResponse:
    return McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp.server"),
        results=(McpDevToolResult(capability.name, False, payloads),),
    )


def typed(contract, **values):
    return dataclass_from_mapping(contract, {"schema_version": SCHEMA_VERSION, **values})


def render(capability, payload, *command_args: str) -> str:
    """Render through the capability's command, as the CLI does."""
    command = capability.cli_command
    args = _build_parser().parse_args((command, *command_args))
    return McpDevCommandSpec.for_name(command).render_result(batch(capability, payload), args)


def test_every_viewer_output_contract_has_its_own_typed_renderer():
    contracts = (
        RuntimeServerScanResult, RuntimeServerInfo, RuntimeExecutionStatus,
        ViewerWindowSnapshotResult, ViewerWindowStateResult, ViewerWindowPayloadResult,
        ViewerWindowImageSampleResult, ViewerWindowRoiSummaryResult,
        ViewerWindowNavigationResult, ViewerWindowLayerIsolationResult,
        ViewerWindowProbeResult, ViewerWindowValidationSummaryResult,
        UiWindowSnapshotResult,
    )
    renderers = [McpDevOutputRenderer.for_output_contract(contract) for contract in contracts]
    assert all(renderer is not None for renderer in renderers)
    assert all(renderer.output_contract is contract
               for renderer, contract in zip(renderers, contracts))
    assert len(set(renderers)) == len(contracts)


def test_missing_payload_renders_unavailable_summary_and_diagnostic_once():
    empty = McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp.server"),
        results=(McpDevToolResult(
            agent_capabilities.navigate_viewer_window.name, False, ()),),
    )
    rendered = McpDevOutputRenderer.for_output_contract(
        ViewerWindowNavigationResult).render(empty)
    assert rendered.startswith("Viewer navigation: failed\nErrors:\n")
    assert "mcp_payload_missing" in rendered


def test_validation_tool_boundary_error_is_the_whole_compact_output():
    capability = agent_capabilities.validate_viewer_window_state
    raw = McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp.server"),
        results=(McpDevToolResult(capability.name, False, ({
            "schema_version": SCHEMA_VERSION, "ok": False, "tool": capability.name,
            "errors": [{"code": "mcp_tool_failed",
                        "message": "Viewer MCP timeout must not exceed 2000ms."}],
        },)),),
    )
    args = _build_parser().parse_args(("validate-viewer", "5555"))
    assert McpDevCommandSpec.for_name("validate-viewer").render_result(raw, args) == (
        "Viewer validation: failed\nErrors:\n"
        "- mcp_tool_failed: Viewer MCP timeout must not exceed 2000ms."
    )


def test_validation_reports_policy_layers_and_axis_component_hint():
    payload = typed(
        ViewerWindowValidationSummaryResult,
        valid=False, observed=True, layer_count=1, mounted_layer_count=1,
        payload_count=1, nonzero_payload_count=1,
        validation_policy={"expected_layer_count": 2,
                           "required_axis_labels": ["site", "well", "channel"]},
        connection={"host": "localhost", "port": 5555, "transport_mode": "ipc"},
        layer_summaries=[{
            "route_key": "image-layer", "title": "Image", "valid": False,
            "mounted": True, "item_count": 1, "axis_labels": ["channel", "y", "x"],
            "component_labels": ["channel", "site", "well"],
            "missing_required_axis_labels": ["site", "well"],
            "axis_labels_present_as_components": ["site", "well"],
        }],
        warnings=[{
            "code": "viewer_required_axis_labels_missing",
            "message": "Viewer layer 'Image' is missing required axis labels: site, well.",
            "hint": "These labels are present as component metadata rather than mounted axes: site, well.",
        }],
    )
    rendered = render(agent_capabilities.validate_viewer_window_state, payload, "5555")
    assert "Viewer validation: valid=False observed=True layers=1 mounted=1" in rendered
    assert "Policy: expected_layers=2 required_axes=site,well,channel required_components=<none>" in rendered
    assert "Connection: localhost:5555 transport=ipc" in rendered
    assert "- image-layer: valid=False mounted=True items=1 axes=channel,y,x" in rendered
    assert "missing_axes=site,well components=channel,site,well missing_components=<none>" in rendered
    assert "axis_as_components=site,well" in rendered
    assert ('Warnings:\n- viewer_required_axis_labels_missing: '
            "Viewer layer 'Image' is missing required axis labels: site, well. "
            'hint="These labels are present as component metadata rather than '
            'mounted axes: site, well."') in rendered


def test_state_merges_component_values_and_bounds_payload_summaries():
    payload = typed(
        ViewerWindowStateResult,
        **PORT, observed=True,
        viewer={"viewer_type": "napari", "title": "OpenHCS Napari Visualization"},
        layer_count=1, viewer_ndim=3, axis_labels=["channel", "y", "x"],
        current_step=[0, 47, 47], active_dimension_label_route="image-layer",
        component_group_count=1, component_item_count=2,
        layers=[{
            "route_key": "image-layer", "title": "1. Agent invert", "mounted": True,
            "visible": True, "selected": True, "item_count": 2,
            "data_types": ["image"], "axis_labels": ["channel", "y", "x"],
            "component_values": [
                {"well": "A01", "channel": 1, "site": 1},
                {"well": "A01", "channel": 2, "site": 1},
            ],
            "axis_component_values": {"channel": [1, 2]},
        }],
    )
    rendered = render(agent_capabilities.get_viewer_window_state, payload, "5555")
    assert 'Viewer state: observed=True type=napari title="OpenHCS Napari Visualization"' in rendered
    assert "Window: layers=1 ndim=3 axes=channel,y,x current_step=[0, 47, 47] active_route=image-layer" in rendered
    assert '- image-layer: title="1. Agent invert" visible=True selected=True items=2 types=image' in rendered
    assert "  components: channel=1,2, site=1, well=A01" in rendered
    assert "  axis values: channel=1,2" in rendered


def test_payloads_mark_streamed_paths_and_shape_payload_counts(tmp_path):
    streamed_path = tmp_path / "streamed_A01_w1.tif"
    payload = typed(
        ViewerWindowPayloadResult,
        **PORT, observed=True, layer_count=2,
        layers=[
            {"route_key": "image-layer", "title": "Images", "mounted": True,
             "item_count": 2, "axis_labels": ["channel", "y", "x"],
             "stack_axes": ["channel"],
             "payloads": [{
                 "route_key": "image-layer:0", "data_type": "image", "axis_indices": [0],
                 "components": {"well": "A01", "channel": 1},
                 "path": str(streamed_path),
                 "summary": {"shape": [96, 96], "dtype": "uint16", "nonzero_count": 9216},
                 "array_value_summary": {"included": False, "shape": [96, 96],
                                         "omitted_reason": "max_array_elements_exceeded"},
             }]},
            {"route_key": "roi-layer", "title": "ROIs", "mounted": True,
             "item_count": 1, "axis_labels": ["y", "x"],
             "payloads": [{
                 "route_key": "roi-layer:0", "data_type": "shapes", "components": {"channel": 2},
                 "path": "relative/A01_w2.roi.zip",
                 "summary": {"shape_payload_count": 7, "nonzero_count": 7},
                 "shape_payloads": [{"metadata": {"label": 1}}, {"metadata": {"label": 2}}],
             }]},
        ],
    )
    rendered = render(agent_capabilities.get_viewer_window_payloads, payload, "5555")
    assert "Viewer payloads: observed=True layers=2" in rendered
    assert '- image-layer: title="Images" mounted=True items=2 axes=channel,y,x stack=channel payloads=1' in rendered
    assert "payload type=image axis=0 aggregate_axis=<none> components=channel=1, well=A01" in rendered
    assert "shape=[96, 96] dtype=uint16 nonzero=9216" in rendered
    assert "array=included=False sample_shape=[96, 96] reason=max_array_elements_exceeded" in rendered
    assert f"path={streamed_path} (streamed/non-materialized)" in rendered
    assert "payload type=shapes axis=<none>" in rendered
    assert "shape_members=7 returned_shapes=2 semantic_rois=use-viewer-rois" in rendered
    assert "path=relative/A01_w2.roi.zip" in rendered
    assert "relative/A01_w2.roi.zip (streamed" not in rendered


ROI_PAYLOAD = {
    "layer_route_key": "roi-layer", "layer_title": "ROIs",
    "payload_route_key": "roi-layer:0", "path": "/tmp/A01.roi.zip",
    "components": {"well": "A01", "channel": 1}, "axis_indices": [0, 1],
    "roi_count": 3, "returned_roi_count": 3, "roi_count_exact": False,
    "roi_member_count": 7, "returned_roi_member_count": 3,
    "roi_duplicate_member_count": 0, "roi_payloads_truncated": True,
    "area": {"min": 10.0, "median": 42.0, "mean": 40.0, "max": 80.0},
    "perimeter": None, "bounds_yx": None, "coordinate_count": 128,
    "spatial_origin_yx": [0, 0], "source_spatial_shape_yx": [96, 96],
    "out_of_source_bounds_count": 0,
    "example_rois": [{"label": "cell-1", "area": 42, "centroid_yx": [5, 6]}],
}


def test_rois_render_payload_statistics_and_examples():
    payload = typed(
        ViewerWindowRoiSummaryResult,
        observed=True, route_key="roi-layer", axis_indices=[0, 1], layer_count=2,
        payload_record_count=1, payload_type_counts={"shapes": 1}, roi_payload_count=1,
        total_roi_count=3, returned_roi_count=3, roi_count_exact=False,
        total_roi_member_count=7, returned_roi_member_count=3,
        roi_payloads_truncated=True, payloads=[ROI_PAYLOAD],
    )
    rendered = render(agent_capabilities.summarize_viewer_window_rois, payload, "5555", "roi-layer")
    assert "Viewer ROIs: observed=True route=roi-layer axis=0,1" in rendered
    assert "ROIs: total=3 returned=3 exact=False members=7/3 truncated=True" in rendered
    assert "Payload types: shapes=1" in rendered
    assert ('- title="ROIs" layer_route=roi-layer payload_route=roi-layer:0 axis=0,1 '
            "components=channel=1, well=A01 roi_count=3 returned=3 exact=False "
            "members=7/3 duplicate_members=0") in rendered
    assert "area=min=10.0,median=42.0,mean=40.0,max=80.0 perimeter=<none>" in rendered
    assert "coords=128 source_origin=[0, 0] source_shape=[96, 96] out_of_bounds=0" in rendered
    assert "example label=cell-1 area=42 centroid=[5, 6]" in rendered


@pytest.mark.parametrize("route_key", (None, "image-layer"))
def test_rois_explain_missing_roi_payloads_for_the_requested_scope(route_key):
    payload = typed(
        ViewerWindowRoiSummaryResult,
        observed=True, route_key=route_key, layer_count=7,
        payload_record_count=32, payload_type_counts={"image": 32},
    )
    rendered = render(agent_capabilities.summarize_viewer_window_rois, payload, "5555")
    assert f"Viewer ROIs: observed=True route={route_key or '<none>'} axis=<none> layers=7 records=32 payloads=0" in rendered
    assert "Payload types: image=32" in rendered
    suffix = " route." if route_key else "."
    assert f"Interpretation: no ROI/shapes payloads were found for the requested viewer{suffix}" in rendered
    rerun = "- If `viewer-state` shows a shapes layer, rerun `viewer-rois <port> <route_key>` for that route."
    assert (rerun in rendered) is (route_key is None)
    assert "- If payload types are image-only" in rendered


def test_rois_with_errors_do_not_explain_absence():
    payload = typed(
        ViewerWindowRoiSummaryResult, observed=False,
        errors=[{"code": "viewer_window_rois_failed", "message": "timed out"}],
    )
    rendered = render(agent_capabilities.summarize_viewer_window_rois, payload, "5555")
    assert "Interpretation" not in rendered
    assert rendered.endswith("Errors:\n- viewer_window_rois_failed: timed out")


def image_sample(max_array_elements: int, *, included: bool = False, values=()):
    return typed(
        ViewerWindowImageSampleResult,
        observed=True, route_key="image-layer", axis_indices={"channel": 1},
        array_slices=[[0, 8], [0, 8]], record_count=1, returned_record_count=1,
        raw_image_record_count=1, total_payload_record_count=2,
        sample_protocol_supported=True,
        sample_included_count=int(included), sample_omitted_count=int(not included),
        records=[{
            "layer_title": "image-layer", "data_type": "image", "components": {},
            "payload_route_key": "image-layer:0", "layer_route_key": "image-layer",
            "axis_indices": [1], "path": "virtual/image.tif",
            "summary": {"shape": [96, 96], "dtype": "uint16", "min": 23,
                        "max": 10755, "nonzero_count": 9216},
            "array_value_summary": {
                "included": included, "shape": [8, 8],
                **({} if included else {"omitted_reason": "max_array_elements_exceeded"}),
                "max_array_elements": max_array_elements,
            },
            "array_values": list(values),
        }],
    )


def test_image_sample_includes_small_sample_values():
    sample = image_sample(64, included=True, values=([1, 2], [3, 4]))
    rendered = render(agent_capabilities.sample_viewer_window_image, sample,
                      "5555", "image-layer", "--include-array-values")
    assert "Viewer image sample: observed=True route=image-layer axis=channel=1 slices=[[0, 8], [0, 8]]" in rendered
    assert "Records: matched=1 returned=1 truncated=0 image=1 total_payloads=2 sample_supported=True" in rendered
    assert "- image-layer:0: layer=image-layer axis=1 path=virtual/image.tif" in rendered
    assert "shape=[96, 96] dtype=uint16 min=23 max=10755 nonzero=9216" in rendered
    assert "included=True sample_shape=[8, 8]" in rendered
    assert "sample values: [[1, 2], [3, 4]]" in rendered


@pytest.mark.parametrize(
    "command_args,budget,expected",
    (
        ((), 0, "reason=array_values_not_requested max_elements=0 "
                "rerun_with=--include-array-values --max-array-elements 64"),
        (("--include-array-values", "--max-array-elements", "40"), 40,
         "reason=max_array_elements_exceeded max_elements=40 rerun_max_elements=64"),
    ),
)
def test_image_sample_omission_names_the_rerun_that_includes_values(command_args, budget, expected):
    rendered = render(agent_capabilities.sample_viewer_window_image, image_sample(budget),
                      "5555", "image-layer", *command_args)
    assert "axis={'channel': 1}" not in rendered
    assert "included=False sample_shape=[8, 8]" in rendered
    assert expected in rendered


def test_navigation_and_isolation_report_position_layers_and_grouped_errors():
    navigation = typed(
        ViewerWindowNavigationResult,
        **PORT, observed=True, route_key="roi-layer", visible=True, selected=True,
        axis_labels=["channel", "y", "x"], current_step=[1, 0, 0],
        active_dimension_label_route="roi-layer",
        available_layers=[
            {"route_key": "image-layer", "title": "Image", "visible": True, "selected": False},
            {"route_key": "roi-layer", "title": "ROIs", "visible": True, "selected": True},
        ],
        warnings=[{"code": "viewer_axis_missing", "message": "z_index is not mounted."}],
    )
    rendered = render(agent_capabilities.navigate_viewer_window, navigation, "5555", "roi-layer")
    assert "Viewer navigation: observed=True route=roi-layer visible=True selected=True" in rendered
    assert "Position: axes=channel,y,x current_step=[1, 0, 0] active_route=roi-layer" in rendered
    assert ('Available layers:\n- image-layer: visible=True selected=False title="Image"\n'
            '- roi-layer: visible=True selected=True title="ROIs"') in rendered
    assert "Warnings:\n- viewer_axis_missing: z_index is not mounted." in rendered

    isolation = typed(
        ViewerWindowLayerIsolationResult,
        **PORT, observed=True, applied=True, selected_route_key="roi-layer",
        changed_route_count=2, layer_count=2, axis_labels=["channel", "y", "x"],
        current_step=[1, 0, 0], visible_route_keys=["roi-layer"],
        hidden_route_keys=["image-layer"], missing_route_keys=["gone"],
        visible_layers=[{"route_key": "roi-layer", "title": "ROIs",
                         "visible": True, "selected": True}],
    )
    rendered = render(agent_capabilities.isolate_viewer_window_layers, isolation, "5555", "roi-layer")
    assert "Viewer isolation: observed=True applied=True selected=roi-layer changed=2 layers=2" in rendered
    assert "Visible: roi-layer\nHidden: image-layer\nMissing routes: gone" in rendered
    assert 'Visible layers:\n- roi-layer: visible=True selected=True title="ROIs"' in rendered

    failed = typed(
        ViewerWindowLayerIsolationResult, **PORT, observed=False,
        selected_route_key="roi-layer",
        errors=[
            {"code": "viewer_window_navigation_failed", "message": "Viewer control request timed out."},
            {"code": "viewer_window_navigation_failed", "message": "Viewer control request timed out."},
            {"code": "viewer_window_state_failed", "message": "Viewer control request timed out."},
        ],
    )
    rendered = render(agent_capabilities.isolate_viewer_window_layers, failed, "5555", "roi-layer")
    assert ("- viewer_window_navigation_failed, viewer_window_state_failed: "
            "Viewer control request timed out.") in rendered
    assert rendered.count("Viewer control request timed out.") == 1


def test_snapshots_render_image_and_resource_facts():
    resource = {"path": "/tmp/snapshots/viewer.png", "uri": "file:///tmp/snapshots/viewer.png",
                "title": "viewer.png", "mime_type": "image/png", "size_bytes": 12345,
                "sha256": "abc123"}
    viewer = typed(
        ViewerWindowSnapshotResult, **PORT, output_dir_path="/tmp/snapshots",
        captured=True, capture_scope="widget",
        viewer={"viewer_type": "napari", "title": "Viewer"},
        width=640, height=480, resource=resource,
    )
    rendered = render(agent_capabilities.viewer_snapshot_window, viewer, "5555")
    assert 'Viewer snapshot: captured=True type=napari title="Viewer" scope=widget' in rendered
    assert "Image: size=640x480 bytes=12345 mime=image/png" in rendered
    assert ("Resource: path=/tmp/snapshots/viewer.png "
            "uri=file:///tmp/snapshots/viewer.png sha256=abc123") in rendered

    window = typed(
        UiWindowSnapshotResult, output_dir_path="/tmp/snapshots",
        captured=True, window_id="global_config", capture_scope="window",
        width=550, height=600, resource=resource,
        summary={
            "schema_version": SCHEMA_VERSION, "identity": {"window_id": "global_config"},
            "title": "Configuration - GlobalPipelineConfig", "window_kind": "scope",
            "visible": True, "focusable": True, "signature_diff": True,
            "signature_diff_field_count": 3, "semantic_markers": ["_"],
            "object_state_scope_id": "global_config",
            "managed_action_ids": ["save_and_close", "save_without_close"],
        },
    )
    capability = agent_capabilities.ui_snapshot_window
    rendered = render(capability, window, "global_config")
    assert ("Window snapshot: captured=True window=global_config "
            'title="Configuration - GlobalPipelineConfig" kind=scope scope=window') in rendered
    assert ("Status: visible=True dirty=False dirty_fields=0 default_diff=True "
            "default_diff_fields=3 markers=_") in rendered
    assert "Image: size=550x600 bytes=12345 mime=image/png" in rendered
    assert "ObjectState: scope=global_config" in rendered
    assert "Actions: save_and_close,save_without_close" in rendered
    call_args = _build_parser().parse_args(
        ("call", capability.name, "--arguments", '{"window_id":"global_config"}'))
    call_rendered = McpDevCommandSpec.for_name("call").render_result(batch(capability, window), call_args)
    assert call_rendered == rendered
    assert '"payloads"' not in call_rendered


def test_runtime_scan_info_and_status_render_server_facts():
    napari = dict(schema_version=SCHEMA_VERSION, connection={"port": 5555},
                  server="NapariViewer", reachable=True, ready=True, control_port=6555,
                  log_file_path="/tmp/napari.log")
    execution = dict(schema_version=SCHEMA_VERSION, connection={"port": 7777},
                     server="ZMQExecutionServer", reachable=True, ready=True,
                     control_port=8777, active_executions=1, uptime=12.34,
                     log_file_path="/tmp/exec.log")
    scan = typed(RuntimeServerScanResult, ports=[5555, 7777], timeout_ms=300,
                 servers=[napari, execution])
    rendered = render(agent_capabilities.scan_runtime_servers, scan, "5555", "7777")
    assert "Runtime scan: ports=5555,7777 timeout_ms=300 servers=2" in rendered
    assert "port=5555 server=NapariViewer reachable=True ready=True control=6555" in rendered
    assert ("port=7777 server=ZMQExecutionServer reachable=True ready=True control=8777 "
            "active=1 running=0 queued=0 workers=0 uptime=12.3s log=/tmp/exec.log") in rendered

    unreachable = RuntimeServerInfo(
        schema_version=SCHEMA_VERSION, connection=ExecutionConnectionSpec(port=7777),
        reachable=False, errors=(AgentError(code="runtime_unreachable", message="no pong"),),
    )
    rendered = McpDevOutputRenderer.for_output_contract(RuntimeServerInfo).render(
        batch(agent_capabilities.get_runtime_server_info, unreachable))
    assert rendered.startswith("Runtime server:\n- port=7777 server=<none> reachable=False")
    assert rendered.endswith("Errors:\n- runtime_unreachable: no pong")

    status = RuntimeExecutionStatus(
        schema_version=SCHEMA_VERSION, connection=ExecutionConnectionSpec(port=7777),
        execution_id="run-1", status="ok",
        response={"status": "ok", "active_executions": 1, "uptime": 12.34,
                  "executions": ["run-1", "run-2"], "queued_executions": [],
                  "running_executions": [{"execution_id": "run-1", "subject_id": "p",
                                          "start_time": 1.0, "elapsed": 2.0}]},
    )
    rendered = RuntimeExecutionStatusRenderer.render(
        batch(agent_capabilities.get_runtime_server_execution_status, status))
    assert "Runtime execution status: status=ok execution_id=run-1 port=7777" in rendered
    assert "Executions: known=2 active=1 running=1 queued=0 uptime=12.3s" in rendered


def test_probe_presents_false_zero_and_empty_facts():
    probe = ViewerWindowProbeResult(
        schema_version=SCHEMA_VERSION, connection=ExecutionConnectionSpec(port=5555),
        reachable=True, observed=True, layer_count=2, component_group_count=2,
        component_item_count=4,
        viewer=ViewerWindowDescriptor(ViewerType.NAPARI, "OpenHCS Napari Visualization"),
        warnings=(AgentWarning(code="notice", message="shown"),),
    )
    rendered = render(agent_capabilities.probe_viewer_window, probe, "5555")
    assert ('Viewer probe: reachable=True observed=True type=napari '
            'title="OpenHCS Napari Visualization"') in rendered
    assert "Window: port=5555 layers=2 component_groups=2 component_items=4" in rendered
    assert rendered.endswith("Warnings:\n- notice: shown")


def test_viewer_renderers_read_no_record_by_key():
    import ast
    import inspect

    import openhcs.mcp.dev_client_renderers.viewer as module

    tree = ast.parse(inspect.getsource(module))
    calls = [node for node in ast.walk(tree) if isinstance(node, ast.Call)
             and isinstance(node.func, ast.Attribute) and node.func.attr == "get"]
    assert calls == []
    assert issubclass(module.ViewerProbeRenderer, ViewerResultRenderer)
