"""Viewer, runtime-server, and snapshot renderers for the MCP dev client."""

from __future__ import annotations

import json
from collections.abc import Mapping
from pathlib import Path

from python_introspect import to_jsonable
from zmqruntime.messages import ExecutionStatusSnapshot

from openhcs.agent.dto.execution import (
    RuntimeDebugInspectionResult,
    RuntimeExecutionStatus,
    RuntimeServerInfo,
    RuntimeServerScanResult,
)
from openhcs.agent.dto.ui_bridge import UiWindowSnapshotResult
from openhcs.agent.dto.viewer import (
    ViewerWindowImageSampleResult,
    ViewerWindowLayerIsolationResult,
    ViewerWindowLayerVisibilityRecord,
    ViewerWindowNavigationResult,
    ViewerWindowPayloadResult,
    ViewerWindowProbeResult,
    ViewerWindowRoiSummaryResult,
    ViewerWindowSnapshotResult,
    ViewerWindowStateResult,
    ViewerWindowValidationSummaryResult,
)
from openhcs.core.debug_view_models import DebugViewSection
from openhcs.mcp.dev_client_rendering import (
    CatalogRenderOptions,
    McpDevOutputRenderer,
    McpDevOutputRenderOptions,
    ViewerImageSampleRenderOptions,
)


class ViewerResultRenderer(McpDevOutputRenderer):
    """Presentation vocabulary shared by viewer result renderers."""

    @classmethod
    def viewer_text(cls, viewer) -> str:
        if viewer is None:
            return "type=<none> title=<none>"
        return f"type={cls.text(viewer.viewer_type)} title={cls.quoted(viewer.title)}"

    @classmethod
    def mapping_text(cls, value: Mapping | None) -> str:
        """``key=value`` pairs sorted by key; sequence values joined by commas."""
        if not value:
            return "<none>"
        parts: list[str] = []
        for key, item in sorted(value.items(), key=lambda entry: str(entry[0])):
            item_text = (
                ",".join(cls.text(part) for part in item)
                if isinstance(item, list | tuple)
                else cls.text(item)
            )
            parts.append(f"{key}={item_text}")
        return ", ".join(parts)

    @classmethod
    def axis_text(cls, value) -> str:
        """Axis selectors are either positional indices or named indices."""
        if isinstance(value, Mapping):
            return cls.mapping_text(value)
        return cls.sequence_text(value)

    @classmethod
    def path_text(cls, value: str | None) -> str:
        """Do not imply that a streamed (virtual) payload path exists on disk."""
        text = cls.text(value)
        if not value:
            return text
        path = Path(value)
        if not path.is_absolute() or path.exists():
            return text
        return f"{text} (streamed/non-materialized)"

    @classmethod
    def position_line(cls, payload) -> str:
        return (
            "Position: "
            f"axes={cls.sequence_text(payload.axis_labels)} "
            f"current_step={cls.json_text(payload.current_step)} "
            f"active_route={cls.text(payload.active_dimension_label_route)}"
        )

    @classmethod
    def visibility_lines(
        cls, label: str, layers: tuple[ViewerWindowLayerVisibilityRecord, ...]
    ) -> list[str]:
        if not layers:
            return []
        return [
            f"{label}:",
            *(
                f"- {layer.route_key}: visible={layer.visible} "
                f"selected={layer.selected} title={cls.quoted(layer.title)}"
                for layer in layers
            ),
        ]


class ViewerValidationRenderer(ViewerResultRenderer):
    """Compact renderer for viewer validation summaries."""

    output_contract = ViewerWindowValidationSummaryResult
    unavailable_summary = "Viewer validation: failed"

    @classmethod
    def render_payload(
        cls,
        payload: ViewerWindowValidationSummaryResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        policy = payload.validation_policy
        connection = payload.connection
        lines = [
            (
                "Viewer validation: "
                f"valid={payload.valid} observed={payload.observed} "
                f"layers={payload.layer_count} mounted={payload.mounted_layer_count} "
                f"pending={payload.pending_update_count}"
            ),
            (
                "Payloads: "
                f"total={payload.payload_count} nonzero={payload.nonzero_payload_count} "
                f"zero={payload.zero_payload_count} "
                f"missing={payload.missing_payload_coordinate_count} "
                f"duplicates={payload.duplicate_payload_coordinate_count}"
            ),
            (
                "Policy: "
                f"expected_layers={cls.text(policy.expected_layer_count)} "
                f"required_axes={cls.sequence_text(policy.required_axis_labels)} "
                "required_components="
                f"{cls.sequence_text(policy.required_component_labels)} "
                f"require_nonzero={policy.require_nonzero_payloads}"
            ),
            (
                "Connection: "
                f"{connection.host}:{connection.port} "
                f"transport={cls.text(connection.transport_mode)}"
            ),
        ]
        if payload.layer_summaries:
            lines.append("Layers:")
            lines.extend(
                "- "
                f"{layer.route_key}: valid={layer.valid} mounted={layer.mounted} "
                f"items={layer.item_count} axes={cls.sequence_text(layer.axis_labels)} "
                f"stack={cls.sequence_text(layer.stack_axes)} "
                f"payloads={layer.payload_count} nonzero={layer.nonzero_payload_count} "
                f"gaps={layer.coordinate_gap_count} "
                f"missing_axes={cls.sequence_text(layer.missing_required_axis_labels)} "
                f"components={cls.sequence_text(layer.component_labels)} "
                "missing_components="
                f"{cls.sequence_text(layer.missing_required_component_labels)} "
                "axis_as_components="
                f"{cls.sequence_text(layer.axis_labels_present_as_components)} "
                f"title={cls.quoted(layer.title)}"
                for layer in payload.layer_summaries
            )
        return "\n".join(lines)


class ViewerStateRenderer(ViewerResultRenderer):
    """Compact renderer for viewer state and layer component metadata."""

    output_contract = ViewerWindowStateResult
    unavailable_summary = "Viewer state: failed"

    @classmethod
    def render_payload(
        cls, payload: ViewerWindowStateResult, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"Viewer state: observed={payload.observed} {cls.viewer_text(payload.viewer)}",
            (
                "Window: "
                f"layers={payload.layer_count} ndim={payload.viewer_ndim} "
                f"axes={cls.sequence_text(payload.axis_labels)} "
                f"current_step={cls.json_text(payload.current_step)} "
                f"active_route={cls.text(payload.active_dimension_label_route)}"
            ),
            (
                "Components: "
                f"groups={payload.component_group_count} items={payload.component_item_count}"
            ),
        ]
        lines.extend(cls.optional_lines(payload.native_viewport, cls._viewport_lines))
        lines.extend(cls.optional_lines(payload.native_dimensions, cls._dimension_lines))
        if payload.layers:
            lines.append("Layers:")
            lines.extend(cls._layer_lines(payload.layers))
        return "\n".join(lines)

    @classmethod
    def _viewport_lines(cls, viewport) -> tuple[str, ...]:
        return (
            "Native viewport: "
            f"center={cls.json_text(viewport.center)} zoom={viewport.zoom}",
        )

    @classmethod
    def _dimension_lines(cls, dimensions) -> tuple[str, ...]:
        return (
            "Native dimensions: "
            f"displayed_axes={cls.sequence_text(dimensions.displayed_axes)} "
            f"ndisplay={dimensions.ndisplay} order={cls.json_text(dimensions.order)} "
            f"point={cls.json_text(dimensions.point)} "
            f"camera_angles={cls.json_text(dimensions.camera_angles)}",
            *cls.optional_lines(
                dimensions.canvas_size,
                lambda size: (f"Native canvas: width={size[0]} height={size[1]}",),
            ),
        )

    @classmethod
    def _layer_lines(cls, layers) -> list[str]:
        lines: list[str] = []
        for layer in layers:
            lines.append(
                "- "
                f"{layer.route_key}: "
                f"title={cls.quoted(layer.title)} "
                f"visible={layer.visible} selected={layer.selected} items={layer.item_count} "
                f"types={cls.sequence_text(layer.data_types)} "
                f"axes={cls.sequence_text(layer.axis_labels)} "
                f"stack={cls.sequence_text(layer.stack_axes)} "
                f"shape={cls.json_text(layer.data_shape)}"
            )
            lines.append(
                f"  components: {cls._component_values_text(layer.component_values)}"
            )
            lines.extend(
                cls.optional_lines(
                    layer.native_intensity,
                    lambda intensity: (
                        "  native intensity: "
                        f"contrast_limits={cls.json_text(intensity.contrast_limits)} "
                        f"gamma={intensity.gamma}",
                    ),
                )
            )
            if layer.native_transform.scale:
                lines.append(
                    "  native transform: "
                    f"scale={cls.json_text(layer.native_transform.scale)} "
                    f"translate={cls.json_text(layer.native_transform.translate)}"
                )
            if layer.axis_component_values:
                lines.append(
                    f"  axis values: {cls.mapping_text(layer.axis_component_values)}"
                )
            if layer.routed_component_values:
                lines.append(
                    f"  routed values: {cls.mapping_text(layer.routed_component_values)}"
                )
            if layer.payload_summaries:
                lines.append(
                    "  payload summaries: "
                    f"{layer.payload_summary_count} "
                    f"truncated={layer.payload_summaries_truncated}"
                )
                lines.extend(
                    f"  payload summary: {cls.json_text(summary)}"
                    for summary in layer.payload_summaries[:3]
                )
        return lines

    @classmethod
    def _component_values_text(cls, values) -> str:
        """Merge the distinct values seen for each component across a layer."""
        merged: dict[str, list[str]] = {}
        for item in values:
            for key, component_value in item.items():
                seen = merged.setdefault(str(key), [])
                text = cls.text(component_value)
                if text not in seen:
                    seen.append(text)
        if not merged:
            return "<none>"
        return ", ".join(
            f"{key}={','.join(seen)}" for key, seen in sorted(merged.items())
        )


class ViewerPayloadRenderer(ViewerResultRenderer):
    """Compact renderer for viewer payload inspection records."""

    output_contract = ViewerWindowPayloadResult
    unavailable_summary = "Viewer payloads: failed"

    @classmethod
    def render_payload(cls, payload: ViewerWindowPayloadResult, options) -> str:
        lines = [
            f"Viewer payloads: observed={payload.observed} layers={payload.layer_count}"
        ]
        if payload.layers:
            lines.append("Layers:")
            for layer in payload.layers:
                payloads = layer.payloads
                lines.append(
                    "- "
                    f"{layer.route_key}: "
                    f"title={cls.quoted(layer.title)} "
                    f"mounted={layer.mounted} items={layer.item_count} "
                    f"axes={cls.sequence_text(layer.axis_labels)} "
                    f"stack={cls.sequence_text(layer.stack_axes)} "
                    f"payloads={len(payloads)} "
                    f"pending={layer.pending_update}"
                )
                lines.extend(cls._payload_line(record) for record in payloads[:5])
                if len(payloads) > 5:
                    lines.append(f"  ...<truncated {len(payloads) - 5} payloads>")
        return "\n".join(lines)

    @classmethod
    def _payload_line(cls, payload) -> str:
        summary = payload.summary
        array_summary = payload.array_value_summary
        return (
            "  payload "
            f"type={payload.data_type} "
            f"axis={cls.axis_text(payload.axis_indices)} "
            f"aggregate_axis={cls.axis_text(payload.aggregate_axis_indices)} "
            f"components={cls.mapping_text(payload.components)} "
            f"shape={cls.json_text(summary.optional(summary.shape))} "
            f"dtype={cls.text(summary.optional(summary.dtype))} "
            f"nonzero={cls.text(summary.known_nonzero_count)} "
            f"shape_members={cls.text(summary.optional(summary.shape_payload_count))} "
            f"returned_shapes={len(payload.shape_payloads)} semantic_rois=use-viewer-rois "
            f"array=included={cls.text(array_summary.optional(array_summary.included))} "
            f"sample_shape={cls.json_text(array_summary.optional(array_summary.shape))} "
            f"reason={cls.text(array_summary.optional(array_summary.omitted_reason))} "
            f"path={cls.path_text(payload.path)}"
        )


class ViewerRoiSummaryRenderer(ViewerResultRenderer):
    """Compact renderer for viewer ROI summaries."""

    output_contract = ViewerWindowRoiSummaryResult
    unavailable_summary = "Viewer ROIs: failed"

    @classmethod
    def render_payload(cls, payload: ViewerWindowRoiSummaryResult, options) -> str:
        lines = [
            (
                "Viewer ROIs: "
                f"observed={payload.observed} "
                f"route={cls.text(payload.route_key)} "
                f"axis={cls.axis_text(payload.axis_indices)} "
                f"layers={payload.layer_count} records={payload.payload_record_count} "
                f"payloads={payload.roi_payload_count}"
            ),
            (
                "ROIs: "
                f"total={payload.total_roi_count} returned={payload.returned_roi_count} "
                f"exact={payload.roi_count_exact} members={payload.total_roi_member_count}/"
                f"{payload.returned_roi_member_count} truncated={payload.roi_payloads_truncated}"
            ),
        ]
        if payload.payload_type_counts:
            lines.append(f"Payload types: {cls.mapping_text(payload.payload_type_counts)}")
        if payload.payloads:
            lines.append("Payloads:")
            lines.extend(cls._payload_lines(payload.payloads))
        elif payload.should_explain_missing_rois:
            lines.extend(cls._no_roi_guidance(payload))
        return "\n".join(lines)

    @classmethod
    def _no_roi_guidance(cls, payload: ViewerWindowRoiSummaryResult) -> list[str]:
        if payload.total_roi_count != 0:
            return []
        route_key = payload.route_key
        lines = [
            (
                "Interpretation: no ROI/shapes payloads were found for the "
                "requested viewer" + (" route." if route_key else ".")
            ),
            "Next:",
            "- Run `viewer-state <port>` to list layer route keys, layer types, and visible image layers.",
        ]
        if route_key:
            lines.append(
                "- Check that the selected route is a shapes/ROI layer, or stream ROI artifacts to the viewer."
            )
        else:
            lines.append(
                "- If `viewer-state` shows a shapes layer, rerun `viewer-rois <port> <route_key>` for that route."
            )
        if payload.payload_type_counts:
            lines.append(
                "- If payload types are image-only, this pipeline/viewer state has no streamed ROI layer."
            )
        lines.append(
            "- To validate output artifacts, query selected output files and stream ROI files if they exist."
        )
        return lines

    @classmethod
    def _payload_lines(cls, roi_payloads) -> list[str]:
        lines: list[str] = []
        for roi_payload in roi_payloads:
            lines.append(
                "- "
                f"title={cls.quoted(cls.text(roi_payload.layer_title))} "
                f"layer_route={roi_payload.layer_route_key} "
                f"payload_route={cls._route_summary(roi_payload.payload_route_key)} "
                f"axis={cls.axis_text(roi_payload.axis_indices)} "
                f"components={cls.mapping_text(roi_payload.components)} "
                f"roi_count={roi_payload.roi_count} returned={roi_payload.returned_roi_count} "
                f"exact={roi_payload.roi_count_exact} members={roi_payload.roi_member_count}/"
                f"{roi_payload.returned_roi_member_count} duplicate_members={roi_payload.roi_duplicate_member_count} "
                f"truncated={roi_payload.roi_payloads_truncated} "
                f"area={cls._stats_text(roi_payload.area)} perimeter={cls._stats_text(roi_payload.perimeter)} "
                f"bounds={cls.json_text(roi_payload.bounds_yx)} "
                f"coords={cls.text(roi_payload.coordinate_count)} "
                f"source_origin={cls.json_text(roi_payload.spatial_origin_yx)} "
                f"source_shape={cls.json_text(roi_payload.source_spatial_shape_yx)} "
                f"out_of_bounds={cls.text(roi_payload.out_of_source_bounds_count)}"
            )
            lines.extend(
                "  example "
                f"label={cls.text(example.label)} "
                f"area={cls.text(example.area)} "
                f"centroid={cls.json_text(example.centroid_yx)} "
                f"bbox={cls.json_text(example.bbox_yxyx)}"
                for example in roi_payload.example_rois[:2]
            )
        return lines

    @classmethod
    def _route_summary(cls, value: str | None) -> str:
        text = cls.text(value)
        if value is None or len(text) <= 80:
            return text
        separator_index = text.rfind("::")
        if separator_index >= 0:
            return f"...{text[separator_index:]}"
        return f"{text[:32]}...{text[-32:]}"

    @classmethod
    def _stats_text(cls, value) -> str:
        if value is None:
            return "<none>"
        return f"min={value.min},median={value.median},mean={value.mean},max={value.max}"


class ViewerImageSampleRenderer(ViewerResultRenderer):
    """Compact renderer for viewer image samples."""

    output_contract = ViewerWindowImageSampleResult
    render_options_type = ViewerImageSampleRenderOptions
    unavailable_summary = "Viewer image sample: failed"

    @classmethod
    def render_payload(
        cls,
        payload: ViewerWindowImageSampleResult,
        options: ViewerImageSampleRenderOptions,
    ) -> str:
        lines = [
            (
                "Viewer image sample: "
                f"observed={payload.observed} "
                f"route={cls.text(payload.route_key)} "
                f"axis={cls.axis_text(payload.axis_indices)} "
                f"slices={cls.json_text(payload.array_slices)}"
            ),
            (
                "Records: "
                f"matched={payload.record_count} returned={payload.returned_record_count} "
                f"truncated={payload.records_truncated_count} image={payload.raw_image_record_count} "
                f"total_payloads={payload.total_payload_record_count} "
                f"sample_supported={payload.sample_protocol_supported} "
                f"included={payload.sample_included_count} omitted={payload.sample_omitted_count}"
            ),
        ]
        if payload.candidate_image_route_keys:
            lines.append(
                f"Image routes: {cls.sequence_text(payload.candidate_image_route_keys)}"
            )
        if payload.records:
            lines.append("Image records:")
            lines.extend(
                cls._record_lines(
                    payload.records,
                    include_array_values_requested=options.include_array_values_requested,
                )
            )
        return "\n".join(lines)

    @classmethod
    def _record_lines(
        cls,
        records,
        *,
        include_array_values_requested: bool | None,
    ) -> list[str]:
        lines: list[str] = []
        for record in records:
            array_summary = record.array_value_summary
            summary = record.summary
            array_reason = array_summary.presentation_omission_reason(
                include_requested=include_array_values_requested,
            )
            reason_text = f" reason={array_reason}" if array_reason else ""
            max_elements_text = "".join(
                cls.optional_lines(
                    array_summary.optional(array_summary.max_array_elements),
                    lambda value: (f" max_elements={value}",),
                )
            )
            rerun_hint = ""
            required_elements = array_summary.shape_element_count
            if (
                array_reason == "max_array_elements_exceeded"
                and required_elements is not None
            ):
                rerun_hint = f" rerun_max_elements={required_elements}"
            if array_reason == "array_values_not_requested":
                rerun_hint = " rerun_with=--include-array-values"
                if required_elements is not None:
                    rerun_hint += f" --max-array-elements {required_elements}"
            lines.append(
                "- "
                f"{record.payload_route_key}: layer={record.layer_route_key} "
                f"axis={cls.axis_text(record.axis_indices)} "
                f"path={cls.path_text(record.path)} "
                f"shape={cls.json_text(summary.optional(summary.shape))} "
                f"dtype={cls.text(summary.optional(summary.dtype))} "
                f"min={cls.text(summary.optional(summary.min))} "
                f"max={cls.text(summary.optional(summary.max))} "
                f"nonzero={cls.text(summary.known_nonzero_count)} "
                f"included={cls.text(array_summary.optional(array_summary.included))} "
                f"sample_shape={cls.json_text(array_summary.optional(array_summary.shape))}"
                f"{reason_text}"
                f"{max_elements_text}"
                f"{rerun_hint}"
            )
            if (
                array_summary.sample_included
                and cls.json_value_count(record.array_values) <= 64
            ):
                lines.append(
                    f"  sample values: {json.dumps(to_jsonable(record.array_values))}"
                )
        return lines


class ViewerNavigationRenderer(ViewerResultRenderer):
    """Compact renderer for viewer navigation results."""

    output_contract = ViewerWindowNavigationResult
    unavailable_summary = "Viewer navigation: failed"

    @classmethod
    def render_payload(cls, payload: ViewerWindowNavigationResult, options) -> str:
        return "\n".join(
            (
                "Viewer navigation: "
                f"observed={payload.observed} "
                f"route={cls.text(payload.route_key)} "
                f"visible={cls.text(payload.visible)} "
                f"selected={cls.text(payload.selected)}",
                cls.position_line(payload),
                *cls.visibility_lines("Available layers", payload.available_layers),
            )
        )


class ViewerLayerIsolationRenderer(ViewerResultRenderer):
    """Compact renderer for viewer layer isolation results."""

    output_contract = ViewerWindowLayerIsolationResult
    unavailable_summary = "Viewer isolation: failed"

    @classmethod
    def render_payload(
        cls, payload: ViewerWindowLayerIsolationResult, options
    ) -> str:
        lines = [
            (
                "Viewer isolation: "
                f"observed={payload.observed} "
                f"applied={payload.applied} "
                f"selected={cls.text(payload.selected_route_key)} "
                f"changed={payload.changed_route_count} "
                f"layers={payload.layer_count}"
            ),
            cls.position_line(payload),
            f"Visible: {cls.sequence_text(payload.visible_route_keys)}",
            f"Hidden: {cls.sequence_text(payload.hidden_route_keys)}",
        ]
        if payload.missing_route_keys:
            lines.append(
                f"Missing routes: {cls.sequence_text(payload.missing_route_keys)}"
            )
        lines.extend(cls.visibility_lines("Available layers", payload.available_layers))
        lines.extend(cls.visibility_lines("Visible layers", payload.visible_layers))
        return "\n".join(lines)


class RuntimeServerInfoRenderer(McpDevOutputRenderer):
    """Compact renderer for one runtime server's ping state."""

    output_contract = RuntimeServerInfo
    unavailable_summary = "Runtime server: unavailable"

    @classmethod
    def render_payload(cls, payload: RuntimeServerInfo, options) -> str:
        return "\n".join(("Runtime server:", cls.server_line(payload)))

    @classmethod
    def server_line(cls, server: RuntimeServerInfo) -> str:
        return (
            "- "
            f"port={cls.text(server.connection.port)} "
            f"server={cls.text(server.server)} "
            f"reachable={server.reachable} "
            f"ready={cls.text(server.ready)} "
            f"control={cls.text(server.control_port)} "
            f"active={cls.text(server.active_executions)} "
            f"running={len(server.running_executions)} "
            f"queued={len(server.queued_executions)} "
            f"workers={len(server.workers)} "
            f"uptime={cls.seconds_text(server.uptime)} "
            f"log={cls.text(server.log_file_path)}"
        )

    @classmethod
    def seconds_text(cls, value: float | None) -> str:
        return "<none>" if value is None else f"{float(value):.1f}s"


class RuntimeServerScanRenderer(RuntimeServerInfoRenderer):
    """Compact renderer for a runtime server port scan."""

    output_contract = RuntimeServerScanResult
    unavailable_summary = "Runtime scan: unavailable"

    @classmethod
    def render_payload(cls, payload: RuntimeServerScanResult, options) -> str:
        lines = [
            "Runtime scan: "
            f"ports={cls.sequence_text(payload.ports)} "
            f"timeout_ms={payload.timeout_ms} "
            f"servers={len(payload.servers)}"
        ]
        if payload.servers:
            lines.append("Servers:")
            lines.extend(cls.server_line(server) for server in payload.servers)
        return "\n".join(lines)


class RuntimeExecutionStatusRenderer(McpDevOutputRenderer):
    """Compact renderer for one runtime execution status request."""

    output_contract = RuntimeExecutionStatus
    unavailable_summary = "Runtime execution status: unavailable"

    @classmethod
    def render_payload(cls, payload: RuntimeExecutionStatus, options) -> str:
        lines = [
            "Runtime execution status: "
            f"status={payload.status} "
            f"execution_id={cls.text(payload.execution_id)} "
            f"port={cls.text(payload.connection.port)}"
        ]
        if payload.response:
            # The execution server's status reply, decoded by its own codec.
            snapshot = ExecutionStatusSnapshot.from_dict(payload.response)
            lines.append(
                "Executions: "
                f"known={len(snapshot.executions or ())} "
                f"active={cls.text(snapshot.active_executions)} "
                f"running={len(snapshot.running_executions or ())} "
                f"queued={len(snapshot.queued_executions or ())} "
                f"uptime={RuntimeServerInfoRenderer.seconds_text(snapshot.uptime)}"
            )
        return "\n".join(lines)


class RuntimeDebugInspectionRenderer(McpDevOutputRenderer):
    """Compact renderer for one renderer-independent paused-worker view."""

    output_contract = RuntimeDebugInspectionResult
    render_options_type = CatalogRenderOptions
    unavailable_summary = "Runtime debug: unavailable"
    MAX_CELL_CHARS = 160
    MAX_TEXT_CHARS = 500

    @classmethod
    def render_payload(
        cls, payload: RuntimeDebugInspectionResult, options: CatalogRenderOptions
    ) -> str:
        view_model = payload.view_model
        if view_model is None:
            return cls.unavailable_summary
        contains = options.contains
        sections = view_model.sections
        matching_sections = tuple(
            section for section in sections if cls._section_matches(section, contains)
        )
        total_items = sum(cls._item_count(section) for section in sections)
        matched_items = sum(
            cls._matched_item_count(section, contains) for section in matching_sections
        )
        remaining = max(options.limit, 0)
        shown_items = 0
        shown_sections = 0
        body_lines: list[str] = []
        for section in matching_sections:
            section_lines, section_shown_items = cls._section_lines(
                section, contains=contains, remaining=remaining
            )
            if not section_lines:
                continue
            shown_sections += 1
            shown_items += section_shown_items
            remaining -= section_shown_items
            body_lines.extend(section_lines)

        connection = payload.connection
        return "\n".join(
            (
                "Runtime debug: "
                f"session={payload.debug_session_id} "
                f"endpoint={connection.host}:{cls.text(connection.port)} "
                f"transport={cls.text(connection.transport_mode)} "
                f"persistent={connection.persistent} "
                f"title={cls.quoted(view_model.title)}",
                "Sections: "
                f"total={len(sections)} matched={len(matching_sections)} "
                f"shown={shown_sections}",
                "Items: "
                f"total={total_items} matched={matched_items} shown={shown_items} "
                f"truncated={max(matched_items - shown_items, 0)} "
                f"limit={max(options.limit, 0)}",
                *options.filter_lines(),
                *body_lines,
            )
        )

    @classmethod
    def _section_lines(
        cls,
        section: DebugViewSection,
        *,
        contains: str | None,
        remaining: int,
    ) -> tuple[list[str], int]:
        rows = cls._rows(section)
        matching_rows = cls._matching_rows(section, rows, contains)
        visible_rows = matching_rows[:remaining]
        text = section.text or None
        text_matches = cls._text_matches(section, text, contains)
        show_text = text_matches and len(visible_rows) < remaining
        shown_items = len(visible_rows) + int(show_text)
        matching_items = len(matching_rows) + int(text_matches)
        if matching_items > 0 and shown_items == 0:
            return [], 0

        lines = [
            "Section: "
            f"kind={cls._bounded_cell(section.kind)} "
            f"title={cls.quoted(section.title)} "
            f"items={cls._item_count(section)} "
            f"matched={matching_items} shown={shown_items} "
            f"truncated={max(matching_items - shown_items, 0)}"
        ]
        table = section.table
        if table is not None:
            columns = cls._columns(section)
            lines.append(
                f"Columns ({len(columns)}): "
                + (" | ".join(columns) if columns else "<none>")
            )
            lines.append(
                "Rows: "
                f"total={len(rows)} matched={len(matching_rows)} "
                f"shown={len(visible_rows)} "
                f"truncated={max(len(matching_rows) - len(visible_rows), 0)}"
            )
            lines.extend("- " + " | ".join(row) for row in visible_rows)
            if not rows and table.empty_message:
                lines.append(f"Empty: {cls.quoted(table.empty_message)}")
        if text is not None and text_matches:
            compact_text = " ".join(text.split())
            visible_text = cls._bounded_text(compact_text) if show_text else ""
            lines.append(
                "Text: "
                f"chars={len(compact_text)} shown={len(visible_text)} "
                f"truncated={max(len(compact_text) - len(visible_text), 0)}"
            )
            if visible_text:
                lines.append(f"- {visible_text}")
        return lines, shown_items

    @classmethod
    def _columns(cls, section: DebugViewSection) -> tuple[str, ...]:
        if section.table is None:
            return ()
        return tuple(cls._bounded_cell(column) for column in section.table.columns)

    @classmethod
    def _rows(cls, section: DebugViewSection) -> tuple[tuple[str, ...], ...]:
        if section.table is None:
            return ()
        return tuple(
            tuple(cls._bounded_cell(cell) for cell in row) for row in section.table.rows
        )

    @classmethod
    def _matching_rows(
        cls,
        section: DebugViewSection,
        rows: tuple[tuple[str, ...], ...],
        contains: str | None,
    ) -> tuple[tuple[str, ...], ...]:
        if not contains or cls._metadata_matches(section, contains):
            return rows
        needle = contains.casefold()
        return tuple(row for row in rows if needle in " | ".join(row).casefold())

    @classmethod
    def _text_matches(
        cls,
        section: DebugViewSection,
        text: str | None,
        contains: str | None,
    ) -> bool:
        if text is None:
            return False
        if not contains or cls._metadata_matches(section, contains):
            return True
        return contains.casefold() in text.casefold()

    @classmethod
    def _section_matches(cls, section: DebugViewSection, contains: str | None) -> bool:
        if not contains or cls._metadata_matches(section, contains):
            return True
        return bool(
            cls._matching_rows(section, cls._rows(section), contains)
        ) or cls._text_matches(section, section.text or None, contains)

    @classmethod
    def _metadata_matches(cls, section: DebugViewSection, contains: str) -> bool:
        metadata = " ".join(
            (
                cls.text(section.kind),
                section.title,
                " ".join(cls._columns(section)),
                cls.text(None if section.table is None else section.table.empty_message),
            )
        )
        return contains.casefold() in metadata.casefold()

    @classmethod
    def _item_count(cls, section: DebugViewSection) -> int:
        return len(cls._rows(section)) + int(bool(section.text))

    @classmethod
    def _matched_item_count(cls, section: DebugViewSection, contains: str | None) -> int:
        return len(cls._matching_rows(section, cls._rows(section), contains)) + int(
            cls._text_matches(section, section.text or None, contains)
        )

    @classmethod
    def _bounded_cell(cls, value) -> str:
        text = cls.text(value)
        if len(text) <= cls.MAX_CELL_CHARS:
            return text
        return f"{text[: cls.MAX_CELL_CHARS - 3]}..."

    @classmethod
    def _bounded_text(cls, value: str) -> str:
        if len(value) <= cls.MAX_TEXT_CHARS:
            return value
        return f"{value[: cls.MAX_TEXT_CHARS - 3]}..."


class ViewerProbeRenderer(ViewerResultRenderer):
    """Compact renderer for cheap viewer reachability probes."""

    output_contract = ViewerWindowProbeResult
    unavailable_summary = "Viewer probe: unavailable"

    @classmethod
    def render_payload(
        cls, payload: ViewerWindowProbeResult, options: McpDevOutputRenderOptions
    ) -> str:
        return "\n".join(
            (
                "Viewer probe: "
                f"reachable={payload.reachable} observed={payload.observed} "
                f"{cls.viewer_text(payload.viewer)}",
                "Window: "
                f"port={payload.connection.port} layers={payload.layer_count} "
                f"component_groups={payload.component_group_count} "
                f"component_items={payload.component_item_count}",
            )
        )


class SnapshotResourceRenderer(McpDevOutputRenderer):
    """Image and resource lines shared by viewer and UI window snapshots."""

    @classmethod
    def resource_lines(cls, payload) -> tuple[str, str]:
        resource = payload.resource
        return (
            "Image: "
            f"size={cls.text(payload.width)}x{cls.text(payload.height)} "
            f"bytes={cls.text(None if resource is None else resource.size_bytes)} "
            f"mime={cls.text(None if resource is None else resource.mime_type)}",
            "Resource: "
            f"path={cls.text(None if resource is None else resource.path)} "
            f"uri={cls.text(None if resource is None else resource.uri)} "
            f"sha256={cls.text(None if resource is None else resource.sha256)}",
        )


class ViewerSnapshotRenderer(SnapshotResourceRenderer, ViewerResultRenderer):
    """Compact renderer for viewer snapshot resources."""

    output_contract = ViewerWindowSnapshotResult
    unavailable_summary = "Viewer snapshot: unavailable"

    @classmethod
    def render_payload(cls, payload: ViewerWindowSnapshotResult, options) -> str:
        return "\n".join(
            (
                "Viewer snapshot: "
                f"captured={payload.captured} "
                f"{cls.viewer_text(payload.viewer)} "
                f"scope={cls.text(payload.capture_scope)}",
                *cls.resource_lines(payload),
            )
        )


class WindowSnapshotRenderer(SnapshotResourceRenderer):
    """Compact renderer for UI bridge window snapshot resources."""

    output_contract = UiWindowSnapshotResult
    unavailable_summary = "Window snapshot: unavailable"

    @classmethod
    def render_payload(cls, payload: UiWindowSnapshotResult, options) -> str:
        summary = payload.summary
        lines = [
            "Window snapshot: "
            f"captured={payload.captured} "
            f"window={payload.window_id} "
            f"title={cls.quoted(None if summary is None else summary.title)} "
            f"kind={cls.text(None if summary is None else summary.window_kind)} "
            f"scope={cls.text(payload.capture_scope)}",
        ]
        if summary is not None:
            lines.append(
                "Status: "
                f"visible={summary.visible} "
                f"dirty={summary.dirty} "
                f"dirty_fields={summary.dirty_field_count} "
                f"default_diff={summary.signature_diff} "
                f"default_diff_fields={summary.signature_diff_field_count} "
                f"markers={''.join(summary.semantic_markers) or '-'}"
            )
        lines.extend(cls.resource_lines(payload))
        if payload.operation_id:
            lines.append(
                f"Observation operation: {payload.operation_id} (use operation-wait)"
            )
        if summary is not None and summary.object_state_scope_id:
            lines.append(f"ObjectState: scope={summary.object_state_scope_id}")
        if summary is not None and summary.managed_action_ids:
            lines.append("Actions: " + ",".join(summary.managed_action_ids))
        return "\n".join(lines)
