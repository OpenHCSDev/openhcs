"""Plate inspection, query, sampling and streaming renderers for the MCP dev client."""

from __future__ import annotations

import json
from collections.abc import Callable, Sequence
from math import prod
from pathlib import Path
from typing import ClassVar

from python_introspect import JsonObject, JsonValue, dataclass_from_mapping

from openhcs.agent.dto.plate import (
    PlateFileQueryRecordSummary,
    PlateFileQueryResult,
    PlateFileStreamResult,
    PlateImageSampleResult,
    PlateInspectionComponentSummary,
    PlateInspectionComponentValue,
    PlateInspectionHandlerCandidate,
    PlateInspectionImageRecordSummary,
    PlateInspectionIssueCode,
    PlateInspectionResultFilePreview,
    PlateInspectionResultFileRecordSummary,
    PlatePathInspectionResult,
    SelectedPlateFileQueryResult,
    SelectedPlateFileQueryTarget,
    SelectedPlateFileStreamResult,
    SelectedPlateImageInspectionResult,
    SelectedPlateImageSampleResult,
    SyntheticPlateGenerationResult,
)
from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.ui_bridge import UiPlateManagerRowState
from openhcs.core.axes import AxisFamily
from openhcs.core.plate_file_inventory import PlateFileKind
from openhcs.mcp.dev_client_rendering import (
    McpDevOutputRenderer,
    McpDevOutputRenderOptions,
)

FileRecord = (
    PlateInspectionImageRecordSummary
    | PlateInspectionResultFileRecordSummary
    | PlateFileQueryRecordSummary
)


def json_member(bag: JsonObject, name: str) -> JsonValue:
    """Read one member of a dynamic JSON bag that no DTO class models.

    File stat metadata (``size``/``modified``), CSV preview rows, ROI examples
    and handler source diagnostics are open JSON objects on the wire; their
    members are conventions of the producing reader, not declared fields.
    """
    return bag[name] if name in bag else None


def _dimensions_text(values: Sequence[object] | None) -> str:
    if values is None:
        return "<none>"
    return "x".join(str(value) for value in values)


class PlateFileRecordPresentation:
    """Shared presentation of inventory file records and their stat metadata."""

    MODIFIED: ClassVar[str] = "modified"
    SIZE: ClassVar[str] = "size"

    @classmethod
    def modified(cls, record: FileRecord) -> str | None:
        modified = json_member(record.metadata, cls.MODIFIED)
        return None if modified is None else McpDevOutputRenderer.text(modified)

    @classmethod
    def metadata_suffix(cls, record: FileRecord) -> str:
        parts = [
            f"{name}={McpDevOutputRenderer.text(value)}"
            for name in (cls.MODIFIED, cls.SIZE)
            if (value := json_member(record.metadata, name)) is not None
        ]
        return " " + " ".join(parts) if parts else ""

    @classmethod
    def modified_summary_line(
        cls, label: str, records: Sequence[FileRecord]
    ) -> str | None:
        modified_values = tuple(
            modified for record in records if (modified := cls.modified(record))
        )
        if not modified_values:
            return None
        distinct_values = tuple(sorted(set(modified_values)))
        latest, earliest = distinct_values[-1], distinct_values[0]
        if len(distinct_values) == 1:
            return f"{label}: {latest}"
        older_record_count = sum(1 for value in modified_values if value != latest)
        return (
            f"{label}: mixed latest={latest} earliest={earliest} "
            f"distinct={len(distinct_values)} older_records={older_record_count}"
        )

    @classmethod
    def query_record_lines(
        cls, records: Sequence[PlateFileQueryRecordSummary]
    ) -> list[str]:
        lines: list[str] = []
        for record in records:
            head = f"- {record.kind.value} {record.key}"
            suffix = cls.metadata_suffix(record)
            if record.source_path is not None:
                lines.append(f"{head} -> {record.source_path}{suffix}")
            elif record.full_path is not None:
                lines.append(
                    f"{head} type={McpDevOutputRenderer.text(record.file_format)} "
                    f"-> {record.full_path}{suffix}"
                )
                lines.extend(ResultPreviewPresentation.lines(record.preview))
            else:
                lines.append(f"{head}{suffix}")
        return lines


class ResultPreviewPresentation:
    """Bounded text, CSV and ROI previews of one analysis artifact."""

    MAX_TEXT_PREVIEW_LINES: ClassVar[int] = 3
    MAX_CSV_PREVIEW_ROWS: ClassVar[int] = 3
    MAX_CSV_PREVIEW_COLUMNS: ClassVar[int] = 8
    MAX_TEXT_PREVIEW_CHARS: ClassVar[int] = 180
    MAX_CSV_CELL_CHARS: ClassVar[int] = 90
    MAX_CSV_COLUMN_CHARS: ClassVar[int] = 48
    MAX_CSV_ROW_CHARS: ClassVar[int] = 520

    @classmethod
    def lines(cls, preview: PlateInspectionResultFilePreview | None) -> list[str]:
        if preview is None:
            return []
        if preview.omitted_reason is not None:
            return [f"  preview omitted: {preview.omitted_reason}"]
        if preview.roi_count is not None:
            return cls._roi_lines(preview)
        csv_lines = cls._csv_lines(preview)
        if csv_lines:
            return csv_lines
        if not preview.text_lines:
            return []
        visible_lines = preview.text_lines[: cls.MAX_TEXT_PREVIEW_LINES]
        lines = [f"  preview: {cls.bounded(line)}" for line in visible_lines]
        if preview.truncated or len(preview.text_lines) > len(visible_lines):
            lines.append("  preview: ...")
        return lines

    @classmethod
    def _roi_lines(cls, preview: PlateInspectionResultFilePreview) -> list[str]:
        member_text = (
            f"members={preview.roi_member_count} "
            f"duplicate_members={preview.roi_duplicate_member_count} "
            if preview.roi_member_count is not None
            and preview.roi_duplicate_member_count is not None
            and preview.roi_duplicate_member_count > 0
            else ""
        )
        lines = [
            f"  roi preview: count={preview.roi_count} {member_text}"
            f"area={cls._roi_area_text(preview)}"
        ]
        for example in preview.roi_examples[:3]:
            lines.append(
                "  roi example: "
                f"label={McpDevOutputRenderer.text(json_member(example, 'label'))} "
                f"area={McpDevOutputRenderer.text(json_member(example, 'area'))} "
                f"bbox={McpDevOutputRenderer.json_text(json_member(example, 'bbox'))} "
                "centroid="
                f"{McpDevOutputRenderer.json_text(json_member(example, 'centroid'))}"
            )
        if preview.truncated:
            lines.append("  roi preview: ...")
        return lines

    @staticmethod
    def _roi_area_text(preview: PlateInspectionResultFilePreview) -> str:
        if (
            preview.roi_area_min is None
            and preview.roi_area_max is None
            and preview.roi_area_mean is None
        ):
            return "<none>"
        mean = (
            "<none>" if preview.roi_area_mean is None else f"{preview.roi_area_mean:.3f}"
        )
        return (
            f"min={McpDevOutputRenderer.text(preview.roi_area_min)},"
            f"mean={mean},"
            f"max={McpDevOutputRenderer.text(preview.roi_area_max)}"
        )

    @classmethod
    def _csv_lines(cls, preview: PlateInspectionResultFilePreview) -> list[str]:
        columns, rows = preview.csv_columns, preview.csv_rows
        if (
            not columns
            or not all(columns)
            or len(set(columns)) != len(columns)
            or not rows
        ):
            return []
        lines = [f"  csv columns: {cls._csv_columns_text(columns)}"]
        visible_rows = rows[: cls.MAX_CSV_PREVIEW_ROWS]
        lines.extend(f"  csv row: {cls._csv_row_text(columns, row)}" for row in visible_rows)
        omitted_row_count = len(rows) - len(visible_rows)
        if omitted_row_count > 0:
            lines.append(
                "  csv preview: "
                f"showing {len(visible_rows)}/{len(rows)} rows; "
                f"{omitted_row_count} more in payload"
            )
        if preview.truncated:
            lines.append("  csv preview: ...")
        return lines

    @classmethod
    def _csv_row_text(cls, columns: tuple[str, ...], row: JsonObject) -> str:
        compact_cells: list[str] = []
        wide_columns: list[str] = []
        for column in columns:
            value_text = McpDevOutputRenderer.text(json_member(row, column))
            column_text = cls.bounded(column, cls.MAX_CSV_COLUMN_CHARS)
            if (
                "\n" not in value_text
                and "\r" not in value_text
                and len(value_text) <= cls.MAX_CSV_CELL_CHARS
            ):
                compact_cells.append(f"{column_text}={value_text}")
            else:
                wide_columns.append(column_text)
        row_text = ", ".join(compact_cells) if compact_cells else "<no compact cells>"
        if wide_columns:
            row_text = f"{row_text}; omitted wide cells: {', '.join(wide_columns)}"
        return cls.bounded(row_text, cls.MAX_CSV_ROW_CHARS)

    @classmethod
    def _csv_columns_text(cls, columns: tuple[str, ...]) -> str:
        visible_columns = columns[: cls.MAX_CSV_PREVIEW_COLUMNS]
        column_text = ", ".join(
            cls.bounded(column, cls.MAX_CSV_COLUMN_CHARS) for column in visible_columns
        )
        hidden_count = len(columns) - len(visible_columns)
        if hidden_count > 0:
            column_text = f"{column_text}; {hidden_count} more columns"
        return cls.bounded(column_text, cls.MAX_CSV_ROW_CHARS)

    @classmethod
    def bounded(cls, text: str, max_chars: int | None = None) -> str:
        limit = cls.MAX_TEXT_PREVIEW_CHARS if max_chars is None else max_chars
        return text if len(text) <= limit else f"{text[:limit]}..."


class PlateImageSampleRenderer(McpDevOutputRenderer):
    """Compact renderer for sampled plate image pixels and statistics."""

    output_contract = PlateImageSampleResult
    unavailable_summary = "Sample failed: <unavailable>"

    @classmethod
    def render_payload(
        cls, sample: PlateImageSampleResult, options: McpDevOutputRenderOptions
    ) -> str:
        if sample.errors:
            return "Sample failed:"
        sample_value_count = cls.json_value_count(sample.sample_values)
        lines = [
            f"Image: {cls.text(sample.virtual_path)}",
            f"Source: {cls.text(sample.source_path)}",
            (
                "Resolution: "
                f"selected={cls.text(sample.selected_resolution_index)} "
                f"count={cls.text(sample.resolution_count)} "
                f"source_shape={_dimensions_text(sample.shape)} "
                f"resolution_shape={_dimensions_text(sample.resolution_shape)} "
                f"downsample_yx={_dimensions_text(sample.downsample_yx)}"
            ),
            (
                "Statistics: "
                f"scope={cls.text(sample.statistics_scope)} "
                f"dtype={cls.text(sample.dtype)} "
                f"min={cls.text(sample.minimum)} "
                f"max={cls.text(sample.maximum)} "
                f"mean={'<none>' if sample.mean is None else f'{sample.mean:.3f}'}"
            ),
            (
                "Sample: "
                f"origin_yx={_dimensions_text(sample.sample_origin_yx)} "
                f"shape={_dimensions_text(sample.sample_shape)} "
                f"included={sample.sample_included}"
            ),
        ]
        if sample.sample_included:
            if sample_value_count <= 64:
                lines.append("Sample values:")
                lines.append(json.dumps(sample.sample_values, indent=2))
            else:
                lines.append(
                    f"Sample values: {sample_value_count} elements; "
                    "pass --json to print them."
                )
        else:
            lines.append(cls._omitted_line(sample))
        return "\n".join(lines)

    @classmethod
    def _omitted_line(cls, sample: PlateImageSampleResult) -> str:
        omitted_reason = cls.text(sample.sample_omitted_reason)
        line = f"Sample values omitted: {omitted_reason}"
        required_elements = prod(sample.sample_shape) if sample.sample_shape else None
        if "max_array_elements" in omitted_reason and required_elements is not None:
            line += (
                f"; rerun with --max-array-elements {required_elements} "
                "or smaller --width/--height"
            )
        elif omitted_reason == "array_values_not_requested":
            line += "; rerun with --include-array-values"
            if required_elements is not None:
                line += f" --max-array-elements {required_elements}"
        return line


class SyntheticPlateGenerationRenderer(McpDevOutputRenderer):
    """Compact renderer for synthetic plate generation results."""

    output_contract = SyntheticPlateGenerationResult
    unavailable_summary = "Synthetic plate generation: unavailable"

    @classmethod
    def render_payload(
        cls,
        payload: SyntheticPlateGenerationResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        if payload.errors:
            return "Synthetic plate generation: failed"
        lines = [
            f"Synthetic plate: {payload.output_dir}",
            (
                "Geometry: "
                f"grid={_dimensions_text(payload.grid_size)} "
                f"tile={_dimensions_text(payload.tile_size)} "
                f"overlap={payload.overlap_percent}% "
                f"stage_error_px={payload.stage_error_px}"
            ),
            (
                "Content: "
                f"wells={cls.sequence_text(payload.wells)} "
                f"channels={payload.wavelengths} "
                f"z={payload.z_stack_levels} "
                f"cells={payload.num_cells} "
                f"shared_fraction={payload.shared_cell_fraction}"
            ),
            (
                "Files: "
                f"images={payload.image_count} "
                f"sampled={len(payload.sampled_image_files)} "
                f"truncated={payload.truncated_image_count}"
            ),
            (
                "Metadata: "
                f"file={cls.text(payload.metadata_file_path)} "
                f"microscope={cls.text(payload.detected_source_format)} "
                f"handler={cls.text(payload.handler_class)}"
            ),
        ]
        if payload.sampled_image_files:
            lines.append("Sample images:")
            lines.extend(f"- {path}" for path in payload.sampled_image_files[:12])
        lines.append(f"Next: inspect-plate {payload.output_dir}")
        lines.append(f"Next: query-plate-files {payload.output_dir} --limit 10")
        return "\n".join(lines)


class PlateInspectionRenderer(McpDevOutputRenderer):
    """Compact renderer for plate inspection results."""

    output_contract = PlatePathInspectionResult
    unavailable_summary = "Plate inspection: unavailable"
    SAMPLE_FLAGS: ClassVar[str] = "--height 8 --width 8 --no-array-values"

    @classmethod
    def render_payload(
        cls,
        payload: PlatePathInspectionResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        return cls.inspection_text(
            payload,
            lambda image_path: f"sample-plate-image {payload.plate_path} {image_path}",
        )

    @classmethod
    def inspection_text(
        cls,
        payload: PlatePathInspectionResult,
        sample_command: Callable[[str], str],
    ) -> str:
        """Render an inspection; ``sample_command`` names the next sampling call."""
        if payload.errors:
            return "Plate inspection: failed"
        image_files = payload.image_files
        result_files = payload.result_files
        parse = payload.parse_summary
        sampled_records = image_files.sampled_records
        result_records = result_files.sampled_records
        lines = [
            f"Plate: {payload.plate_path}",
            (
                f"Status: {payload.status.value} "
                f"confidence={payload.confidence.value} "
                f"microscope={cls.text(payload.detected_source_format)}"
            ),
            (
                f"Handler: {cls.text(payload.handler_class)} "
                f"parser={cls.text(payload.parser_class)}"
            ),
            (
                f"Images: count={image_files.count} "
                f"sampled={len(sampled_records) or len(image_files.sampled_files)} "
                f"truncated={image_files.truncated_file_count}"
            ),
            (
                f"Results: count={result_files.count} "
                f"sampled={len(result_records) or len(result_files.sampled_files)} "
                f"scanned={result_files.scanned_file_count} "
                f"truncated={result_files.truncated_file_count}"
            ),
            (
                f"Parse: attempted={parse.attempted_file_count} "
                f"parsed={parse.parsed_file_count} "
                f"failed={parse.failed_file_count} "
                f"skipped={parse.skipped_file_count}"
            ),
            (
                f"Geometry: grid={_dimensions_text(payload.grid_dimensions)} "
                f"pixel_size={cls.text(payload.pixel_size)}"
            ),
        ]
        workspace = payload.workspace_preparation
        lines.append(
            f"Workspace: {workspace.operation.value} "
            f"read_only={workspace.read_only_inspection} "
            f"required_before_execution={workspace.required_before_execution}"
        )
        workflow = payload.workflow_advice
        lines.extend(
            (
                f"Routing: scope={workflow.workflow_scope.value} "
                f"ingestion={workflow.ingestion_route.value} "
                f"owner={cls.text(workflow.ingestion_owner)} "
                f"source_bindings={workflow.source_binding_role.value}",
                f"UI next: document={cls.text(workflow.ui_code_document_id)} "
                f"operation={cls.text(workflow.ui_operation)}",
                f"Advice: {workflow.message}",
                f"Knowledge query: {workflow.knowledge_query}",
            )
        )
        if payload.format_specific_handler_candidates:
            lines.append("Format-specific handler candidates:")
            lines.extend(
                cls._handler_candidate_line(candidate)
                for candidate in payload.format_specific_handler_candidates
            )
        if payload.components:
            lines.append(cls._axis_summary_line(payload.components))
            lines.append(cls._metadata_sources_line(payload.components))
            lines.append("Components:")
            lines.extend(cls._component_lines(payload.components))
        if payload.source_diagnostics:
            lines.append(f"Source diagnostics: {len(payload.source_diagnostics)}")
            lines.extend(
                f"- {cls.text(json_member(diagnostic, 'diagnostic_type'))}: "
                f"{cls.text(json_member(diagnostic, 'message'))}"
                for diagnostic in payload.source_diagnostics
            )
        modified_line = PlateFileRecordPresentation.modified_summary_line(
            "Sampled artifacts modified", (*sampled_records, *result_records)
        )
        if modified_line is not None:
            lines.append(modified_line)
        if sampled_records:
            lines.append("Sample records:")
            lines.extend(cls._image_record_lines(sampled_records))
            sample_path = cls._preferred_sample_record(sampled_records).virtual_path
            lines.append(f"Next: {sample_command(sample_path)} {cls.SAMPLE_FLAGS}")
        elif image_files.sampled_files:
            lines.append("Sample paths:")
            lines.extend(f"- {path}" for path in image_files.sampled_files)
            lines.append(
                f"Next: {sample_command(image_files.sampled_files[0])} "
                f"{cls.SAMPLE_FLAGS}"
            )
        if result_records:
            lines.append("Result records:")
            for record in result_records:
                lines.append(
                    f"- {record.relative_path} type={record.file_format}"
                    f"{PlateFileRecordPresentation.metadata_suffix(record)}"
                )
                lines.extend(ResultPreviewPresentation.lines(record.preview))
        return "\n".join(lines)

    @classmethod
    def _handler_candidate_line(cls, candidate: PlateInspectionHandlerCandidate) -> str:
        return (
            f"  - {candidate.source_format} "
            f"parser={candidate.parser_class} "
            f"recognized={candidate.recognized_file_count}/"
            f"{candidate.tested_file_count} "
            f"root={candidate.root_dir} "
            f"metadata_detected={candidate.metadata_detected} "
            f"diagnostic={cls.text(candidate.metadata_diagnostic)}"
        )

    @staticmethod
    def _image_record_lines(
        records: Sequence[PlateInspectionImageRecordSummary],
    ) -> list[str]:
        return [
            f"- {record.virtual_path}"
            + (
                f" -> {record.source_path}"
                if record.source_path
                not in {record.virtual_path, record.full_virtual_path}
                else ""
            )
            + PlateFileRecordPresentation.metadata_suffix(record)
            for record in records
        ]

    @staticmethod
    def _preferred_sample_record(
        records: Sequence[PlateInspectionImageRecordSummary],
    ) -> PlateInspectionImageRecordSummary:
        """The most recently modified record, the first one on ties."""
        modified_records = [
            (modified, -index, record)
            for index, record in enumerate(records)
            if (modified := PlateFileRecordPresentation.modified(record)) is not None
        ]
        if not modified_records:
            return records[0]
        return max(modified_records, key=lambda item: item[:2])[2]

    @classmethod
    def _component_lines(
        cls, components: Sequence[PlateInspectionComponentSummary]
    ) -> list[str]:
        return [
            f"- {component.component}: count={component.count} "
            f"source={component.source.value} "
            "values="
            f"{', '.join(cls._component_value_text(value) for value in component.values) or '<none>'} "
            f"truncated={component.truncated_value_count}"
            for component in components
        ]

    @staticmethod
    def _component_value_text(value: PlateInspectionComponentValue) -> str:
        return value.key if value.label is None else f"{value.key} ({value.label})"

    @staticmethod
    def _summary_axis_names() -> tuple[str, ...]:
        """Partition axis first, then the variable axes in declaration order."""
        family = AxisFamily.active()
        return (
            family.partition_axis().name,
            *(axis.name for axis in family.variable_axes()),
        )

    @classmethod
    def _axis_summary_line(
        cls, components: Sequence[PlateInspectionComponentSummary]
    ) -> str:
        counts = {component.component: component.count for component in components}
        sizes = " ".join(
            f"{name}={counts[name] if name in counts else '<unknown>'}"
            for name in cls._summary_axis_names()
        )
        profile = ",".join(
            (
                f"unknown-{axis.name}"
                if axis.name not in counts
                else f"multi-{axis.name}"
                if counts[axis.name] > 1
                else f"single-{axis.name}"
            )
            for axis in AxisFamily.active().variable_axes()
        )
        return f"Axis sizes: {sizes} profile={profile}"

    @classmethod
    def _metadata_sources_line(
        cls, components: Sequence[PlateInspectionComponentSummary]
    ) -> str:
        sources = {
            component.component: component.source.value for component in components
        }
        ordered_parts = [
            f"{name}={sources[name]}"
            for name in cls._summary_axis_names()
            if name in sources
        ]
        return f"Metadata sources: {', '.join(ordered_parts) or '<none>'}"


class PlateFileQueryRenderer(McpDevOutputRenderer):
    """Compact renderer for plate file query results."""

    output_contract = PlateFileQueryResult
    unavailable_summary = "Plate file query: unavailable"

    @classmethod
    def render_payload(
        cls, payload: PlateFileQueryResult, options: McpDevOutputRenderOptions
    ) -> str:
        if payload.errors:
            return "Plate file query: failed"
        records = payload.records
        lines = [
            f"Plate file query: {payload.plate_path}",
            (
                f"Result: returned={payload.returned_count} "
                f"total={payload.total_count} "
                f"offset={payload.offset} "
                f"limit={payload.limit} "
                f"truncated={payload.truncated_count}"
            ),
            (
                f"Handler: {cls.text(payload.handler_class)} "
                f"parser={cls.text(payload.parser_class)}"
            ),
        ]
        for line in (
            PlateFileRecordPresentation.modified_summary_line(
                "Returned records modified", records
            ),
            cls._stale_result_line(records),
            cls._record_root_line(payload.plate_path, records),
        ):
            if line is not None:
                lines.append(line)
        if records:
            lines.append("Records:")
            lines.extend(PlateFileRecordPresentation.query_record_lines(records))
        else:
            lines.append("Records: <none>")
        if payload.truncated_count > 0:
            lines.append(
                "Next page: rerun with "
                f"--offset {payload.offset + payload.returned_count} "
                f"--limit {payload.limit}"
            )
        result_query_line = cls._result_query_line(payload)
        if result_query_line is not None:
            lines.append(result_query_line)
        return "\n".join(lines)

    @staticmethod
    def _record_root_line(
        plate_path: str, records: Sequence[PlateFileQueryRecordSummary]
    ) -> str | None:
        if not plate_path:
            return None
        query_root = Path(plate_path)
        record_roots: list[str] = []
        for record in records:
            if not record.full_path or not record.relative_path:
                continue
            root = Path(record.full_path)
            for part in Path(record.relative_path).parts:
                if part not in ("", "."):
                    root = root.parent
            if root != query_root and str(root) not in record_roots:
                record_roots.append(str(root))
        if not record_roots:
            return None
        displayed_roots = ", ".join(record_roots[:3])
        if len(record_roots) > 3:
            displayed_roots = f"{displayed_roots}, ... (+{len(record_roots) - 3})"
        return (
            f"Record file roots: {displayed_roots} "
            "(differs from query root; inventory may expose materialized outputs)"
        )

    @staticmethod
    def _result_query_line(payload: PlateFileQueryResult) -> str | None:
        warning_codes = {warning.code for warning in payload.warnings}
        if (
            PlateInspectionIssueCode.RESULT_FILES_AVAILABLE.value not in warning_codes
            or not payload.plate_path
        ):
            return None
        microscope_option = (
            f" --source-format {payload.detected_source_format}"
            if payload.detected_source_format
            else ""
        )
        return (
            f"Next: query-plate-files {payload.plate_path}{microscope_option} "
            "--kind result --include-previews"
        )

    @staticmethod
    def _stale_result_line(
        records: Sequence[PlateFileQueryRecordSummary],
    ) -> str | None:
        def modified_values(kind: PlateFileKind) -> tuple[str, ...]:
            return tuple(
                modified
                for record in records
                if record.kind is kind
                and (modified := PlateFileRecordPresentation.modified(record))
                is not None
            )

        image_modified = modified_values(PlateFileKind.IMAGE)
        result_modified = modified_values(PlateFileKind.RESULT)
        if not image_modified or not result_modified:
            return None
        latest_image = max(image_modified)
        older_result_count = sum(
            1 for modified in result_modified if modified < latest_image
        )
        if older_result_count == 0:
            return None
        return (
            "Potential stale results: "
            f"{older_result_count} result artifact(s) are older than the latest "
            f"image record ({latest_image}); confirm they belong to the current "
            "pipeline/run before using them."
        )


class PlateFileStreamRenderer(McpDevOutputRenderer):
    """Compact renderer for plate file stream results."""

    output_contract = PlateFileStreamResult
    unavailable_summary = "Plate file stream: unavailable"

    MAX_PATH_LINES: ClassVar[int] = 8
    MAX_STATUS_LINES: ClassVar[int] = 5

    @classmethod
    def render_payload(
        cls, payload: PlateFileStreamResult, options: McpDevOutputRenderOptions
    ) -> str:
        if payload.errors:
            return "Plate file stream: failed"
        connection = payload.connection
        lines = [
            f"Plate file stream: {payload.plate_path}",
            (
                f"Viewer: {cls.text(payload.viewer_type)} "
                f"config={payload.viewer_config_key} "
                f"host={connection.host} "
                f"port={cls.text(connection.port)} "
                f"transport={cls.text(connection.transport_mode)} "
                f"persistent={connection.persistent}"
            ),
            (
                f"Files: requested={len(payload.requested_paths)} "
                f"resolved={len(payload.resolved_records)} "
                f"images={len(payload.streamed_image_paths)} "
                f"rois={len(payload.streamed_roi_paths)} "
                f"skipped={len(payload.skipped_records)}"
            ),
            (
                f"Handler: {cls.text(payload.handler_class)} "
                f"parser={cls.text(payload.parser_class)}"
            ),
        ]
        lines.extend(cls._bounded_lines("Images", payload.streamed_image_paths))
        lines.extend(cls._bounded_lines("ROIs", payload.streamed_roi_paths))
        if payload.skipped_records:
            lines.append("Skipped:")
            lines.extend(
                PlateFileRecordPresentation.query_record_lines(
                    payload.skipped_records[: cls.MAX_PATH_LINES]
                )
            )
            if len(payload.skipped_records) > cls.MAX_PATH_LINES:
                lines.append(
                    f"- ... {len(payload.skipped_records) - cls.MAX_PATH_LINES} more"
                )
        lines.extend(
            cls._bounded_lines("Status", payload.status_messages, cls.MAX_STATUS_LINES)
        )
        if connection.port is not None:
            viewer_options = cls._viewer_command_options(connection)
            lines.append("Next:")
            lines.append(
                f"- validate-viewer {viewer_options} --require-nonzero-payloads"
            )
            lines.append(f"- viewer-state {viewer_options}")
            if payload.streamed_roi_paths:
                lines.append(f"- viewer-rois {viewer_options} --limit 5")
        return "\n".join(lines)

    @classmethod
    def _bounded_lines(
        cls,
        heading: str,
        values: Sequence[str],
        limit: int | None = None,
    ) -> list[str]:
        bound = cls.MAX_PATH_LINES if limit is None else limit
        if not values:
            return []
        lines = [f"{heading}:", *(f"- {value}" for value in values[:bound])]
        if len(values) > bound:
            lines.append(f"- ... {len(values) - bound} more")
        return lines

    @classmethod
    def _viewer_command_options(cls, connection: ExecutionConnectionSpec) -> str:
        parts = [f"--port {connection.port}"]
        if connection.host not in ("", "localhost"):
            parts.append(f"--host {connection.host}")
        if connection.transport_mode is not None:
            parts.append(f"--transport-mode {cls.text(connection.transport_mode)}")
        return " ".join(parts)


class SelectedPlateRenderer(McpDevOutputRenderer):
    """Shared header of results scoped to the plate selected in the UI.

    Declares no output contract; each selected-plate result renders its nested
    plate result through that result's own renderer.
    """

    @classmethod
    def selected_plate_line(cls, payload) -> str:
        row = cls.selected_row(payload)
        return (
            "Selected plate: "
            f"{cls.text(None if row is None else row.name)} "
            f"root={cls.text(None if row is None else row.plate_root)} "
            f"target={payload.target.value}"
        )

    @classmethod
    def selected_row(cls, payload) -> UiPlateManagerRowState | None:
        """The selected PlateManager row, declared by its state DTO."""
        return (
            dataclass_from_mapping(UiPlateManagerRowState, payload.selected_plate)
            if payload.selected_plate
            else None
        )


class SelectedPlateImagesRenderer(SelectedPlateRenderer):
    """Compact renderer for selected-plate image inspection."""

    output_contract = SelectedPlateImageInspectionResult
    unavailable_summary = "Selected plate images: unavailable"

    @classmethod
    def render_payload(
        cls,
        payload: SelectedPlateImageInspectionResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        lines = [cls.selected_plate_line(payload)]
        if payload.errors:
            return "\n".join(("Selected plate images: failed", *lines))
        if payload.inspection is None:
            lines.append("Inspection: <none>")
            return "\n".join(lines)
        target_prefix = (
            ""
            if payload.target is SelectedPlateFileQueryTarget.SELECTED
            else f"--target {payload.target.value} "
        )
        lines.append(
            PlateInspectionRenderer.inspection_text(
                payload.inspection,
                lambda image_path: f"selected-plate-sample {target_prefix}{image_path}",
            )
        )
        return "\n".join(lines)


class SelectedPlateFilesRenderer(SelectedPlateRenderer):
    """Compact renderer for selected-plate file queries."""

    output_contract = SelectedPlateFileQueryResult
    unavailable_summary = "Selected plate files: unavailable"

    @classmethod
    def render_payload(
        cls,
        payload: SelectedPlateFileQueryResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        lines = [cls.selected_plate_line(payload)]
        if payload.errors:
            return "\n".join(("Selected plate files: failed", *lines))
        query = payload.query
        if query is None:
            lines.append("Query: <none>")
            return "\n".join(lines)
        lines.append(PlateFileQueryRenderer.render_payload(query, options))
        row = cls.selected_row(payload)
        if (
            payload.target is SelectedPlateFileQueryTarget.SELECTED
            and query.total_count == 0
            and row is not None
            and row.output_plate_root
            and query.plate_path == row.plate_root
        ):
            lines.append(f"Related output: {row.output_plate_root}")
            lines.append("Next: selected-plate-files --target output --kind result")
        return "\n".join(lines)


class SelectedPlateSampleRenderer(SelectedPlateRenderer):
    """Compact renderer for selected-plate image sampling."""

    output_contract = SelectedPlateImageSampleResult
    unavailable_summary = "Selected plate sample: <unavailable>"

    @classmethod
    def render_payload(
        cls,
        payload: SelectedPlateImageSampleResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        lines = [
            cls.selected_plate_line(payload),
            (
                f"Selected image: {cls.text(payload.image_path)} "
                f"auto={payload.auto_selected_image_path}"
            ),
        ]
        if payload.errors:
            return "\n".join(("Selected plate sample: failed", *lines))
        lines.append(
            "Sample: <none>"
            if payload.sample is None
            else PlateImageSampleRenderer.render_payload(payload.sample, options)
        )
        return "\n".join(lines)


class SelectedPlateStreamRenderer(SelectedPlateRenderer):
    """Compact renderer for selected-plate file streaming."""

    output_contract = SelectedPlateFileStreamResult
    unavailable_summary = "Selected plate stream: unavailable"

    @classmethod
    def render_payload(
        cls,
        payload: SelectedPlateFileStreamResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        header = cls.selected_plate_line(payload)
        if payload.errors:
            return "\n".join(("Selected plate stream: failed", header))
        if payload.stream is None:
            return "\n".join((header, "Stream: <none>"))
        return "\n".join(
            (header, PlateFileStreamRenderer.render_payload(payload.stream, options))
        )
