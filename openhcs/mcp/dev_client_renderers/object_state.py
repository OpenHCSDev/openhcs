"""ObjectState renderers for the MCP dev client."""

from __future__ import annotations

from openhcs.agent.dto.ui_bridge import (
    UiCatalogPageMetadata,
    UiObjectStateFieldFilter,
    UiObjectStateFieldHelpResult,
    UiObjectStateFieldListResult,
    UiObjectStateFieldMutationResult,
    UiObjectStateFieldProvenance,
    UiObjectStateFieldSemanticCarrier,
    UiObjectStateFieldSummary,
    UiObjectStateScopeCatalog,
    UiObjectStateScopeSummary,
    UiObjectStateValuePreview,
)
from openhcs.mcp.dev_client_rendering import (
    McpDevOutputRenderer,
    McpDevOutputRenderOptions,
)


class ObjectStatePresentation(McpDevOutputRenderer):
    """Marker and field-line vocabulary shared by every ObjectState view."""

    MARKER_LEGEND = "Markers: [*]=unsaved/dirty [_]=differs-from-defaults [-]=clean"

    @staticmethod
    def scope_mark(
        *,
        has_unsaved_changes: bool,
        dirty_field_count: int,
        has_default_overrides: bool,
        signature_diff_field_count: int,
    ) -> str:
        marks = ""
        if has_unsaved_changes or dirty_field_count:
            marks += "*"
        if has_default_overrides or signature_diff_field_count:
            marks += "_"
        return marks or "-"

    @classmethod
    def field_line(
        cls,
        field: UiObjectStateFieldSemanticCarrier,
        field_path: str,
        object_state_path_type: str,
    ) -> str:
        return (
            f"  [{cls._field_mark(field)}] {field_path}: "
            f"target={cls.short_type(object_state_path_type)} "
            f"raw={cls._preview_text(field.raw_value_preview, field.raw_value)} "
            "-> "
            f"resolved={cls._preview_text(field.resolved_value_preview, field.resolved_value)} "
            f"inherited={field.inherited_value} "
            f"provenance={cls._provenance_text(field.provenance)}"
        )

    @classmethod
    def summary_line(cls, field: UiObjectStateFieldSummary) -> str:
        return cls.field_line(
            field, field.address.field_path, field.object_state_path_type
        )

    @staticmethod
    def _field_mark(field: UiObjectStateFieldSemanticCarrier) -> str:
        marks: list[str] = []
        if field.dirty:
            marks.append("*")
        if field.signature_diff:
            marks.append("_")
        for marker in field.semantic_markers:
            if marker and marker not in marks:
                marks.append(marker)
        return "".join(marks) or "-"

    @classmethod
    def _preview_text(
        cls, preview: UiObjectStateValuePreview | None, value: object
    ) -> str:
        return cls.text(value) if preview is None else preview.text

    @classmethod
    def _provenance_text(cls, provenance: UiObjectStateFieldProvenance | None) -> str:
        if provenance is None:
            return "<none>"
        return (
            f"{cls.text(provenance.source_scope_id)}:"
            f"{cls.text(provenance.source_field_path)} "
            f"({cls.short_type(provenance.source_type)})"
        )

    @staticmethod
    def short_type(value: str | None) -> str:
        if not value:
            return "<none>"
        return value.rsplit(".", 1)[-1]


class ObjectStateScopeRenderer(ObjectStatePresentation):
    """Compact renderer for ObjectState scope catalogs."""

    output_contract = UiObjectStateScopeCatalog
    unavailable_summary = "ObjectState scopes: unavailable"

    @classmethod
    def render_payload(
        cls, payload: UiObjectStateScopeCatalog, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            "ObjectState scopes: "
            f"scopes={len(payload.scopes)} token={payload.object_state_token} "
            f"branch={payload.current_branch} "
            f"snapshot={payload.current_snapshot_index} active={payload.active}",
            cls.MARKER_LEGEND,
        ]
        if payload.scopes:
            lines.append("Scopes:")
            for scope in payload.scopes:
                lines.append(cls._scope_line(scope))
                lines.extend(f"  {cls.summary_line(field)}" for field in scope.fields)
            next_page = next(
                (
                    scope.field_page
                    for scope in payload.scopes
                    if scope.field_page is not None
                    and scope.field_page.next_offset is not None
                ),
                None,
            )
            if next_page is not None:
                lines.append(
                    "Next field page: rerun with --include-fields "
                    f"--field-offset {next_page.next_offset} --field-limit {next_page.limit}"
                )
        return "\n".join(lines)

    @classmethod
    def _scope_line(cls, scope: UiObjectStateScopeSummary) -> str:
        mark = cls.scope_mark(
            has_unsaved_changes=scope.has_unsaved_changes,
            dirty_field_count=scope.dirty_field_count,
            has_default_overrides=scope.has_default_overrides,
            signature_diff_field_count=scope.signature_diff_field_count,
        )
        line = (
            f"- [{mark}] scope={scope.identity.object_state_scope_id}: "
            f"type={scope.object_type} params={scope.parameter_count} "
            f"dirty={scope.dirty_field_count} "
            f"default_diff={scope.signature_diff_field_count} "
            f"unsaved={scope.has_unsaved_changes} "
            f"overrides={scope.has_default_overrides} "
            f"changed={cls.text(scope.last_changed_field)}"
        )
        if scope.field_page is None:
            return line
        return f"{line} {cls._field_page_text(scope.field_page)}"

    @classmethod
    def _field_page_text(cls, page: UiCatalogPageMetadata) -> str:
        text = f"fields={page.returned_count}/{cls.text(page.total_count)}"
        if page.next_offset is not None:
            text += f" next={page.next_offset}"
        return text


class ObjectStateFieldRenderer(ObjectStatePresentation):
    """Compact renderer for ObjectState field-list query results."""

    output_contract = UiObjectStateFieldListResult
    unavailable_summary = "ObjectState fields: unavailable"

    @classmethod
    def render_payload(
        cls, payload: UiObjectStateFieldListResult, options: McpDevOutputRenderOptions
    ) -> str:
        next_text = (
            "" if payload.next_offset is None else f" next={payload.next_offset}"
        )
        lines = [
            "ObjectState fields: "
            f"scopes={payload.matched_scope_count} "
            f"fields={payload.matched_field_count} "
            f"returned={payload.returned_field_count} offset={payload.field_offset} "
            f"limit={payload.field_limit}{next_text} "
            f"truncated={payload.truncated} token={payload.object_state_token} "
            f"branch={payload.current_branch} "
            f"snapshot={payload.current_snapshot_index}",
            cls.MARKER_LEGEND,
        ]
        fields = tuple(field for scope in payload.scopes for field in scope.fields)
        if fields:
            lines.append(cls._semantic_summary(fields))
        lines.extend(cls._filter_lines(payload))
        if payload.scopes:
            lines.append("Scopes:")
            for scope in payload.scopes:
                mark = cls.scope_mark(
                    has_unsaved_changes=scope.has_unsaved_changes,
                    dirty_field_count=scope.dirty_field_count,
                    has_default_overrides=scope.has_default_overrides,
                    signature_diff_field_count=scope.signature_diff_field_count,
                )
                lines.append(
                    f"Scope [{mark}] scope={scope.scope_id}: "
                    f"type={scope.object_type} dirty={scope.dirty_field_count} "
                    f"default_diff={scope.signature_diff_field_count} "
                    f"unsaved={scope.has_unsaved_changes} "
                    f"overrides={scope.has_default_overrides}"
                )
                lines.extend(
                    cls.field_line(field, field.field_path, field.object_state_path_type)
                    for field in scope.fields
                )
        return "\n".join(lines)

    @staticmethod
    def _semantic_summary(fields: tuple[UiObjectStateFieldSemanticCarrier, ...]) -> str:
        raw_none_resolved = sum(
            1
            for field in fields
            if field.raw_value_is_none and not field.resolved_value_is_none
        )
        resolved_none_raw = sum(
            1
            for field in fields
            if not field.raw_value_is_none and field.resolved_value_is_none
        )
        semantic = sum(
            1
            for field in fields
            if field.dirty
            or field.signature_diff
            or field.inherited_value
            or field.raw_value_is_none is not field.resolved_value_is_none
        )
        return (
            "Returned semantics: "
            f"dirty={sum(1 for field in fields if field.dirty)} "
            f"default_diff={sum(1 for field in fields if field.signature_diff)} "
            f"inherited={sum(1 for field in fields if field.inherited_value)} "
            f"raw_none_resolved={raw_none_resolved} "
            f"resolved_none_raw={resolved_none_raw} "
            f"plain={len(fields) - semantic}"
        )

    @staticmethod
    def _filter_lines(payload: UiObjectStateFieldListResult) -> tuple[str, ...]:
        filters: list[str] = []
        if payload.requested_scope_ids:
            filters.append("scope_ids=" + ",".join(payload.requested_scope_ids))
        if payload.field_paths:
            filters.append("field_paths=" + ",".join(payload.field_paths))
        if payload.field_path_contains:
            filters.append("contains=" + ",".join(payload.field_path_contains))
        if payload.field_filter != UiObjectStateFieldFilter.ALL.value:
            filters.append(f"field_filter={payload.field_filter}")
        if payload.include_container_fields:
            filters.append("include_container_fields=True")
        return ("Filters: " + " ".join(filters),) if filters else ()


class ObjectStateFieldHelpRenderer(ObjectStatePresentation):
    """Compact renderer for one ObjectState field help result."""

    output_contract = UiObjectStateFieldHelpResult
    unavailable_summary = "ObjectState field help: unavailable"

    MAX_TARGET_SUMMARY_CHARS = 220

    @classmethod
    def render_payload(
        cls, payload: UiObjectStateFieldHelpResult, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            "ObjectState field help: "
            f"scope={payload.address.object_state_scope_id} "
            f"field={payload.address.field_path}",
            "Target: "
            f"object={cls.short_type(payload.object_type)} "
            f"help_target={cls.short_type(payload.help_target_type)} "
            f"parameter={cls.text(payload.parameter_name)}",
        ]
        if payload.field is not None:
            lines.append("Field:")
            lines.append(cls.summary_line(payload.field))
        if payload.target_summary:
            lines.append(
                f"Target summary: {cls._compact_target_summary(payload.target_summary)}"
            )
        if payload.summary:
            lines.append(f"Summary: {payload.summary}")
        if payload.description:
            lines.append("Description:")
            lines.append(payload.description)
        if payload.description_truncated:
            lines.append(
                "Description truncated; rerun with a larger max_description_chars."
            )
        return "\n".join(lines)

    @classmethod
    def _compact_target_summary(cls, target_summary: str) -> str:
        compact = " ".join(target_summary.split())
        if len(compact) <= cls.MAX_TARGET_SUMMARY_CHARS:
            return compact
        return f"{compact[: cls.MAX_TARGET_SUMMARY_CHARS - 3]}..."


class ObjectStateFieldMutationRenderer(ObjectStatePresentation):
    """Compact renderer for one ObjectState field update/reset result."""

    output_contract = UiObjectStateFieldMutationResult
    unavailable_summary = "ObjectState field mutation: unavailable"

    @classmethod
    def render_payload(
        cls,
        payload: UiObjectStateFieldMutationResult,
        options: McpDevOutputRenderOptions,
    ) -> str:
        lines = [
            "ObjectState field mutation: "
            f"scope={payload.address.object_state_scope_id} "
            f"field={payload.address.field_path} "
            f"mutated={payload.mutated} reset={payload.reset}",
            "Receipt: "
            f"accepted={payload.receipt.accepted} "
            f"operation={cls.text(payload.receipt.bridge_operation_id)}",
        ]
        if payload.before is not None:
            lines.append("Before:")
            lines.append(cls.summary_line(payload.before))
        if payload.after is not None:
            lines.append("After:")
            lines.append(cls.summary_line(payload.after))
        return "\n".join(lines)
