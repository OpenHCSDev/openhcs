"""UI bridge renderers for the MCP dev client."""

from __future__ import annotations

from abc import ABC, abstractmethod
from typing import ClassVar

from python_introspect import dataclass_from_mapping

from openhcs.agent.dto.session import DatasetRowState, PipelineStepState
from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import AgentWarning
from openhcs.agent.dto.mcp import McpServerHealthResult
from openhcs.agent.dto.ui_bridge import (
    QT_TOP_LEVEL_WINDOW_KIND,
    UiActionCatalog,
    UiActionInvokeResult,
    UiActionSummary,
    UiBridgeCatalog,
    UiBridgeStatus,
    UiCodeDocument,
    UiCodeDocumentApplyResult,
    UiCodeDocumentCatalog,
    UiCodeDocumentSummary,
    UiCodeDocumentValidationResult,
    UiDebugActionState,
    UiDebugRuntimeFrameState,
    UiLiveOverviewSection,
    UiLiveOverviewState,
    UiPipelineDebugSessionState,
    UiPipelineEditorState,
    UiPlateManagerState,
    UiSelectedPlateWorkflowResult,
    UiSnapshotRef,
    UiStateSurfaceCatalog,
    UiStateSurfaceDocument,
    UiStateSurfaceEnvelope,
    UiStateSurfaceSummary,
    UiWidgetActionInvokeResult,
    UiWidgetActionSummary,
    UiWidgetTreeNode,
    UiWidgetTreeResult,
    UiWindowCatalog,
    UiWindowSummary,
)
from openhcs.agent.ui_bridge_identities import (
    MainWindowWidgetIdentity,
    PipelineDebugSessionStateSurfaceIdentityDeclaration,
    PipelineEditorStateSurfaceIdentityDeclaration,
    PlateManagerStateSurfaceIdentityDeclaration,
    UiLiveOverviewStateSurfaceIdentityDeclaration,
    UiStateSurfaceIdentityDeclarationBase,
)
from openhcs.mcp.dev_client_rendering import (
    CatalogRenderOptions,
    CodeDocumentRenderOptions,
    McpDevOutputRenderer,
    McpDevOutputRenderOptions,
    UiActionCatalogRenderOptions,
    WidgetTreeRenderOptions,
)


class UiBridgeStatusRenderer(McpDevOutputRenderer):
    """Compact renderer for live UI bridge status."""

    output_contract = UiBridgeStatus
    unavailable_summary = "UI bridge: unavailable"

    @classmethod
    def render_payload(
        cls, payload: UiBridgeStatus, options: McpDevOutputRenderOptions
    ) -> str:
        pid = payload.descriptors[0].pid if payload.descriptors else None
        connection = payload.connection
        return "\n".join(
            (
                f"UI bridge: reachable={payload.reachable} "
                f"descriptor={cls.text(payload.descriptor_status)}",
                f"Instance: {cls.text(payload.bridge_instance_id)} pid={cls.text(pid)}",
                f"Connection: {cls.text(connection.transport_mode)} "
                f"{connection.host}:{cls.text(connection.port)}",
                f"Descriptor: {cls.text(payload.descriptor_file_path)}",
                f"Capabilities: {len(payload.supported_operations)} operations, "
                f"{len(payload.bridge_features)} features",
            )
        )


class UiWindowCatalogRenderer(McpDevOutputRenderer):
    """Compact renderer for UI window catalogs."""

    output_contract = UiWindowCatalog
    unavailable_summary = "Windows: unavailable"

    @classmethod
    def render_payload(
        cls, payload: UiWindowCatalog, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [f"Windows: {len(payload.windows)}"]
        attention_windows = tuple(
            window for window in payload.windows if cls._needs_attention(window)
        )
        if attention_windows:
            lines.append(
                f"Attention: {len(attention_windows)} visible top-level window(s): "
                + ", ".join(
                    f"{window.window_id} title={cls.quoted(window.title)}"
                    for window in attention_windows
                )
            )
        lines.extend(
            f"- {window.window_id} [{window.window_kind}] visible={window.visible} "
            f"dirty={window.dirty} diff={window.signature_diff} "
            f"title={cls.quoted(window.title)}"
            for window in payload.windows
        )
        return "\n".join(lines)

    @staticmethod
    def _needs_attention(window: UiWindowSummary) -> bool:
        """A visible stray Qt top-level window other than the main window."""
        return (
            window.visible
            and window.window_kind == QT_TOP_LEVEL_WINDOW_KIND
            and window.title != MainWindowWidgetIdentity.require_title()
        )


class UiSmokeRenderer:
    """Compact presentation of the multi-tool ``ui-smoke`` command."""

    @classmethod
    def render(cls, response) -> str:
        from openhcs.mcp.dev_client_core import McpDevToolBatchResponse
        from openhcs.mcp.dev_client_rendering import diagnostic_lines

        decoded = McpDevToolBatchResponse.for_rendering(response)
        if decoded.errors:
            return "\n".join(
                ("UI smoke: unavailable", *diagnostic_lines(decoded.errors))
            )
        mcp_errors = sum(1 for result in decoded.results if result.mcp_error)
        health: McpServerHealthResult | None = decoded.payload_for(
            agent_capabilities.health_check
        )
        status: UiBridgeStatus | None = decoded.payload_for(
            agent_capabilities.ui_bridge_status
        )
        bridges: UiBridgeCatalog | None = decoded.payload_for(
            agent_capabilities.ui_list_bridges
        )
        windows: UiWindowCatalog | None = decoded.payload_for(
            agent_capabilities.ui_list_windows
        )
        options = McpDevOutputRenderOptions()
        return "\n".join(
            (
                f"UI smoke: results={len(decoded.results)} mcp_errors={mcp_errors}",
                "Health: missing"
                if health is None
                else f"Health: status={health.status} "
                f"restart_required={health.restart_required} "
                f"stale_paths={len(health.stale_source_paths)}",
                UiBridgeStatusRenderer.unavailable_summary
                if status is None
                else McpDevOutputRenderer.render_payload_value(status, options),
                "Bridges: missing"
                if bridges is None
                else f"Bridges: live={len(bridges.bridges)} errors={len(bridges.errors)}",
                UiWindowCatalogRenderer.unavailable_summary
                if windows is None
                else McpDevOutputRenderer.render_payload_value(windows, options),
                *McpDevOutputRenderer.diagnostic_lines(decoded.diagnostic_errors()),
            )
        )


class UiStateSurfaceCatalogRenderer(McpDevOutputRenderer):
    """Compact renderer for UI state-surface catalogs."""

    output_contract = UiStateSurfaceCatalog
    render_options_type = CatalogRenderOptions

    @classmethod
    def render_payload(
        cls, payload: UiStateSurfaceCatalog, options: CatalogRenderOptions
    ) -> str:
        surfaces, visible = options.select(payload.surfaces, cls._surface_line)
        lines = [
            f"State surfaces: count={len(payload.surfaces)} matched={len(surfaces)} "
            f"shown={len(visible)}",
            *options.filter_lines(),
        ]
        if visible:
            lines.append("Surfaces:")
            lines.extend(cls._surface_line(surface) for surface in visible)
        if len(visible) < len(surfaces):
            lines.append(f"...<truncated {len(surfaces) - len(visible)} surfaces>")
        return "\n".join(lines)

    @classmethod
    def _surface_line(cls, surface: UiStateSurfaceSummary) -> str:
        return (
            f"- {surface.surface_id}: widget={surface.widget_id} "
            f"readable={surface.readable} "
            f"selection={surface.current_selection_count}/{surface.total_scope_count} "
            f"modes={cls.sequence_text(surface.supported_selection_modes)} "
            f"title={cls.quoted(surface.title)}"
        )


class UiStateSurfaceStateRenderer(McpDevOutputRenderer):
    """Presentation of one state surface's declared state record.

    A member declares the surface identity it presents and, as its
    ``output_contract``, the state DTO that surface's document carries.
    """

    surface_identity: ClassVar[type[UiStateSurfaceIdentityDeclarationBase]]

    @classmethod
    def for_surface_id(cls, surface_id: str) -> type["UiStateSurfaceStateRenderer"] | None:
        return next(
            (
                renderer
                for renderer in McpDevOutputRenderer.__registry__.values()
                if issubclass(renderer, cls)
                and renderer.surface_identity.value == surface_id
            ),
            None,
        )

    @classmethod
    def state_from_document(cls, document: UiStateSurfaceDocument):
        return dataclass_from_mapping(cls.output_contract, document.payload)

    @classmethod
    def revision_lines(cls, state: UiStateSurfaceEnvelope) -> tuple[str, ...]:
        lines = [f"Revision: {cls.text(state.current_revision_token)}"]
        lines.extend(
            cls.optional_lines(
                state.current_snapshot,
                lambda snapshot: (
                    f"Snapshot: {snapshot.index} {cls.quoted(snapshot.label)}",
                ),
            )
        )
        return tuple(lines)


class UiStateSurfaceRenderer(McpDevOutputRenderer):
    """State-surface documents, presented by the surface's state renderer."""

    output_contract = UiStateSurfaceDocument

    @classmethod
    def render_payload(
        cls, payload: UiStateSurfaceDocument, options: McpDevOutputRenderOptions
    ) -> str:
        summary = payload.summary
        state_renderer = UiStateSurfaceStateRenderer.for_surface_id(summary.surface_id)
        if state_renderer is not None:
            return state_renderer.render_payload(
                state_renderer.state_from_document(payload), options
            )
        lines = [
            f"Surface: {summary.surface_id}",
            f"Title: {summary.title}",
            f"Readable: {summary.readable}",
            f"Selection: {cls.text(payload.selection_mode)}",
            f"Revision: {cls.text(payload.current_revision_token)}",
        ]
        if not summary.readable:
            lines.append("Next: state-surfaces")
        return "\n".join(lines)


class UiLiveOverviewStateSurfaceRenderer(UiStateSurfaceStateRenderer):
    """Compact renderer for the live UI overview surface."""

    surface_identity = UiLiveOverviewStateSurfaceIdentityDeclaration
    output_contract = UiLiveOverviewState

    @classmethod
    def render_payload(
        cls, payload: UiLiveOverviewState, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"UI live overview: sections={len(payload.sections)}",
            f"Revision: {cls.text(payload.current_revision_token)}",
        ]
        for section in payload.sections:
            lines.extend(cls._section_lines(section))
        return "\n".join(lines)

    @classmethod
    def _section_lines(cls, section: UiLiveOverviewSection) -> list[str]:
        metric_text = " ".join(
            f"{metric.label}={metric.value}" for metric in section.metrics
        )
        lines = [f"{section.title}: {section.summary} {metric_text}".rstrip()]
        for item in section.items:
            parts = [f"severity={item.severity}"]
            for label, value in (
                ("status", item.status),
                ("detail", item.detail),
                ("surface", item.source_surface_id),
                ("window", item.source_window_id),
            ):
                parts.extend(cls.optional_lines(value, lambda text: (f"{label}={text}",)))
            lines.append(f"- {item.label}: " + " ".join(parts))
        return lines


class PlateManagerStateSurfaceRenderer(UiStateSurfaceStateRenderer):
    """Compact renderer for PlateManager state-surface rows."""

    surface_identity = PlateManagerStateSurfaceIdentityDeclaration
    output_contract = UiPlateManagerState

    @classmethod
    def render_payload(
        cls, payload: UiPlateManagerState, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"Plate manager: rows={len(payload.rows)} "
            f"selected={payload.summary.current_selection_count} "
            f"manager={payload.manager_execution_state}",
            *cls.revision_lines(payload),
        ]
        if payload.rows:
            lines.append("Rows:")
            lines.extend(cls.row_lines(payload.rows))
        return "\n".join(lines)

    @classmethod
    def row_lines(cls, rows: tuple[DatasetRowState, ...]) -> list[str]:
        """The one presentation of a plate-manager row, shared by workflow waits."""
        lines: list[str] = []
        for row in rows:
            parts = [
                f"state={cls.text(row.orchestrator_state)}",
                f"status={cls.text(row.status_prefix or None)}",
                f"init={row.initialized}",
                f"compiled={row.compiled}",
                f"active={row.execution_active}",
                f"terminal={cls.text(row.terminal_status)}",
                f"selected={row.selected}",
            ]
            for label, value in (
                ("root", row.root),
                ("output", row.output_root),
                ("source", row.source_root),
            ):
                parts.extend(cls.optional_lines(value, lambda text: (f"{label}={text}",)))
            lines.append(f"- {row.name}: " + ", ".join(parts))
        return lines


class PipelineEditorStateSurfaceRenderer(UiStateSurfaceStateRenderer):
    """Compact renderer for PipelineEditor state-surface step rows."""

    surface_identity = PipelineEditorStateSurfaceIdentityDeclaration
    output_contract = UiPipelineEditorState

    @classmethod
    def render_payload(
        cls, payload: UiPipelineEditorState, options: McpDevOutputRenderOptions
    ) -> str:
        summary = payload.summary
        lines = [
            f"Pipeline editor: steps={len(payload.steps)} "
            f"selected={summary.current_selection_count}/{summary.total_scope_count} "
            f"plate={cls.text(payload.current_plate_scope_id)} "
            f"pipeline={cls.text(payload.pipeline_scope_id)}",
            *cls.revision_lines(payload),
        ]
        if payload.selected_scope_ids:
            lines.append(
                f"Selected scopes: {cls.sequence_text(payload.selected_scope_ids)}"
            )
        if payload.steps:
            lines.append("Steps:")
            lines.extend(cls._step_line(step) for step in payload.steps)
        return "\n".join(lines)

    @classmethod
    def _step_line(cls, step: PipelineStepState) -> str:
        parts = [
            f"enabled={step.enabled}",
            f"selected={step.selected}",
            f"funcs={cls.sequence_text(step.function_names)}",
        ]
        if step.function_ids:
            parts.append(f"ids={','.join(step.function_ids)}")
        if step.debug_pause:
            parts.append("debug_pause=True")
        parts.extend(
            cls.optional_lines(step.step_scope_id, lambda scope: (f"scope={scope}",))
        )
        markers = ("*" if step.dirty else "") + ("_" if step.default_diff else "")
        marker_text = f"[{markers}] " if markers else ""
        return f"- {step.index}. {marker_text}{step.name}: " + ", ".join(parts)


class PipelineDebugSessionStateSurfaceRenderer(UiStateSurfaceStateRenderer):
    """Compact renderer for PipelineEditor debug-session state."""

    surface_identity = PipelineDebugSessionStateSurfaceIdentityDeclaration
    output_contract = UiPipelineDebugSessionState

    @classmethod
    def render_payload(
        cls, payload: UiPipelineDebugSessionState, options: McpDevOutputRenderOptions
    ) -> str:
        text = cls.text
        lines = [
            f"Pipeline debug: phase={payload.phase} "
            f"plate={text(payload.current_plate_scope_id)} "
            f"pipeline={text(payload.pipeline_scope_id)} "
            f"manager={payload.manager_execution_state}",
            f"Target: initialized={payload.initialized} compiled={payload.compiled} "
            f"terminal={text(payload.terminal_status)}",
            f"Session: id={text(payload.active_session_id)} "
            f"execution={text(payload.execution_id)} axis={text(payload.axis_id)} "
            f"source_group={text(payload.selected_source_group)}",
            f"Revision: {text(payload.current_revision_token)}",
        ]
        lines.extend(
            cls.optional_lines(
                payload.cursor,
                lambda cursor: (
                    f"Cursor: step={cursor.step_index} "
                    f"scope={text(cursor.step_scope_id)} group={text(cursor.group_key)} "
                    f"invocation={text(cursor.invocation_key)} dirty={cursor.dirty}",
                ),
            )
        )
        lines.extend(
            cls.optional_lines(
                payload.current_frame,
                lambda frame: (cls._frame_line("Current frame", frame),),
            )
        )
        if payload.last_frame != payload.current_frame:
            lines.extend(
                cls.optional_lines(
                    payload.last_frame,
                    lambda frame: (cls._frame_line("Last frame", frame),),
                )
            )
        if payload.actions:
            lines.append("Actions:")
            lines.extend(cls._action_line(action) for action in payload.actions)
        return "\n".join(lines)

    @classmethod
    def _frame_line(cls, label: str, frame: UiDebugRuntimeFrameState) -> str:
        return (
            f"{label}: event={frame.event_type} step={frame.step_name} "
            f"callable={cls.text(frame.callable_name)} "
            f"axis={frame.progress_identity.axis_id} "
            f"snapshot={cls.text(frame.snapshot_id)} "
            f"invocation={cls.text(frame.cursor.invocation_key)}"
        )

    @classmethod
    def _action_line(cls, action: UiDebugActionState) -> str:
        disabled = (
            ""
            if action.disabled_error is None
            else f" disabled={action.disabled_error.code}"
        )
        return (
            f"- {action.action_id}: enabled={action.enabled} "
            f"placement={action.placement} title={cls.quoted(action.label)}{disabled}"
        )


class WidgetTreeOutlineRenderer(McpDevOutputRenderer):
    """Human-readable outline of a widget tree."""

    output_contract = UiWidgetTreeResult
    render_options_type = WidgetTreeRenderOptions
    MAX_LABEL_CHARS = 96
    TECHNICAL_WIDGET_CLASSES = frozenset({"QHeaderView", "QScrollBar", "QSplitterHandle"})
    TECHNICAL_OBJECT_NAME_PREFIX = "qt_scrollarea_"

    @classmethod
    def render_payload(
        cls, payload: UiWidgetTreeResult, options: WidgetTreeRenderOptions
    ) -> str:
        lines: list[str] = []
        lines.extend(cls.optional_lines(payload.summary, cls._summary_lines))
        root = payload.root
        if root is None:
            lines.append("Tree: <not returned; use --include-tree or outline mode>")
        else:
            if options.outline_root_class is not None:
                root = cls._first_node_with_class(root, options.outline_root_class)
                if root is None:
                    lines.append(
                        f'Tree: <no node with class "{options.outline_root_class}">'
                    )
                    return "\n".join(lines)
            if lines:
                lines.append("")
            lines.append("Tree:")
            actions = {action.path_id: action for action in payload.actionable_widgets}
            lines.extend(cls._node_lines(root, "  ", options, actions))
        if payload.tree_truncated:
            lines.extend(("", "Tree truncated by max depth/node limits."))
        if payload.actionable_widgets_truncated:
            lines.append("Actionable widget list truncated by max node limits.")
        return "\n".join(lines)

    @classmethod
    def _first_node_with_class(
        cls, node: UiWidgetTreeNode, class_name: str
    ) -> UiWidgetTreeNode | None:
        if node.class_name == class_name:
            return node
        return next(
            (
                match
                for child in node.children
                if (match := cls._first_node_with_class(child, class_name)) is not None
            ),
            None,
        )

    @classmethod
    def _summary_lines(cls, summary: UiWindowSummary) -> list[str]:
        status_parts = [
            f"dirty={summary.dirty}",
            f"dirty_fields={summary.dirty_field_count}",
            f"default_diff={summary.signature_diff}",
            f"default_diff_fields={summary.signature_diff_field_count}",
        ]
        if summary.semantic_markers:
            status_parts.append("markers=" + ",".join(summary.semantic_markers))
        return [f"Window: {summary.title}", "Status: " + " ".join(status_parts)]

    @classmethod
    def _node_lines(
        cls,
        node: UiWidgetTreeNode,
        prefix: str,
        options: WidgetTreeRenderOptions,
        actions: dict[str, UiWidgetActionSummary],
    ) -> list[str]:
        lines = [f"{prefix}{cls._node_label(node, actions)}"]
        for child in node.children:
            if not cls._is_hidden_technical_node(child, options):
                lines.extend(cls._node_lines(child, f"{prefix}  ", options, actions))
        return lines

    @classmethod
    def _is_hidden_technical_node(
        cls, node: UiWidgetTreeNode, options: WidgetTreeRenderOptions
    ) -> bool:
        if options.include_technical_widgets:
            return False
        return (
            node.class_name in cls.TECHNICAL_WIDGET_CLASSES
            or not node.visible
            or node.object_name.startswith(cls.TECHNICAL_OBJECT_NAME_PREFIX)
        )

    @classmethod
    def _node_label(
        cls, node: UiWidgetTreeNode, actions: dict[str, UiWidgetActionSummary]
    ) -> str:
        parts = [part for part in (node.class_name,) if part]
        if node.object_name:
            parts.append(f"#{node.object_name}")
        addressable = node.actionable or (
            node.visible and any(node.action_kinds)
        )
        path_id = node.path_id if addressable else ""
        action = actions[path_id] if path_id in actions else None
        semantic_parts = [] if action is None else cls._semantic_parts(action)
        if not semantic_parts:
            label = next((text for text in (node.text, node.title) if text), None)
            if label:
                parts.append(f'"{cls._compact_text(label)}"')
            if node.current_text:
                parts.append(f'current="{cls._compact_text(node.current_text)}"')
        if path_id:
            parts.append(f"path={path_id}")
            parts.extend(semantic_parts)
            parts.extend(cls._interaction_state_parts(node))
        return " ".join(parts)

    @staticmethod
    def _interaction_state_parts(node: UiWidgetTreeNode) -> list[str]:
        if node.actionable:
            return []
        parts: list[str] = []
        if not node.visible:
            parts.append("hidden")
        if not node.enabled:
            parts.append("disabled")
        elif not node.clickable:
            parts.append("not-clickable")
        return parts

    @classmethod
    def _semantic_parts(cls, action: UiWidgetActionSummary) -> list[str]:
        scope_id = action.object_state_scope_id
        markers = "".join(action.semantic_markers) or (
            ("*" if action.dirty else "") + ("_" if action.signature_diff else "")
        )
        if not scope_id and not markers:
            return []
        parts = [f"[{markers or '-'}]"]
        if scope_id:
            parts.append(f"scope={cls._compact_text(scope_id)}")
        if action.field_path:
            parts.append(f"field={cls._compact_text(action.field_path)}")
        return parts

    @classmethod
    def _compact_text(cls, text: str) -> str:
        compact = " ".join(text.split())
        if len(compact) <= cls.MAX_LABEL_CHARS:
            return compact
        return f"{compact[: cls.MAX_LABEL_CHARS - 3]}..."


class CodeDocumentCatalogRenderer(McpDevOutputRenderer):
    """Compact renderer for UI code-document catalogs."""

    output_contract = UiCodeDocumentCatalog
    render_options_type = CatalogRenderOptions

    @classmethod
    def render_payload(
        cls, payload: UiCodeDocumentCatalog, options: CatalogRenderOptions
    ) -> str:
        documents, visible = options.select(payload.documents, cls._document_line)
        lines = [
            f"Code documents: count={len(payload.documents)} "
            f"matched={len(documents)} shown={len(visible)}",
            *options.filter_lines(),
        ]
        if visible:
            lines.append("Documents:")
            lines.extend(cls._document_line(document) for document in visible)
        if len(visible) < len(documents):
            lines.append(f"...<truncated {len(documents) - len(visible)} documents>")
        return "\n".join(lines)

    @classmethod
    def _document_line(cls, document: UiCodeDocumentSummary) -> str:
        return (
            f"- {document.document_id}: widget={document.widget_id} "
            f"readable={document.readable} writable={document.writable} "
            f"selection={document.current_selection_count}/{document.total_scope_count} "
            f"modes={cls.sequence_text(document.supported_selection_modes)} "
            f"title={cls.quoted(document.title)}"
        )


class CodeDocumentRenderer(McpDevOutputRenderer):
    """Compact renderer for one UI code document."""

    output_contract = UiCodeDocument
    render_options_type = CodeDocumentRenderOptions

    @classmethod
    def render_payload(
        cls, payload: UiCodeDocument, options: CodeDocumentRenderOptions
    ) -> str:
        summary = payload.summary
        snapshot = payload.current_snapshot
        snapshot_text = (
            "<none>@<none> head=<none>"
            if snapshot is None
            else f"{snapshot.branch}@{snapshot.index} head={snapshot.is_head}"
        )
        lines = [
            f"Code document: id={summary.document_id} title={cls.quoted(summary.title)} "
            f"widget={summary.widget_id} writable={summary.writable} "
            f"mode={cls.text(payload.selection_mode)} "
            f"scopes={cls.sequence_text(payload.selected_scope_ids)}",
            f"Revision: token={cls.text(payload.current_revision_token)} "
            f"sha256={payload.sha256} bytes={payload.size_bytes} "
            f"snapshot={snapshot_text}",
        ]
        if options.include_source:
            lines.extend(("Source:", options.source_text(payload.source)))
        return "\n".join(lines)


class CodeDocumentValidationRenderer(McpDevOutputRenderer):
    """Compact renderer for UI code-document validation results."""

    output_contract = UiCodeDocumentValidationResult

    @classmethod
    def render_payload(
        cls, payload: UiCodeDocumentValidationResult, options: McpDevOutputRenderOptions
    ) -> str:
        return (
            f"Code document validation: id={payload.document_id} valid={payload.valid} "
            f"normalized_scopes={cls.sequence_text(payload.normalized_scope_ids)}"
        )


class UiMutationRenderer(McpDevOutputRenderer):
    """Shared presentation of a bridge mutation's request acknowledgement."""

    @classmethod
    def acknowledgement_line(cls, acknowledgement) -> str:
        return (
            f"Receipt: accepted={acknowledgement.accepted} "
            f"request_token={cls.text(acknowledgement.request_token.value)} "
            f"bridge_operation={cls.text(acknowledgement.bridge_operation_id)}"
        )


class CodeDocumentApplyRenderer(UiMutationRenderer):
    """Compact renderer for UI code-document apply results."""

    output_contract = UiCodeDocumentApplyResult

    @classmethod
    def render_payload(
        cls, payload: UiCodeDocumentApplyResult, options: McpDevOutputRenderOptions
    ) -> str:
        return "\n".join(
            (
                f"Code document apply: id={payload.document_id} "
                f"applied={payload.applied} outcome={payload.outcome} "
                f"operation={cls.text(payload.operation_id)}",
                f"Revision: base={payload.base_revision_token} "
                f"current={cls.text(payload.current_revision_token)} "
                f"new={cls.text(payload.new_revision_token)}",
                cls.acknowledgement_line(payload.receipt),
                f"Snapshots: current={cls._snapshot_text(payload.current_snapshot)} "
                f"undo={cls._snapshot_text(payload.undo_snapshot)}",
            )
        )

    @staticmethod
    def _snapshot_text(snapshot: UiSnapshotRef | None) -> str:
        if snapshot is None:
            return "<none>"
        return f"{snapshot.branch}@{snapshot.index}:{snapshot.snapshot_id}"


class UiActionCatalogRenderer(McpDevOutputRenderer):
    """Compact renderer for semantic UI action catalogs."""

    output_contract = UiActionCatalog
    render_options_type = UiActionCatalogRenderOptions

    @classmethod
    def render_payload(
        cls, payload: UiActionCatalog, options: UiActionCatalogRenderOptions
    ) -> str:
        actions = cls._selected_actions(payload, options)
        header = f"UI actions: count={len(actions)}"
        if options.widget_id is not None:
            header = f"{header} widget={options.widget_id}"
        lines = [header]
        if actions:
            lines.append("Actions:")
            lines.extend(cls._action_line(action) for action in actions)
            hint_lines = cls._disabled_hint_lines(actions)
            if hint_lines:
                lines.append("Disabled hints:")
                lines.extend(hint_lines)
        elif options.widget_id is not None:
            lines.append(
                "No semantic actions matched this widget. "
                f"Use widget-tree {options.widget_id} for generic widget action paths."
            )
        return "\n".join(lines)

    @staticmethod
    def _selected_actions(
        payload: UiActionCatalog, options: UiActionCatalogRenderOptions
    ) -> tuple[UiActionSummary, ...]:
        if options.widget_id is None:
            return payload.actions
        return tuple(
            action
            for action in payload.actions
            if action.identity.widget_id == options.widget_id
        )

    @classmethod
    def presented_warnings(
        cls, payload: UiActionCatalog, options: UiActionCatalogRenderOptions
    ) -> tuple[AgentWarning, ...]:
        """For one widget, only the warnings that mention it or its actions."""
        warnings = super().presented_warnings(payload, options)
        if options.widget_id is None:
            return warnings
        terms = {options.widget_id.lower()}
        for action in cls._selected_actions(payload, options):
            terms.update(
                (action.identity.widget_id.lower(), action.identity.action_id.lower())
            )
        terms.discard("")
        return tuple(
            warning
            for warning in warnings
            if any(
                term in f"{warning.code} {warning.message} {warning.hint or ''}".lower()
                for term in terms
            )
        )

    @classmethod
    def _disabled_hint_lines(cls, actions: tuple[UiActionSummary, ...]) -> list[str]:
        action_keys_by_hint: dict[str, list[str]] = {}
        for action in actions:
            if action.disabled_error is not None and action.disabled_error.hint:
                action_keys_by_hint.setdefault(action.disabled_error.hint, []).append(
                    f"{action.identity.widget_id}/{action.identity.action_id}"
                )
        return [
            f"- {','.join(action_keys)}: {cls.quoted(hint)}"
            for hint, action_keys in action_keys_by_hint.items()
        ]

    @classmethod
    def _action_line(cls, action: UiActionSummary) -> str:
        disabled = action.disabled_error
        disabled_text = (
            "" if disabled is None else f" disabled={disabled.code}:{disabled.message}"
        )
        return (
            f"- {action.identity.widget_id}/{action.identity.action_id}: "
            f"title={cls.quoted(action.title)} enabled={action.enabled} "
            f"confirm={action.confirmation_required} mode={action.invocation_mode} "
            f"selection={action.current_selection_count} "
            f"targets={cls.sequence_text(action.target_scope_ids)} "
            f"selection_rev={cls.text(action.selection_revision_token)} "
            f"effects={cls.sequence_text(action.side_effects)} "
            f"selection_mode={cls.text(action.selection_mode)} "
            f"surfaces={cls.sequence_text(action.related_state_surface_ids)}"
            f"{disabled_text}"
        )


class UiActionResultRenderer(UiMutationRenderer, ABC):
    """Shared presentation of the action owned by each declared result."""

    unavailable_summary = "UI action: <unavailable>"

    @classmethod
    @abstractmethod
    def action_result(cls, payload) -> UiActionInvokeResult:
        raise NotImplementedError

    @classmethod
    def introduction_lines(cls, payload) -> tuple[str, ...]:
        return ()

    @classmethod
    def render_payload(cls, payload, options: McpDevOutputRenderOptions) -> str:
        action = cls.action_result(payload)
        return "\n".join(
            (
                *cls.introduction_lines(payload),
                f"UI action invoke: "
                f"action={action.identity.widget_id}/{action.identity.action_id} "
                f"status={action.status}",
                cls.acknowledgement_line(action.receipt),
                f"Selection: targets={cls.sequence_text(action.target_scope_ids)} "
                f"selection_rev={cls.text(action.selection_revision_token)}",
                f"Follow: surfaces={cls.sequence_text(action.workflow_status_surface_ids)} "
                f"events_after={cls.text(action.event_sequence)}",
            )
        )


class UiActionInvokeRenderer(UiActionResultRenderer):
    """The direct action is already the declared invocation result."""

    output_contract = UiActionInvokeResult

    @classmethod
    def action_result(cls, payload: UiActionInvokeResult) -> UiActionInvokeResult:
        return payload


class UiSelectedPlateWorkflowRenderer(UiActionResultRenderer):
    """Workflow wrapper owns its nested action, not a second action schema."""

    output_contract = UiSelectedPlateWorkflowResult

    @classmethod
    def action_result(
        cls, payload: UiSelectedPlateWorkflowResult
    ) -> UiActionInvokeResult:
        return payload.action_result

    @classmethod
    def introduction_lines(
        cls, payload: UiSelectedPlateWorkflowResult
    ) -> tuple[str, ...]:
        return (
            f"Workflow: {payload.workflow.value} state_surface={payload.state_surface_id}",
        )


class UiWidgetActionInvokeRenderer(UiMutationRenderer):
    """Compact renderer for generic widget action invocation results."""

    output_contract = UiWidgetActionInvokeResult

    @classmethod
    def render_payload(
        cls, payload: UiWidgetActionInvokeResult, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"Widget action invoke: window={payload.window_id} path={payload.path_id} "
            f"kind={payload.action_kind} invoked={payload.invoked}",
            cls.acknowledgement_line(payload.receipt),
        ]
        lines.extend(
            cls.optional_lines(
                payload.summary,
                lambda summary: (
                    f"Widget: label={cls.quoted(summary.label)} "
                    f"enabled={summary.enabled} clickable={summary.clickable} "
                    f"actions={cls.sequence_text(summary.action_kinds)}",
                ),
            )
        )
        return "\n".join(lines)
