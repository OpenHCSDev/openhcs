"""UI bridge presentations over typed DTO fixtures."""

from __future__ import annotations

from dataclasses import replace

from python_introspect import to_jsonable

from openhcs.agent.dto.common import AgentError, AgentWarning
from openhcs.agent.dto.mcp import McpServerHealthResult
from openhcs.agent.dto.ui_bridge import (
    QT_TOP_LEVEL_WINDOW_KIND,
    UiActionCatalog,
    UiActionIdentity,
    UiActionSummary,
    UiBridgeCatalog,
    UiBridgeStatus,
    UiCodeDocument,
    UiCodeDocumentApplyResult,
    UiCodeDocumentCatalog,
    UiCodeDocumentIdentity,
    UiCodeDocumentSummary,
    UiDebugRuntimeFrameState,
    UiPipelineDebugSessionState,
    UiPipelineEditorState,
    UiPipelineEditorStepState,
    UiPlateManagerRowState,
    UiPlateManagerState,
    UiSnapshotRef,
    UiStateSurfaceCatalog,
    UiStateSurfaceDocument,
    UiStateSurfaceIdentity,
    UiStateSurfaceSummary,
    UiWidgetActionSummary,
    UiWidgetTreeNode,
    UiWidgetTreeResult,
    UiWindowCatalog,
    UiWindowIdentity,
    UiWindowSummary,
)
from openhcs.agent.ui_bridge_identities import (
    PipelineEditorStateSurfaceIdentityDeclaration,
    PlateManagerStateSurfaceIdentityDeclaration,
)
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolBatchResponse,
    McpDevToolListResponse,
    McpDevToolMetadata,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_renderers.ui_bridge import (
    PlateManagerStateSurfaceRenderer,
    UiSmokeRenderer,
)
from openhcs.mcp.dev_client_rendering import (
    CatalogRenderOptions,
    CodeDocumentRenderOptions,
    McpDevOutputRenderer,
    ToolListRenderer,
    UiActionCatalogRenderOptions,
    WidgetTreeRenderOptions,
)
from test_mcp_dev_client_renderers import SERVER, framed, sample_dto


def render(payload, options=None) -> str:
    return McpDevOutputRenderer.for_output_contract(type(payload)).render(
        framed(payload), options
    )


def snapshot(index: int, label: str = "edit") -> UiSnapshotRef:
    return replace(
        sample_dto(UiSnapshotRef), index=index, label=label, branch="main",
        snapshot_id=f"snapshot-{index}",
    )


def surface_summary(surface_id: str, **values) -> UiStateSurfaceSummary:
    return replace(
        sample_dto(UiStateSurfaceSummary),
        identity=UiStateSurfaceIdentity(surface_id=surface_id),
        **values,
    )


def document_for(state) -> UiStateSurfaceDocument:
    return replace(
        sample_dto(UiStateSurfaceDocument),
        summary=state.summary,
        payload=to_jsonable(state),
        warnings=(),
    )


def test_bridge_status_and_unavailable_bridge():
    status = replace(
        sample_dto(UiBridgeStatus),
        reachable=True,
        descriptor_status="ok",
        bridge_instance_id="ui-test",
        supported_operations=("a", "b"),
        bridge_features=("c",),
        warnings=(),
    )
    rendered = render(status)
    assert "UI bridge: reachable=True descriptor=ok" in rendered
    assert "Instance: ui-test pid=" in rendered
    assert "Capabilities: 2 operations, 1 features" in rendered

    failed = McpDevToolBatchResponse(
        server=SERVER,
        results=(McpDevToolResult(tool="t", mcp_error=True, payloads=()),),
    )
    assert McpDevOutputRenderer.for_output_contract(UiBridgeStatus).render(
        failed
    ).startswith("UI bridge: unavailable\nErrors:")


def window(window_id: str, title: str, kind: str, visible: bool) -> UiWindowSummary:
    return replace(
        sample_dto(UiWindowSummary),
        identity=UiWindowIdentity(window_id=window_id),
        title=title,
        window_kind=kind,
        visible=visible,
    )


def window_catalog() -> UiWindowCatalog:
    return replace(
        sample_dto(UiWindowCatalog),
        windows=(
            window("main_window", "OpenHCS", QT_TOP_LEVEL_WINDOW_KIND, True),
            window("qt_top_level:1", "Error", QT_TOP_LEVEL_WINDOW_KIND, True),
            window("qt_top_level:2", "Hidden", QT_TOP_LEVEL_WINDOW_KIND, False),
            window("plate_manager", "Plate Manager", "embedded", True),
        ),
        warnings=(),
    )


def test_window_catalog_flags_only_visible_stray_top_level_windows():
    rendered = render(window_catalog())
    assert "Windows: 4" in rendered
    assert (
        'Attention: 1 visible top-level window(s): qt_top_level:1 title="Error"'
        in rendered
    )
    assert '- plate_manager [embedded] visible=True' in rendered


def test_ui_smoke_composes_each_tool_payload():
    from openhcs.agent.capabilities import agent_capabilities

    def result(capability, payload):
        return McpDevToolResult(tool=capability.name, mcp_error=False, payloads=(payload,))

    health = replace(
        sample_dto(McpServerHealthResult),
        status="ok", restart_required=False, stale_source_paths=(), warnings=(),
    )
    bridges = replace(sample_dto(UiBridgeCatalog), warnings=())
    status = replace(sample_dto(UiBridgeStatus), reachable=True, descriptor_status="ok", warnings=())
    response = McpDevToolBatchResponse(
        server=SERVER,
        results=(
            result(agent_capabilities.health_check, health),
            result(agent_capabilities.ui_bridge_status, status),
            result(agent_capabilities.ui_list_bridges, bridges),
            result(agent_capabilities.ui_list_windows, window_catalog()),
        ),
    )
    rendered = UiSmokeRenderer.render(response)
    assert "UI smoke: results=4 mcp_errors=0" in rendered
    assert "Health: status=ok restart_required=False stale_paths=0" in rendered
    assert "UI bridge: reachable=True descriptor=ok" in rendered
    assert f"Bridges: live={len(bridges.bridges)} errors=0" in rendered
    assert "Attention: 1 visible top-level window(s)" in rendered


def test_catalogs_filter_and_truncate_with_contains_and_limit():
    surfaces = replace(
        sample_dto(UiStateSurfaceCatalog),
        surfaces=(
            surface_summary("plate_manager.state", title="Plate Manager"),
            surface_summary("plate_manager.debug", title="Debug"),
            surface_summary("pipeline_editor.state", title="Pipeline Editor"),
        ),
    )
    rendered = render(surfaces, CatalogRenderOptions(contains="plate", limit=1))
    assert "State surfaces: count=3 matched=2 shown=1" in rendered
    assert "Filter: contains=plate" in rendered
    assert "- plate_manager.state: widget=" in rendered
    assert "plate_manager.debug" not in rendered
    assert "...<truncated 1 surfaces>" in rendered

    def document(document_id):
        return replace(
            sample_dto(UiCodeDocumentSummary),
            identity=UiCodeDocumentIdentity(document_id=document_id),
        )

    documents = replace(
        sample_dto(UiCodeDocumentCatalog),
        documents=(document("plate_manager.orchestrator_config"), document("pipeline")),
    )
    assert "Code documents: count=2 matched=2 shown=2" in render(documents)


def plate_row(name: str, selected: bool, **values) -> UiPlateManagerRowState:
    return replace(
        sample_dto(UiPlateManagerRowState),
        name=name, selected=selected, orchestrator_state="compiled",
        status_prefix="", terminal_status=None, plate_root=f"/{name}",
        output_plate_root=None, source_plate_root=None, **values,
    )


def test_state_surface_documents_render_through_their_surface_state():
    state = replace(
        sample_dto(UiPlateManagerState),
        summary=surface_summary(
            PlateManagerStateSurfaceIdentityDeclaration.require_value(),
            current_selection_count=1,
        ),
        manager_execution_state="idle",
        current_snapshot=snapshot(3, "auto-add output plate"),
        rows=(plate_row("plate-a", True), plate_row("plate-b", False)),
        warnings=(),
    )
    rendered = render(document_for(state))
    assert "Plate manager: rows=2 selected=1 manager=idle" in rendered
    assert 'Snapshot: 3 "auto-add output plate"' in rendered
    assert (
        "- plate-a: state=compiled, status=<none>, init=True, compiled=True, "
        "active=True, terminal=<none>, selected=True, root=/plate-a"
    ) in rendered
    # The workflow command reuses this one row presentation.
    assert PlateManagerStateSurfaceRenderer.row_lines(state.rows) == [
        line for line in rendered.splitlines() if line.startswith("- plate-")
    ]

    editor = replace(
        sample_dto(UiPipelineEditorState),
        summary=surface_summary(
            PipelineEditorStateSurfaceIdentityDeclaration.require_value(),
            current_selection_count=1, total_scope_count=2,
        ),
        current_snapshot=snapshot(4, "edit pipeline"),
        selected_scope_ids=("/tmp/plate-a::functionstep_1",),
        steps=(
            replace(
                sample_dto(UiPipelineEditorStepState),
                index=0, name="normalize", dirty=True, default_diff=False,
                function_names=("normalize",), function_ids=(), debug_pause=False,
                step_scope_id=None,
            ),
        ),
        warnings=(),
    )
    rendered = render(document_for(editor))
    assert 'Snapshot: 4 "edit pipeline"' in rendered
    assert "Selected scopes: /tmp/plate-a::functionstep_1" in rendered
    assert "- 0. [*] normalize: enabled=True, selected=True, funcs=normalize" in rendered
    assert "ids=" not in rendered


def test_pipeline_debug_session_shows_distinct_frames_and_actions():
    frame = sample_dto(UiDebugRuntimeFrameState)
    state = replace(
        sample_dto(UiPipelineDebugSessionState),
        phase="active_session",
        current_frame=frame,
        last_frame=frame,
        warnings=(),
    )
    rendered = render(state)
    assert rendered.startswith("Pipeline debug: phase=active_session")
    assert "Current frame: event=" in rendered
    assert "Last frame" not in rendered
    assert "Actions:" in rendered


def test_unregistered_or_unreadable_surface_points_to_the_catalog():
    document = replace(
        sample_dto(UiStateSurfaceDocument),
        summary=surface_summary("plate_manager", readable=False),
        payload={},
        warnings=(),
        errors=(AgentError(code="ui_state_surface_unreadable", message="Not readable."),),
    )
    rendered = render(document)
    assert "Surface: plate_manager" in rendered
    assert "Readable: False" in rendered
    assert "Next: state-surfaces" in rendered
    assert "Errors:\n- ui_state_surface_unreadable: Not readable." in rendered


def tree_node(class_name: str, *children, **values) -> UiWidgetTreeNode:
    defaults = dict(
        object_name="", text=None, title=None, current_text=None, visible=True,
        enabled=True, clickable=True, actionable=False, action_kinds=(),
    )
    return replace(
        sample_dto(UiWidgetTreeNode),
        class_name=class_name, children=children, **(defaults | values),
    )


def test_widget_tree_outline_shows_addressable_paths_and_hides_technical_nodes():
    root = tree_node(
        "PipelineEditorWidget",
        tree_node("QPushButton", text="Edit", path_id="1.0.2", action_kinds=("button",),
                  enabled=False, clickable=False),
        tree_node("QPushButton", text="Generate", path_id="1.0.3",
                  action_kinds=("button",), visible=False),
        tree_node("QScrollBar"),
        tree_node("QLineEdit", path_id="1.0.4", actionable=True, text="Gamma"),
        tree_node("QLabel", current_text="long " * 40),
    )
    action = replace(
        sample_dto(UiWidgetActionSummary),
        path_id="1.0.4", object_state_scope_id="/plate::step", field_path="gamma",
        semantic_markers=("*",),
    )
    result = replace(
        sample_dto(UiWidgetTreeResult),
        root=root, actionable_widgets=(action,), tree_truncated=False,
        actionable_widgets_truncated=False, warnings=(),
        summary=replace(sample_dto(UiWindowSummary), title="Pipeline Editor",
                        dirty=False, dirty_field_count=0, signature_diff=True,
                        semantic_markers=()),
    )
    rendered = render(result)
    assert "Window: Pipeline Editor" in rendered
    assert "Status: dirty=False dirty_fields=0 default_diff=True" in rendered
    assert 'QPushButton "Edit" path=1.0.2 disabled' in rendered
    assert "not-clickable" not in rendered
    assert "Generate" not in rendered
    assert "QScrollBar" not in rendered
    assert "QLineEdit path=1.0.4 [*] scope=/plate::step field=gamma" in rendered
    # A semantic field address replaces the widget's display text.
    assert "Gamma" not in rendered
    compact = ("long " * 40).strip()[:93] + "..."
    assert f'QLabel current="{compact}"' in rendered

    technical = render(result, WidgetTreeRenderOptions(include_technical_widgets=True))
    assert "QScrollBar" in technical

    rooted = render(result, WidgetTreeRenderOptions(outline_root_class="QLineEdit"))
    assert "PipelineEditorWidget" not in rooted
    assert render(
        result, WidgetTreeRenderOptions(outline_root_class="Missing")
    ).endswith('Tree: <no node with class "Missing">')


def test_code_document_bounds_its_source():
    document = replace(
        sample_dto(UiCodeDocument), source="pattern = (some_func," + "x" * 50,
        current_snapshot=snapshot(10), warnings=(),
    )
    rendered = render(document, CodeDocumentRenderOptions(max_source_chars=20))
    assert "Revision: token=" in rendered and "snapshot=main@10 head=" in rendered
    assert "Source:\npattern = (some_func" in rendered
    assert "...<truncated 51 chars>" in rendered
    assert "Source:" not in render(document, CodeDocumentRenderOptions(include_source=False))


def test_code_document_apply_shows_revisions_and_snapshots():
    applied = replace(
        sample_dto(UiCodeDocumentApplyResult),
        base_revision_token="rev-123", current_revision_token="rev-456",
        new_revision_token="rev-456", current_snapshot=snapshot(10),
        undo_snapshot=None, warnings=(),
    )
    rendered = render(applied)
    assert "Revision: base=rev-123 current=rev-456 new=rev-456" in rendered
    assert "Snapshots: current=main@10:snapshot-10 undo=<none>" in rendered
    assert "Receipt: accepted=" in rendered


def ui_action(widget_id: str, action_id: str, **values) -> UiActionSummary:
    return replace(
        sample_dto(UiActionSummary),
        identity=UiActionIdentity(widget_id=widget_id, action_id=action_id),
        **values,
    )


def test_action_catalog_filters_actions_and_warnings_by_widget():
    catalog = replace(
        sample_dto(UiActionCatalog),
        actions=(
            ui_action(
                "plate_manager", "compile_plate", enabled=False,
                disabled_error=AgentError(code="no_plate", message="No plate.", hint="Add a plate."),
            ),
            ui_action("image_browser", "open_file"),
        ),
        warnings=(
            AgentWarning(code="plate_path_setup_uses_code_document", message="Use plate_manager code."),
            AgentWarning(code="unrelated", message="Something else."),
        ),
    )
    everything = render(catalog)
    assert "UI actions: count=2" in everything
    assert "Warnings:" in everything and "unrelated" in everything

    plate = render(catalog, UiActionCatalogRenderOptions(widget_id="plate_manager"))
    assert "UI actions: count=1 widget=plate_manager" in plate
    assert "- plate_manager/compile_plate: " in plate
    assert " disabled=no_plate:No plate." in plate
    assert 'Disabled hints:\n- plate_manager/compile_plate: "Add a plate."' in plate
    assert "- plate_path_setup_uses_code_document:" in plate
    assert "unrelated" not in plate
    assert "image_browser/open_file" not in plate
    # A disabled action describes the catalog; it is not a failed call.
    assert "Errors:" not in plate

    editor = render(catalog, UiActionCatalogRenderOptions(widget_id="pipeline_editor"))
    assert "UI actions: count=0 widget=pipeline_editor" in editor
    assert "Warnings:" not in editor
    assert "widget-tree pipeline_editor" in editor


def test_disabled_actions_do_not_make_the_call_fail():
    catalog = replace(
        sample_dto(UiActionCatalog),
        actions=(ui_action("w", "a", disabled_error=AgentError(code="off", message="Off.")),),
    )
    result = McpDevToolResult(tool="t", mcp_error=False, payloads=(catalog,))
    assert not result.has_errors()


def test_tool_list_filters_groups_and_flattens():
    tools = McpDevToolListResponse(
        server=SERVER,
        tool_count=3,
        tools=(
            McpDevToolMetadata("openhcs_get_viewer_window_state", "Read bounded viewer state.", {}),
            McpDevToolMetadata("openhcs_validate_viewer_window_state", "Validate viewer.", {}),
            McpDevToolMetadata("openhcs_health_check", "Health.", {}),
        ),
    )
    rendered = ToolListRenderer.render(tools, contains="viewer", limit=1)
    assert "Tools: matched=2 total=3 shown=1" in rendered
    assert "Filter: contains=viewer" in rendered
    assert "[Viewer Review]" in rendered
    assert "- openhcs_get_viewer_window_state: Read bounded viewer state." in rendered
    assert "...<truncated 1 tools>" in rendered
    flat = ToolListRenderer.render(tools, contains="viewer", limit=1, grouped=False)
    assert "[Viewer Review]" not in flat
    projected = ToolListRenderer.project_response(tools, contains="viewer", limit=1)
    assert projected["matched_tool_count"] == 2
    assert [tool["name"] for tool in projected["tools"]] == ["openhcs_get_viewer_window_state"]
