"""Real CLI/codec action-family checks without a server or UI mutation."""
import sys
import json
from dataclasses import dataclass, replace

import pytest

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.ui_bridge import (
    UiActionIdentity,
    UiActionInvokeResult,
    UiBridgeOperationIdentity,
    UiBridgeOperationRef,
    UiBridgeOperationRoute,
    UiMutationReceipt,
    UiMutationRequestToken,
    UiPlateManagerRowState,
    UiPlateManagerState,
    UiSelectedPlateWorkflowKind,
    UiSelectedPlateWorkflowResult,
    UiStateSurfaceDocument,
    UiStateSurfaceIdentity,
    UiStateSurfaceSummary,
    UiWidgetTreeResult,
    UiWindowIdentity,
    UiWindowSummary,
)
from openhcs.mcp import dev_client
from openhcs.mcp.dev_client_core import (
    McpDevServerSpec, McpDevToolBatchResponse, McpDevToolResult,
    workflow_result_action_status, workflow_result_target_scope_ids,
    workflow_poll_summary_result,
)
from openhcs.mcp.dev_client_rendering import (
    McpDevOutputRenderer, McpDevOutputRenderOptions,
)
from openhcs.mcp.dev_client_renderers.ui_bridge import UiActionInvokeRenderer
from openhcs.serialization.json import to_jsonable


def action_fixture():
    return UiActionInvokeResult(
        SCHEMA_VERSION,
        UiActionIdentity(widget_id="plate_manager", action_id="run_plate"),
        "accepted",
        UiMutationReceipt(UiMutationRequestToken(), accepted=True),
        target_scope_ids=("scope-1",),
    )


def action_result(capability, value):
    return McpDevToolResult.from_payload(capability.name, {
        "isError": False, "structuredContent": to_jsonable(value), "content": [],
    })


def state_fixture(compiled, revision):
    summary = UiStateSurfaceSummary(
        SCHEMA_VERSION, UiStateSurfaceIdentity(surface_id="plate_manager.state"),
        "Plate Manager", True, widget_id="plate_manager",
    )
    row = UiPlateManagerRowState(
        plate_scope_id="scope-1", name="plate-one", plate_root="/plate-one",
        cppipe_path=None, selected=True, initialized=True, compiled=compiled,
        init_pending=False, compile_pending=False, execution_active=False,
        status_prefix="Compiled" if compiled else "Created",
        orchestrator_state="compiled" if compiled else "created",
        execution_id=None, terminal_status=None,
        runtime_state=None, runtime_percent=None, queue_position=None,
    )
    state = UiPlateManagerState(
        schema_version=SCHEMA_VERSION, summary=summary, object_state_token=revision,
        manager_execution_state="idle", rows=(row,),
        current_revision_token=f"rev-{revision}",
    )
    return UiStateSurfaceDocument(
        schema_version=SCHEMA_VERSION, summary=summary,
        payload_schema="openhcs.ui.plate_manager_state.v1", payload=to_jsonable(state),
        current_revision_token=state.current_revision_token,
    )


@pytest.mark.parametrize("json_output", (False, True))
def test_named_cli_wait_preserves_action_receipt_poll_and_final_rows(
    monkeypatch, capsys, json_output,
):
    """Actual CLI/controller/codec chain, with only the MCP wire controlled."""
    native = UiSelectedPlateWorkflowResult(
        SCHEMA_VERSION, UiSelectedPlateWorkflowKind("compile_plate"),
        replace(action_fixture(),
                identity=UiActionIdentity(widget_id="plate_manager", action_id="compile_plate"),
                receipt=UiMutationReceipt(UiMutationRequestToken(), "operation-one", True)),
    )
    receipt = UiBridgeOperationRef(
        schema_version=SCHEMA_VERSION, status="completed", started_at_unix=1.0,
        completed_at_unix=2.0, outcome="completed",
        identity=UiBridgeOperationIdentity("operation-one", UiBridgeOperationRoute("invoke_action")),
    )
    calls = []
    wire_values = iter((state_fixture(False, 1), native, receipt, state_fixture(True, 2)))
    wire_payloads = tuple(to_jsonable(value) for value in wire_values)

    class ControlledWireSession:
        server_spec = McpDevServerSpec(sys.executable)

        async def call_tool(self, name, arguments, *, timeout_seconds):
            calls.append(name)
            return {"isError": False, "structuredContent": wire_payloads[len(calls)-1], "content": []}

    async def controlled_session(args):
        return await dev_client.McpDevCommandSpec.for_name(args.command).run_session(
            ControlledWireSession(), args,
        )

    import openhcs.serialization.json as serialization
    monkeypatch.setattr(dev_client, "_run_async", controlled_session)
    if not json_output:
        def forbidden_serialization(value):
            raise AssertionError("Compact polling must retain its typed summary")
        monkeypatch.setattr(serialization, "to_jsonable", forbidden_serialization)
    argv = ["selected-workflow", "compile_plate", "--wait", "--wait-interval-seconds", "0"]
    if json_output:
        argv.append("--json")
    assert dev_client.main(argv) == 0
    assert calls == [agent_capabilities.ui_get_state_surface.name,
                     agent_capabilities.ui_selected_plate_workflow.name,
                     agent_capabilities.ui_wait_for_operation_receipt.name,
                     agent_capabilities.ui_get_state_surface.name]
    rendered = capsys.readouterr().out
    if json_output:
        response = json.loads(rendered)
        action = response["results"][1]["payloads"][0]["action_result"]
        assert action["receipt"]["accepted"] is True
        assert action["receipt"]["bridge_operation_id"] == "operation-one"
        summary = response["results"][-1]["payloads"][0]
        assert summary["poll_status"] == "completed" and summary["poll_count"] == 1
        assert summary["target_scope_ids"] == ["scope-1"]
    else:
        assert "Action: accepted poll=completed count=1" in rendered
        assert "Targets: scope-1" in rendered
        assert '- plate-one: state=compiled, status="Compiled", terminal=<none>, selected=True' in rendered


def test_malformed_action_is_nonzero_and_preserves_invalid_wire_receipt(monkeypatch, capsys):
    malformed = {"workflow": "run_plate", "action_result": {"status": "accepted"}}
    result = McpDevToolResult.from_payload(
        agent_capabilities.ui_selected_plate_workflow.name,
        {"isError": False, "structuredContent": malformed, "content": []},
    )
    response = McpDevToolBatchResponse.from_results(McpDevServerSpec(sys.executable), (result,))

    async def controlled_wire(args):
        return response

    monkeypatch.setattr(dev_client, "_run_async", controlled_wire)
    assert dev_client.main(["selected-workflow", "run_plate"]) == 1
    assert "mcp_payload_invalid" in capsys.readouterr().out
    assert dev_client.main(["selected-workflow", "run_plate", "--json"]) == 1
    assert json.loads(capsys.readouterr().out)["results"][0]["payloads"][0] == malformed


def test_poll_presentation_rejects_row_missing_declared_state_field():
    state = state_fixture(True, 2)
    del state.payload["rows"][0]["initialized"]
    response = McpDevToolBatchResponse.from_results(
        McpDevServerSpec(sys.executable),
        (action_result(agent_capabilities.ui_get_state_surface, state),
         workflow_poll_summary_result(
             workflow="compile_plate", poll_requested=True,
             poll_completed=True, poll_count=1, action_status="accepted",
         )),
    )
    args = dev_client._build_parser().parse_args(["selected-workflow", "compile_plate", "--wait"])
    with pytest.raises(ValueError, match="missing required field.*initialized"):
        dev_client.McpDevCommandSpec.for_name("selected-workflow").render_result(response, args)


def test_actual_generic_cli_retains_nested_action_without_json_roundtrip(monkeypatch, capsys):
    native = UiSelectedPlateWorkflowResult(
        SCHEMA_VERSION, UiSelectedPlateWorkflowKind("run_plate"), action_fixture(),
    )
    result = action_result(agent_capabilities.ui_selected_plate_workflow, native)
    response = McpDevToolBatchResponse.from_results(McpDevServerSpec(sys.executable), (result,))

    async def controlled_wire(args):
        return response

    def forbidden_serialization(value):
        raise AssertionError("Compact presentation must retain the decoded result")

    import openhcs.serialization.json as serialization
    monkeypatch.setattr(dev_client, "_run_async", controlled_wire)
    monkeypatch.setattr(serialization, "to_jsonable", forbidden_serialization)
    assert dev_client.main([
        "call", agent_capabilities.ui_selected_plate_workflow.name,
        "--arguments", '{"workflow":"run_plate"}',
    ]) == 0
    rendered = capsys.readouterr().out
    assert "action=plate_manager/run_plate status=accepted" in rendered
    assert "accepted=True" in rendered and "targets=scope-1" in rendered
    assert workflow_result_action_status(result) == "accepted"
    assert workflow_result_target_scope_ids(result) == ("scope-1",)


@pytest.mark.parametrize("presentation", ((), ("--output", "outline"),
    ("--output", "json"), ("--json",)))
def test_actual_widget_tree_cli_uses_its_declared_output_format(
    monkeypatch, capsys, presentation,
):
    """The real CLI must not require a second undeclared args.json flag."""
    native = UiWidgetTreeResult(
        schema_version=SCHEMA_VERSION, window_id="main_window", projected=True,
        summary=UiWindowSummary(SCHEMA_VERSION, UiWindowIdentity(window_id="main_window"),
            "OpenHCS regression window", "qt_top_level", True, True),
    )
    result = action_result(agent_capabilities.ui_get_widget_tree, native)
    response = McpDevToolBatchResponse.from_results(
        McpDevServerSpec(sys.executable), (result,),
    )

    async def controlled_wire(args):
        return response

    monkeypatch.setattr(dev_client, "_run_async", controlled_wire)
    assert dev_client.main(["widget-tree", "main_window", *presentation]) == 0
    output = capsys.readouterr().out
    if "json" in presentation or "--json" in presentation:
        decoded = json.loads(output)
        assert decoded["results"][0]["payloads"][0]["window_id"] == "main_window"
        assert decoded["results"][0]["payloads"][0]["projected"] is True
    else:
        assert "Window: OpenHCS regression window" in output
        assert "Tree: <not returned; use --include-tree or outline mode>" in output


def test_generic_widget_tree_call_uses_the_same_output_declaration(monkeypatch, capsys):
    native = UiWidgetTreeResult(
        schema_version=SCHEMA_VERSION, window_id="main_window", projected=True,
        summary=UiWindowSummary(SCHEMA_VERSION, UiWindowIdentity(window_id="main_window"),
            "OpenHCS regression window", "qt_top_level", True, True),
    )
    result = action_result(agent_capabilities.ui_get_widget_tree, native)
    response = McpDevToolBatchResponse.from_results(
        McpDevServerSpec(sys.executable), (result,),
    )

    async def controlled_wire(args):
        return response

    monkeypatch.setattr(dev_client, "_run_async", controlled_wire)
    assert dev_client.main(["call", agent_capabilities.ui_get_widget_tree.name,
        "--arguments", '{"window_id":"main_window"}']) == 0
    assert "Window: OpenHCS regression window" in capsys.readouterr().out


@pytest.mark.parametrize("reverse", (False, True))
def test_independent_presentation_capabilities_cooperate_in_both_mro_orders(reverse):
    events = []

    class FirstCapability:
        @classmethod
        def introduction_lines(cls, payload):
            events.append("first")
            return (*super().introduction_lines(payload), "first capability")

    class SecondCapability:
        @classmethod
        def introduction_lines(cls, payload):
            events.append("second")
            return (*super().introduction_lines(payload), "second capability")

    @dataclass(frozen=True, slots=True)
    class ExtendedAction(UiActionInvokeResult):
        annotation: str = "new declared fact"

    bases = ((SecondCapability, FirstCapability) if reverse else
             (FirstCapability, SecondCapability))
    extension = type("ExtendedActionRenderer", (*bases, UiActionInvokeRenderer),
                     {"output_contract": ExtendedAction})
    try:
        assert McpDevOutputRenderer.for_output_contract(ExtendedAction).renderer_type is extension
        value = ExtendedAction(
            SCHEMA_VERSION, UiActionIdentity(widget_id="plate_manager", action_id="run_plate"),
            "accepted", UiMutationReceipt(UiMutationRequestToken(), accepted=True),
        )
        decoded = extension.decode_payload(to_jsonable(value), ExtendedAction)
        assert decoded.annotation == "new declared fact"
        rendered = extension.render_payload_value(decoded, McpDevOutputRenderOptions())
        assert events == (["second", "first"] if reverse else ["first", "second"])
        assert rendered.count("first capability") == rendered.count("second capability") == 1
        assert rendered.count("UI action invoke:") == 1
    finally:
        del McpDevOutputRenderer.__registry__[ExtendedAction]
