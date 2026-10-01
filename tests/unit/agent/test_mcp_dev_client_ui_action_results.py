"""Real CLI/codec action-family checks without a server or UI mutation."""
import sys
from dataclasses import dataclass

import pytest

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.ui_bridge import (
    UiActionIdentity,
    UiActionInvokeResult,
    UiMutationReceipt,
    UiMutationRequestToken,
    UiSelectedPlateWorkflowKind,
    UiSelectedPlateWorkflowResult,
)
from openhcs.mcp import dev_client
from openhcs.mcp.dev_client_core import (
    McpDevServerSpec, McpDevToolBatchResponse, McpDevToolResult,
    workflow_result_action_status, workflow_result_target_scope_ids,
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
