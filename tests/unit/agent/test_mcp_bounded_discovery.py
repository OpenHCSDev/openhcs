"""Focused regressions for bounded MCP discovery and side-effect-free help."""

from __future__ import annotations

import json

import pytest

import openhcs.mcp.dev_client as dev_client
import openhcs.mcp.http as mcp_http
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity,
    McpDevToolListResponse,
    McpDevToolMetadata,
)


def test_tools_json_honors_filter_and_limit_without_losing_tool_metadata() -> None:
    args = dev_client._build_parser().parse_args(
        ("tools", "--contains", "viewer", "--limit", "1", "--json")
    )
    tools = (
        McpDevToolMetadata(
            name="openhcs_get_viewer_window_state",
            description="Read bounded viewer state.",
            input_schema={"type": "object", "properties": {"port": {}}},
            output_schema={"type": "object"},
        ),
        McpDevToolMetadata(
            name="openhcs_validate_viewer_window_state",
            description="Validate viewer axes and payloads.",
            input_schema={"type": "object"},
        ),
        McpDevToolMetadata(
            name="openhcs_health_check",
            description="Report health.",
            input_schema={"type": "object"},
        ),
    )
    response = McpDevToolListResponse(
        server=McpDevServerIdentity(command="python", module="openhcs.mcp"),
        tool_count=len(tools),
        tools=tools,
    )

    rendered = dev_client.McpDevCommandSpec.for_name("tools").render_result(
        response,
        args,
    )
    payload = json.loads(rendered)

    assert payload["server"] == {"command": "python", "module": "openhcs.mcp"}
    assert payload["tool_count"] == 3
    assert payload["matched_tool_count"] == 2
    assert payload["returned_tool_count"] == 1
    assert payload["truncated_tool_count"] == 1
    assert payload["filter"] == {"contains": "viewer", "limit": 1}
    assert [tool["name"] for tool in payload["tools"]] == [
        "openhcs_get_viewer_window_state"
    ]
    assert payload["tools"][0]["input_schema"]["properties"] == {"port": {}}
    assert payload["tools"][0]["output_schema"] == {"type": "object"}


def test_http_help_exits_before_settings_or_server_construction(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    construction_attempts: list[bool] = []

    def fail_if_constructed():
        construction_attempts.append(True)
        raise AssertionError("HTTP server construction must not run for --help")

    monkeypatch.setattr(mcp_http, "build_http_server", fail_if_constructed)

    with pytest.raises(SystemExit) as exc_info:
        mcp_http.main(("--help",))

    assert exc_info.value.code == 0
    assert construction_attempts == []
    assert "stateless OpenHCS MCP HTTP server" in capsys.readouterr().out
