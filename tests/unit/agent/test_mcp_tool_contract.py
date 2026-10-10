"""External MCP contract: the advertised tools and resources stay exactly as on main.

The fixture was generated once from ``main`` before the capability invocation
family replaced the per-slot server bindings. MCP clients depend on these names,
titles, descriptions, annotations and schemas.
"""

from __future__ import annotations

import asyncio
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

pytest.importorskip("mcp")

from openhcs.agent.capabilities import (  # noqa: E402
    CapabilityTransport,
    LocalCapabilitySurfaceProfile,
)
from openhcs.mcp.server import build_server  # noqa: E402

FIXTURE_PATH = (
    Path(__file__).resolve().parents[2] / "fixtures" / "mcp" / "mcp_tool_contract.json"
)


async def _surface(transport: CapabilityTransport, profile_name: str):
    server = build_server(
        SimpleNamespace(),
        capability_transport=transport,
        capability_surface_profile=LocalCapabilitySurfaceProfile.for_name(profile_name),
    )
    tools = await server.list_tools()
    resources = await server.list_resources()
    return (
        {tool.name: tool.model_dump(mode="json") for tool in tools},
        sorted(
            (resource.model_dump(mode="json") for resource in resources),
            key=lambda resource: resource["uri"],
        ),
    )


def current_mcp_contract() -> dict[str, object]:
    async def collect():
        surfaces: dict[str, list[str]] = {}
        tools: dict[str, object] = {}
        resources: dict[str, object] = {}
        for transport in CapabilityTransport:
            for profile_name in LocalCapabilitySurfaceProfile.names():
                surface_tools, surface_resources = await _surface(
                    transport, profile_name
                )
                surfaces[f"{transport.value}/{profile_name}"] = sorted(surface_tools)
                for name, record in surface_tools.items():
                    assert tools.setdefault(name, record) == record
                resources[f"{transport.value}/{profile_name}"] = surface_resources
        return {"surfaces": surfaces, "tools": tools, "resources": resources}

    return asyncio.run(collect())


def test_mcp_tools_resources_and_schemas_match_main_contract():
    expected = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
    actual = current_mcp_contract()

    assert actual["surfaces"] == expected["surfaces"]
    assert sorted(actual["tools"]) == sorted(expected["tools"])
    for name, record in expected["tools"].items():
        assert actual["tools"][name] == record, name
    assert actual["resources"] == expected["resources"]
