"""Declaration-generated public tools, without socket/native/GUI process launch."""

import asyncio
from dataclasses import fields

import pytest

from openhcs.agent.capabilities import (
    CapabilityWorkflowGroup,
    LocalCapabilitySurfaceProfile,
    WorkflowGroupCapabilitySurfaceMixin,
)
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import (
    ViewerWindowNativePresentationRequest,
    ViewerWindowImageColorRequest,
)
from openhcs.agent.services.viewer_window_service import ViewerWindowService
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.mcp.server import build_server
from openhcs.runtime.napari_viewer_server import NapariControlMessageAction
from openhcs.runtime.viewer_protocol import (
    ViewerNativeWindowControlOptions,
    ViewerNativeWindowGeometry,
    ViewerNativeImageColorPresentation,
)
from tests.unit.test_native_viewer_presentation import CameraGateway
from tests.unit.agent.test_native_presentation_451452 import native_server


class PresentationAndPlateSurface(
    WorkflowGroupCapabilitySurfaceMixin, LocalCapabilitySurfaceProfile
):
    # Existing surface capability, not a new production catalog or name roster.
    workflow_groups = frozenset(
        (CapabilityWorkflowGroup.VIEWER_REVIEW, CapabilityWorkflowGroup.PLATE_DATA)
    )


class NativePresentationGateway(CameraGateway):
    def __init__(self):
        self.server, self.window = native_server()
        self.calls = []

    def presentation_control(self, request):
        self.calls.append(request)
        return NapariControlMessageAction.for_message_type(request.message_type).handle(
            self.server,
            {"payload": request.control_payload},
        )


def test_original_mcp_generators_publish_and_invoke_both_native_operations():
    from mcp.server.fastmcp.exceptions import ToolError

    gateway = NativePresentationGateway()
    built = build_server(
        OpenHCSAgentContext(viewer_window_service=ViewerWindowService(gateway=gateway)),
        capability_surface_profile=PresentationAndPlateSurface(),
    )
    tools = {tool.name: tool for tool in asyncio.run(built.list_tools())}
    stream = tools["openhcs_stream_plate_files_to_viewer"].inputSchema
    assert "display_config" in stream["properties"]
    assert "channel_mode" in next(
        definition["properties"]
        for definition in stream["$defs"].values()
        if definition.get("title") == "NapariDisplayConfig"
    )
    window_schema = tools["openhcs_set_viewer_native_window"].inputSchema
    geometry_fields = next(
        definition["properties"]
        for definition in window_schema["$defs"].values()
        if definition.get("title") == "ViewerNativeWindowGeometry"
    )
    assert set(geometry_fields) == {
        field.name for field in fields(ViewerNativeWindowGeometry)
    }
    connection = ExecutionConnectionSpec(port=6004)
    request = ViewerWindowNativePresentationRequest.from_fields(
        connection=connection,
        presentation=ViewerNativeWindowControlOptions(
            ViewerNativeWindowGeometry(30, 30, 600, 450),
            True,
        ),
    )
    _, structured = asyncio.run(
        built.call_tool(
            "openhcs_set_viewer_native_window",
            request.as_tool_arguments(),
        )
    )
    assert structured["observed"] and structured["applied"]
    assert structured["native_window"]["active"]
    gateway.window.active = False
    _, structured = asyncio.run(
        built.call_tool(
            "openhcs_set_viewer_native_window",
            {"port": 6004, "presentation": {}},
        )
    )
    assert structured["native_window"]["active"] is False  # native, not request mirror
    color = ViewerWindowImageColorRequest.from_fields(
        connection=connection,
        route_key="C3",
        presentation=ViewerNativeImageColorPresentation("green", "additive"),
    )
    _, structured = asyncio.run(
        built.call_tool(
            "openhcs_set_viewer_image_color",
            color.as_tool_arguments(),
        )
    )
    assert structured["native_image_color"] == {
        "colormap": "green",
        "blending": "additive",
    }
    before = len(gateway.calls)
    with pytest.raises(ToolError):
        asyncio.run(
            built.call_tool(
                "openhcs_set_viewer_native_window",
                {
                    "port": 6004,
                    "presentation": {
                        "geometry": {"x": 0, "y": 0, "width": True, "height": 300}
                    },
                },
            )
        )
    assert len(gateway.calls) == before


def test_unavailable_native_endpoint_returns_failure_without_adoption_or_launch():
    class MissingEndpoint(NativePresentationGateway):
        def presentation_control(self, request):
            raise TimeoutError("retained missing endpoint")

    gateway = MissingEndpoint()
    result = ViewerWindowService(gateway=gateway).presentation(
        ViewerWindowNativePresentationRequest.from_fields(
            connection=ExecutionConnectionSpec(port=6004),
            presentation=ViewerNativeWindowControlOptions(focus=True),
        ),
    )
    assert not result.observed and not result.applied and result.native_window is None
    assert "missing endpoint" in result.errors[0].message
    assert gateway.window.focus_calls == []
