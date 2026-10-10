"""One control-action family for every viewer server."""

from __future__ import annotations

from types import SimpleNamespace

import pytest
from zmqruntime.messages import EndpointControlCapability

from openhcs.core.streaming_config_factory import ViewerProcessLaunchConfig
from openhcs.runtime.viewer_control_actions import (
    LifecycleControlAction,
    ViewerServerPort,
)
from openhcs.runtime.viewer_protocol import (
    ViewerControlMessageType,
    ViewerControlResponse,
    ViewerSettleProgress,
)

pytest.importorskip("napari")

from openhcs.runtime.fiji_viewer_server import (  # noqa: E402
    FijiBatchSettlementState,
    FijiViewerServer,
    FijiWindowRegistry,
)
from openhcs.runtime.napari_viewer_server import NapariViewerServer  # noqa: E402

VIEWER_SERVERS = (NapariViewerServer, FijiViewerServer)


@pytest.mark.parametrize("server_type", VIEWER_SERVERS)
def test_every_viewer_inherits_every_lifecycle_action(server_type) -> None:
    actions = server_type.control_actions

    assert issubclass(server_type, ViewerServerPort)
    for lifecycle in LifecycleControlAction.declared():
        assert lifecycle.message_type in actions.registered_message_types()
        assert isinstance(actions.for_message_type(lifecycle.message_type), lifecycle)
    assert actions.control_capabilities() == frozenset(EndpointControlCapability)


@pytest.mark.parametrize("server_type", VIEWER_SERVERS)
@pytest.mark.parametrize(
    "message_type",
    (ViewerControlMessageType.NAVIGATE.value, "no_such_message", None),
)
def test_unregistered_control_messages_answer_error(server_type, message_type) -> None:
    actions = server_type.control_actions
    if message_type in actions.registered_message_types():
        pytest.skip(f"{server_type.__name__} handles {message_type!r}")
    server = object.__new__(server_type)

    reply = server.handle_control_message({"type": message_type})

    assert reply["status"] == "error"
    assert reply["type"] == "error"
    assert server.viewer_display_name in reply["message"]


def test_fiji_navigate_no_longer_reports_success() -> None:
    """MCP navigate/viewport/measure sent to Fiji used to succeed silently."""

    server = object.__new__(FijiViewerServer)
    for message_type in (
        ViewerControlMessageType.NAVIGATE,
        ViewerControlMessageType.VIEWPORT,
        ViewerControlMessageType.STATE,
        ViewerControlMessageType.APPLY_INTENSITY_WINDOW,
    ):
        assert server.handle_control_message({"type": message_type.value})["status"] == (
            "error"
        )


def test_fiji_lifecycle_actions_answer_through_the_server_port() -> None:
    launch = ViewerProcessLaunchConfig(listen_host="*")
    server = object.__new__(FijiViewerServer)
    server.windows = FijiWindowRegistry()
    server.batch_processor = SimpleNamespace(settlement=FijiBatchSettlementState())
    server.launch_config = SimpleNamespace(process_launch=launch)
    server._shutdown_requested = False

    process = server.handle_control_message({"type": "process_launch"})
    settle = server.handle_control_message({"type": "settle"})
    shutdown = server.handle_control_message({"type": "shutdown"})

    assert process["type"] == "process_launch_ack"
    assert ViewerProcessLaunchConfig.from_wire_mapping(process["process_launch"]) == launch
    assert ViewerSettleProgress.from_response(ViewerControlResponse(settle)) == (
        ViewerSettleProgress.complete()
    )
    assert shutdown["type"] == "shutdown_ack"
    assert server._shutdown_requested is True
