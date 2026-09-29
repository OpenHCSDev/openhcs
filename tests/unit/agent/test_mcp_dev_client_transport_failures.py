"""Transport selection stops when a session is handed to its caller."""

from __future__ import annotations

import asyncio
import io
import sys

import pytest

from openhcs.mcp import dev_client_core as client_core


@pytest.mark.parametrize(
    "failure",
    [
        OSError("after dispatch"),
        TimeoutError("after dispatch"),
        client_core.McpDevProtocolError("after dispatch"),
        client_core.McpDevJsonRpcError(
            client_core.McpWireMethod.CALL_TOOL,
            {"code": -32603, "message": "after dispatch"},
        ),
    ],
)
def test_established_session_propagates_body_failure_without_fallback(
    monkeypatch,
    tmp_path,
    failure,
) -> None:
    transitions = []

    class ConnectedSocketSession:
        def __init__(self, server_spec, server_stderr, socket_path):
            self.server_spec = server_spec

        async def __aenter__(self):
            transitions.append("connected")
            return self

        async def initialize(self, *, timeout_seconds):
            transitions.append("initialized")

        async def __aexit__(self, exc_type, exc_value, traceback):
            transitions.append(("closed", exc_value))

    def forbidden_fallback(*args, **kwargs):
        pytest.fail("Established-session failure attempted transport fallback")

    monkeypatch.setattr(client_core, "McpDevSocketSession", ConnectedSocketSession)
    monkeypatch.setattr(client_core, "McpDevStdioSession", forbidden_fallback)
    monkeypatch.setattr(
        client_core.McpDevTransportAuthority,
        "spawn_resident_server",
        forbidden_fallback,
    )
    from openhcs.mcp import socket as socket_transport

    monkeypatch.setattr(
        socket_transport,
        "mcp_dev_socket_path",
        lambda profile: tmp_path / "session.sock",
    )
    monkeypatch.setattr(socket_transport, "probe_socket_alive", lambda path: True)

    async def journey():
        async with client_core.open_mcp_dev_session(
            client_core.McpDevServerSpec(sys.executable),
            io.StringIO(),
            initialize_timeout_seconds=1.0,
            use_resident_server=True,
        ):
            transitions.append("dispatched")
            raise failure

    with pytest.raises(type(failure)) as raised:
        asyncio.run(journey())
    assert raised.value is failure
    assert transitions == [
        "connected",
        "initialized",
        "dispatched",
        ("closed", failure),
    ]


def test_failed_initialization_can_select_stdio_before_dispatch(
    monkeypatch,
    tmp_path,
) -> None:
    transitions = []
    failure = OSError("initialization failed")

    class SocketSession:
        def __init__(self, server_spec, server_stderr, socket_path):
            self.server_spec = server_spec

        async def __aenter__(self):
            return self

        async def initialize(self, *, timeout_seconds):
            transitions.append("socket initialize")
            raise failure

        async def __aexit__(self, exc_type, exc_value, traceback):
            transitions.append(("socket closed", exc_value))

    class StdioSession:
        async def __aenter__(self):
            return self

        async def initialize(self, *, timeout_seconds):
            transitions.append("stdio initialize")

        async def __aexit__(self, exc_type, exc_value, traceback):
            transitions.append("stdio closed")

    from openhcs.mcp import socket as socket_transport

    monkeypatch.setattr(client_core, "McpDevSocketSession", SocketSession)
    monkeypatch.setattr(
        socket_transport,
        "mcp_dev_socket_path",
        lambda profile: tmp_path / "session.sock",
    )
    monkeypatch.setattr(socket_transport, "probe_socket_alive", lambda path: True)
    monkeypatch.setattr(
        client_core.McpDevTransportAuthority, "recent_spawn_failure", lambda path: True
    )
    monkeypatch.setattr(
        client_core.McpDevTransportAuthority, "clear_spawn_failure", lambda path: None
    )

    async def journey():
        async with client_core.open_mcp_dev_session(
            client_core.McpDevServerSpec(sys.executable),
            io.StringIO(),
            initialize_timeout_seconds=1.0,
            use_resident_server=True,
            stdio_session_factory=StdioSession,
        ) as session:
            assert isinstance(session, StdioSession)
            transitions.append("dispatched")

    asyncio.run(journey())
    assert transitions == [
        "socket initialize",
        ("socket closed", failure),
        "stdio initialize",
        "dispatched",
        "stdio closed",
    ]
