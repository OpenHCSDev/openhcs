"""Continuous progress journeys through the real generated server and wire."""

import asyncio
import io
import socket
import sys
import threading
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace

import pytest

import openhcs
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.functions import FunctionCatalogPage
from openhcs.mcp.dev_client_core import (
    McpDevServerSpec,
    McpDevSocketSession,
    McpDevStdioSession,
)
from openhcs.mcp.server import build_server
from openhcs.mcp.socket import McpSocketTransport


class ControlledCatalog:
    """Only the underlying work is controlled, never the MCP/progress path."""

    def search(self, *, query, **kwargs):
        del kwargs
        if query != "warm":
            EndpointStartupStatus(
                EndpointStartupPhase.PREPARING_CAPABILITIES,
                "Controlled cold preparation",
            ).publish()
            threading.Event().wait(2.4)
        if query == "failed":
            raise ValueError("Original controlled failure")
        return FunctionCatalogPage(SCHEMA_VERSION, query, (), 0, 50)


@dataclass(frozen=True, slots=True)
class ProgressServerSpec(McpDevServerSpec):
    def process_args(self):
        # Select the same source/wheel as the caller, rather than another checkout.
        module = Path(__file__).resolve()
        import_root = Path(openhcs.__file__).resolve().parent.parent
        return (
            "-c",
            f"import sys, runpy; sys.path.insert(0, {str(import_root)!r}); "
            f"runpy.run_path({str(module)!r}, run_name='__main__')",
        )


async def exercise_progress_journey(session):
    await session.initialize(timeout_seconds=10.0)
    tools = await session.list_tools(timeout_seconds=5.0)
    assert any(tool["name"] == "openhcs_search_functions" for tool in tools)
    results = []
    for query in ("cold", "failed", "warm"):
        started = asyncio.get_running_loop().time()
        result = await session.call_tool(
            "openhcs_search_functions", {"query": query}, timeout_seconds=1.6
        )
        elapsed = asyncio.get_running_loop().time() - started
        if query != "warm":
            assert elapsed >= 2.4, "Total work must exceed the idle timeout"
        results.append(result)
    assert results[0]["structuredContent"]["revision"] == "cold"
    assert "Original controlled failure" in str(results[1])
    assert results[2]["structuredContent"]["revision"] == "warm"


def test_generated_server_progress_keeps_real_stdio_session_alive(tmp_path):
    async def exercise():
        with (tmp_path / "stdio.log").open("w+") as diagnostics:
            async with McpDevStdioSession(
                ProgressServerSpec(sys.executable), diagnostics
            ) as session:
                await exercise_progress_journey(session)
                process = session.require_process()
                assert process.returncode is None
            assert process.returncode is not None
            diagnostics.seek(0)
            output = diagnostics.read()
            assert "preparing_capabilities: Controlled cold preparation" in output
            assert "still running" in output

    asyncio.run(exercise())


@pytest.mark.skipif(not hasattr(socket, "AF_UNIX"), reason="Local Unix transport")
def test_generated_server_progress_keeps_real_socket_session_alive(tmp_path):
    async def exercise():
        server_socket, client_socket = socket.socketpair()
        client_socket.setblocking(False)
        transport = McpSocketTransport(tmp_path / "controlled.sock")
        server = build_server(SimpleNamespace(function_catalog=ControlledCatalog()))
        server_task = asyncio.create_task(transport._run_session(server, server_socket))
        diagnostics = io.StringIO()
        session = McpDevSocketSession(
            McpDevServerSpec(sys.executable), diagnostics, tmp_path / "controlled.sock"
        )
        try:
            session._reader, session._writer = await asyncio.open_connection(
                sock=client_socket
            )
            await exercise_progress_journey(session)
        finally:
            await session.__aexit__(None, None, None)
            await asyncio.wait_for(server_task, 2.0)
            server_socket.close()
            client_socket.close()
        assert (
            "preparing_capabilities: Controlled cold preparation"
            in diagnostics.getvalue()
        )
        assert "still running" in diagnostics.getvalue()

    asyncio.run(exercise())


if __name__ == "__main__":
    from openhcs.mcp.stdio import McpStdioTransport

    with McpStdioTransport.reserve_process_stdio() as transport:
        transport.run(
            build_server(SimpleNamespace(function_catalog=ControlledCatalog()))
        )
