import asyncio
import json
import subprocess
import sys
from pathlib import Path

import pytest
from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


def test_stdio_transport_reserves_protocol_stdout_for_persistent_session(
    tmp_path: Path,
) -> None:
    server_script = tmp_path / "noisy_mcp_server.py"
    server_script.write_text(
        """\
import os

from mcp.server.fastmcp import FastMCP

from openhcs.mcp.stdio import McpStdioTransport


server = FastMCP("noisy-test")


@server.tool()
def emit_noise() -> dict[str, bool]:
    print("python stdout noise", flush=True)
    os.write(1, b"native stdout noise\\n")
    return {"ok": True}


@server.tool()
def health() -> dict[str, bool]:
    return {"ok": True}


with McpStdioTransport.reserve_process_stdio() as transport:
    transport.run(server)
""",
        encoding="utf-8",
    )
    stderr_path = tmp_path / "server.stderr.log"

    async def call_persistent_server() -> tuple[object, object]:
        parameters = StdioServerParameters(
            command=sys.executable,
            args=(str(server_script),),
        )
        with stderr_path.open("w", encoding="utf-8") as stderr:
            async with stdio_client(parameters, errlog=stderr) as (
                read_stream,
                write_stream,
            ):
                async with ClientSession(read_stream, write_stream) as session:
                    await asyncio.wait_for(session.initialize(), timeout=5)
                    noisy = await asyncio.wait_for(
                        session.call_tool("emit_noise", {}),
                        timeout=5,
                    )
                    healthy = await asyncio.wait_for(
                        session.call_tool("health", {}),
                        timeout=5,
                    )
                    return noisy, healthy

    noisy, healthy = asyncio.run(call_persistent_server())

    assert noisy.structuredContent == {"ok": True}
    assert healthy.structuredContent == {"ok": True}
    stderr_text = stderr_path.read_text(encoding="utf-8")
    assert "python stdout noise" in stderr_text
    assert "native stdout noise" in stderr_text
    assert not any(
        line.startswith("{") and json.loads(line).get("jsonrpc") == "2.0"
        for line in stderr_text.splitlines()
    )


@pytest.mark.parametrize("module_name", ["numpy", "scipy.linalg"])
def test_stdio_transport_allows_cold_native_import_after_handshake(
    tmp_path: Path,
    module_name: str,
) -> None:
    """Import while the real transport is already waiting for the next request."""
    server_script = tmp_path / "cold_native_mcp_server.py"
    server_script.write_text(
        """\
import asyncio
import importlib
import sys

from mcp.server.fastmcp import FastMCP
from openhcs.mcp.stdio import McpStdioTransport

server = FastMCP("cold-native-test")

@server.tool()
async def import_native(module_name: str) -> dict[str, bool]:
    assert module_name not in sys.modules, "Native import must actually be cold"
    # Let the protocol reader begin its next blocking pipe read first.
    await asyncio.sleep(0.2)
    module = await asyncio.to_thread(importlib.import_module, module_name)
    return {"imported": module.__name__ == module_name}

with McpStdioTransport.reserve_process_stdio() as transport:
    transport.run(server)
""",
        encoding="utf-8",
    )

    async def import_after_handshake():
        parameters = StdioServerParameters(
            command=sys.executable,
            args=(str(server_script),),
        )
        with (tmp_path / "native.stderr.log").open("w", encoding="utf-8") as stderr:
            async with stdio_client(parameters, errlog=stderr) as (reader, writer):
                async with ClientSession(reader, writer) as session:
                    await asyncio.wait_for(session.initialize(), timeout=10)
                    # No ping or second request may release a blocked native import.
                    return await asyncio.wait_for(
                        session.call_tool(
                            "import_native", {"module_name": module_name}
                        ),
                        timeout=20,
                    )

    result = asyncio.run(import_after_handshake())
    assert not result.isError
    assert result.structuredContent == {"imported": True}


@pytest.mark.parametrize("fail_inside", [False, True])
def test_stdio_channel_reservation_restores_process_handles(fail_inside: bool) -> None:
    script = """\
import os
import sys
from openhcs.mcp.stdio import McpStdioTransport

original_streams = (sys.stdin, sys.stdout)
original_files = (os.fstat(0), os.fstat(1))
try:
    with McpStdioTransport.reserve_process_stdio() as transport:
        assert sys.stdin.read() == ""
        assert os.read(0, 1) == b""
        assert transport._protocol_stdin.readline() == "protocol input\\n"
        if sys.platform == "win32":
            import ctypes
            import msvcrt
            kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
            kernel32.GetStdHandle.argtypes = (ctypes.c_uint32,)
            kernel32.GetStdHandle.restype = ctypes.c_void_p
            assert kernel32.GetStdHandle(-10) == msvcrt.get_osfhandle(0)
        print("application diagnostic", flush=True)
        transport._protocol_stdout.write("protocol output\\n")
        if sys.argv[1] == "True":
            raise ValueError("expected failure")
except ValueError as exc:
    assert str(exc) == "expected failure"
assert (sys.stdin, sys.stdout) == original_streams
assert all(
    os.path.samestat(os.fstat(fd), original)
    for fd, original in enumerate(original_files)
)
print("restored", flush=True)
"""
    completed = subprocess.run(
        [sys.executable, "-c", script, str(fail_inside)],
        input="protocol input\n",
        capture_output=True,
        text=True,
        timeout=10,
    )
    assert completed.returncode == 0, completed.stderr
    assert completed.stdout == "protocol output\nrestored\n"
    assert completed.stderr == "application diagnostic\n"


def test_stdio_stdout_restoration_survives_stdin_restoration_failure() -> None:
    script = """\
import os
import sys
from unittest.mock import patch
from openhcs.mcp.stdio import McpStdioTransport

original_streams = (sys.stdin, sys.stdout)
original_stdout = os.fstat(1)
restore_started = False
restore_targets = []
real_dup2 = os.dup2

def fail_stdin_restoration(source, target):
    if restore_started:
        restore_targets.append(target)
        if target == 0:
            raise OSError("expected stdin restoration failure")
    return real_dup2(source, target)

try:
    with patch("os.dup2", fail_stdin_restoration):
        with McpStdioTransport.reserve_process_stdio():
            restore_started = True
except OSError as exc:
    assert str(exc) == "expected stdin restoration failure"
else:
    raise AssertionError("The restoration failure must remain visible")

assert restore_targets == [0, 1]
assert (sys.stdin, sys.stdout) == original_streams
assert os.path.samestat(os.fstat(1), original_stdout)
print("stdout restored", flush=True)
"""
    completed = subprocess.run(
        [sys.executable, "-c", script],
        input="",
        capture_output=True,
        text=True,
        timeout=10,
    )
    assert completed.returncode == 0, completed.stderr
    assert completed.stdout == "stdout restored\n"
    assert completed.stderr == ""
