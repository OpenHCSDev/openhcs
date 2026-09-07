"""Process-level channel ownership for the OpenHCS MCP stdio transport."""

from __future__ import annotations

import os
import sys
from collections.abc import Iterator
from contextlib import contextmanager
from io import TextIOWrapper
from typing import TYPE_CHECKING

import anyio
from mcp.server.stdio import stdio_server

if TYPE_CHECKING:
    from mcp.server.fastmcp import FastMCP


class McpStdioTransport:
    """Reserve protocol channels and isolate application standard I/O.

    MCP stdio assigns stdout exclusively to JSON-RPC. Libraries imported by an
    OpenHCS capability may write through either ``sys.stdout`` or file
    descriptor 1, including from background work that outlives the initiating
    call. The transport therefore owns the process channel for its entire
    lifetime rather than asking individual services to redirect output.

    Application stdin is empty. In particular, native runtimes initializing
    after the handshake can inspect descriptor 0 without contending with the
    protocol reader's pending pipe read on Windows.
    """

    def __init__(
        self,
        protocol_stdin: TextIOWrapper,
        protocol_stdout: TextIOWrapper,
    ) -> None:
        self._protocol_stdin = protocol_stdin
        self._protocol_stdout = protocol_stdout

    @classmethod
    @contextmanager
    def reserve_process_stdio(cls) -> Iterator[McpStdioTransport]:
        """Reserve the protocol descriptors before server construction."""

        process_stdin = sys.stdin
        process_stdout = sys.stdout
        stdin_fd = process_stdin.fileno()
        stdout_fd = process_stdout.fileno()
        stderr_fd = sys.stderr.fileno()
        process_stdout.flush()
        sys.stderr.flush()

        with (
            os.fdopen(os.dup(stdin_fd), "rb", buffering=0) as protocol_input,
            os.fdopen(os.dup(stdout_fd), "wb", buffering=0) as protocol_output,
            open(os.devnull, "r", encoding="utf-8") as application_stdin,
            TextIOWrapper(
                protocol_input,
                encoding="utf-8",
                errors="replace",
            ) as protocol_stdin,
            TextIOWrapper(
                protocol_output,
                encoding="utf-8",
                errors="strict",
                write_through=True,
            ) as protocol_stdout,
        ):
            try:
                os.dup2(application_stdin.fileno(), stdin_fd)
                os.dup2(stderr_fd, stdout_fd)
                sys.stdin = application_stdin
                sys.stdout = sys.stderr
                yield cls(protocol_stdin, protocol_stdout)
            finally:
                try:
                    sys.stdout.flush()
                    protocol_stdout.flush()
                finally:
                    sys.stdin = process_stdin
                    sys.stdout = process_stdout
                    try:
                        os.dup2(protocol_stdin.fileno(), stdin_fd)
                    finally:
                        os.dup2(protocol_stdout.fileno(), stdout_fd)

    def run(self, server: FastMCP) -> None:
        """Run one FastMCP server against the reserved protocol channel."""

        anyio.run(self._run, server)

    async def _run(self, server: FastMCP) -> None:
        async_stdin = anyio.wrap_file(self._protocol_stdin)
        async_stdout = anyio.wrap_file(self._protocol_stdout)
        async with stdio_server(stdin=async_stdin, stdout=async_stdout) as (
            read_stream,
            write_stream,
        ):
            await server._mcp_server.run(
                read_stream,
                write_stream,
                server._mcp_server.create_initialization_options(),
            )
