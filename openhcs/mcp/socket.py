"""Resident unix-socket transport for the OpenHCS MCP server.

The stdio transport serves exactly one MCP session per process because the
protocol contract assigns stdout to a single client. Development clients
invoking one command per process otherwise pay the full server construction
cost for every call. This transport keeps one constructed server resident and
serves each client connection as an independent MCP session over a private
unix socket, so repeated development calls reuse construction without changing
the wire protocol: every connection still performs the standard MCP
initialize handshake and JSON-RPC exchange.
"""

from __future__ import annotations

import hashlib
import io
import os
import socket
import threading
import time
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from mcp.server.fastmcp import FastMCP

MCP_SOCKET_DIRECTORY_ENVIRONMENT_VARIABLE = "OPENHCS_MCP_SOCKET_DIRECTORY"
MCP_SOCKET_IDLE_EXIT_SECONDS_DEFAULT = 1800.0
MCP_SOCKET_CONNECT_PROBE_TIMEOUT_SECONDS = 0.5
MCP_SOCKET_SESSION_LOG_FILE_NAME = "openhcs-mcp-daemon.log"


def mcp_socket_directory() -> Path:
    """Return the directory owning OpenHCS unix IPC sockets.

    Reuses the execution transport IPC directory convention
    (``~/.openhcs/ipc``) so every OpenHCS local socket lives in one place.
    """

    from openhcs.runtime.zmq_config import OpenHCSZMQConfig

    configured = os.getenv(MCP_SOCKET_DIRECTORY_ENVIRONMENT_VARIABLE)
    if configured:
        return Path(configured)
    config = OpenHCSZMQConfig()
    return Path.home() / f".{config.app_name}" / config.ipc_socket_dir


def mcp_dev_socket_path(surface_name: str) -> Path:
    """Return the resident-server socket path for one surface and checkout.

    The path binds the resolved OpenHCS import root so a resident server
    loaded from one checkout is never reused against different sources.
    """

    from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority

    source_root = OpenHCSRuntimeImportAuthority.current().import_root
    source_token = hashlib.sha256(str(source_root).encode()).hexdigest()[:8]
    directory = mcp_socket_directory()
    return directory / f"openhcs-mcp-{surface_name}-{source_token}.sock"


def probe_socket_alive(
    socket_path: Path,
    *,
    timeout_seconds: float = MCP_SOCKET_CONNECT_PROBE_TIMEOUT_SECONDS,
) -> bool:
    """Return whether a resident server answers on the socket path."""

    if not socket_path.exists():
        return False
    try:
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as probe:
            probe.settimeout(timeout_seconds)
            probe.connect(str(socket_path))
        return True
    except OSError:
        return False


class McpSocketTransport:
    """Own the resident unix-socket channel for one constructed MCP server."""

    listen_backlog = 8

    def __init__(
        self,
        socket_path: Path,
        *,
        idle_exit_seconds: float = MCP_SOCKET_IDLE_EXIT_SECONDS_DEFAULT,
        log_file_path: Path | None = None,
    ) -> None:
        self.socket_path = socket_path
        self.idle_exit_seconds = idle_exit_seconds
        self.log_file_path = (
            log_file_path
            if log_file_path is not None
            else socket_path.parent / MCP_SOCKET_SESSION_LOG_FILE_NAME
        )
        self._last_activity = time.monotonic()
        self._stop = threading.Event()
        self._listener: socket.socket | None = None

    def serve(self, server: "FastMCP") -> None:
        """Accept client connections and serve one MCP session per connection."""

        directory = self.socket_path.parent
        directory.mkdir(parents=True, exist_ok=True)
        if self.socket_path.exists():
            if probe_socket_alive(self.socket_path):
                raise RuntimeError(
                    f"A resident MCP server already serves {self.socket_path}."
                )
            self.socket_path.unlink()
        self._log("serving", surface_socket=str(self.socket_path))
        watchdog = threading.Thread(target=self._watch_idle, daemon=True)
        watchdog.start()
        listener = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self._listener = listener
        try:
            listener.bind(str(self.socket_path))
            listener.listen(self.listen_backlog)
            while not self._stop.is_set():
                listener.settimeout(0.5)
                try:
                    connection, _ = listener.accept()
                except (socket.timeout, TimeoutError):
                    continue
                except OSError:
                    if self._stop.is_set():
                        break
                    raise
                self._last_activity = time.monotonic()
                try:
                    self._serve_connection(server, connection)
                except BaseException as exc:  # session failures must not end residency
                    if isinstance(exc, (KeyboardInterrupt, SystemExit)):
                        raise
                    self._log_session_failure(exc)
                finally:
                    connection.close()
                    self._last_activity = time.monotonic()
        finally:
            self._listener = None
            listener.close()
            try:
                self.socket_path.unlink()
            except FileNotFoundError:
                pass
            self._stop.set()
            self._log("stopped")

    def _serve_connection(self, server: "FastMCP", connection: socket.socket) -> None:
        import anyio

        anyio.run(self._run_session, server, connection)

    async def _run_session(self, server: "FastMCP", connection: socket.socket) -> None:
        import anyio
        from mcp.server.stdio import stdio_server

        # stdio_server exchanges UTF-8 text lines, exactly like the process
        # stdio transport: wrap the socket in text streams before handing
        # them to the protocol server.
        connection_file = connection.makefile("rwb", buffering=0)
        protocol_stdin = io.TextIOWrapper(
            connection_file, encoding="utf-8", errors="replace"
        )
        protocol_stdout = io.TextIOWrapper(
            connection_file, encoding="utf-8", write_through=True
        )
        async with stdio_server(
            stdin=anyio.wrap_file(protocol_stdin),
            stdout=anyio.wrap_file(protocol_stdout),
        ) as (read_stream, write_stream):
            await server._mcp_server.run(
                read_stream,
                write_stream,
                server._mcp_server.create_initialization_options(),
            )

    def _log_session_failure(self, exc: BaseException) -> None:
        import traceback

        try:
            self.log_file_path.parent.mkdir(parents=True, exist_ok=True)
            timestamp = time.strftime("%Y-%m-%dT%H:%M:%S")
            with self.log_file_path.open("a", encoding="utf-8") as log_file:
                log_file.write(f"{timestamp} session_failed\n")
                traceback.print_exception(
                    type(exc), exc, exc.__traceback__, file=log_file
                )
        except OSError:
            pass

    def _watch_idle(self) -> None:
        while not self._stop.wait(5.0):
            idle_seconds = time.monotonic() - self._last_activity
            if idle_seconds >= self.idle_exit_seconds:
                self._log("idle_exit", idle_seconds=round(idle_seconds, 1))
                # Close the listener so the accept loop unwinds through its
                # finally block (socket unlink) instead of exiting abruptly.
                self._stop.set()
                listener = self._listener
                if listener is not None:
                    listener.close()
                return

    def _log(self, event: str, **fields: float | str) -> None:
        try:
            self.log_file_path.parent.mkdir(parents=True, exist_ok=True)
            timestamp = time.strftime("%Y-%m-%dT%H:%M:%S")
            rendered = " ".join(f"{key}={value}" for key, value in fields.items())
            with self.log_file_path.open("a", encoding="utf-8") as log_file:
                log_file.write(f"{timestamp} {event} {rendered}\n")
        except OSError:
            pass


def wait_for_socket(
    socket_path: Path,
    *,
    timeout_seconds: float,
) -> bool:
    """Wait until a resident server answers on the socket path."""

    deadline = time.monotonic() + timeout_seconds
    while time.monotonic() < deadline:
        if probe_socket_alive(socket_path):
            return True
        time.sleep(0.1)
    return False
