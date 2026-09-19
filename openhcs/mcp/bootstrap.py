"""Fail-soft bootstrap for the OpenHCS MCP stdio process."""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from dataclasses import dataclass
from enum import Enum
import logging
import os
from pathlib import Path
from typing import TYPE_CHECKING, TypedDict

if TYPE_CHECKING:
    from openhcs.agent.capabilities import LocalCapabilitySurfaceProfile
    from mcp.server.fastmcp import FastMCP


MCP_BOOTSTRAP_SCHEMA_VERSION = "openhcs.mcp.bootstrap.v1"
MCP_BOOTSTRAP_FAILURE_HINT = (
    "The OpenHCS MCP process started, but the full agent server could not be "
    "constructed or run. Fix the startup exception and restart the MCP client."
)
MCP_BOOTSTRAP_SERVER_INSTRUCTIONS = (
    "OpenHCS could not construct its full MCP server. Call openhcs_health_check "
    "or openhcs_bootstrap_failure for the structured startup error, fix the local "
    "installation, and restart this stdio process."
)
MCP_LOCAL_SURFACE_ENVIRONMENT_VARIABLE = "OPENHCS_MCP_LOCAL_SURFACE"
MCP_VERBOSE_ENVIRONMENT_VARIABLE = "OPENHCS_MCP_VERBOSE"
MCP_STABLE_LAUNCH_COMMAND_ENVIRONMENT_VARIABLE = (
    "OPENHCS_MCP_STABLE_LAUNCH_COMMAND_JSON"
)
MCP_INSTALLATION_POINTER_ENVIRONMENT_VARIABLE = "OPENHCS_MCP_INSTALLATION_POINTER"


class McpBootstrapFailurePhase(str, Enum):
    BUILD_SERVER = "build_server"
    RUN_SERVER = "run_server"


@dataclass(frozen=True, slots=True)
class McpBootstrapFailurePayload:
    """Structured startup failure payload exposed over MCP."""

    schema_version: str
    ok: bool
    status: str
    service: str
    phase: McpBootstrapFailurePhase
    exception_type: str
    message: str
    hint: str


class McpBootstrapFailurePayloadWire(TypedDict):
    """FastMCP-compatible wire schema for bootstrap failure payloads."""

    schema_version: str
    ok: bool
    status: str
    service: str
    phase: str
    exception_type: str
    message: str
    hint: str


class McpBootstrapFailurePayloadAuthority:
    """Authoritative projection for MCP bootstrap failure payloads."""

    @staticmethod
    def from_failure(failure: "McpBootstrapFailure") -> McpBootstrapFailurePayload:
        return McpBootstrapFailurePayload(
            schema_version=MCP_BOOTSTRAP_SCHEMA_VERSION,
            ok=False,
            status="unavailable",
            service="openhcs.mcp",
            phase=failure.phase,
            exception_type=failure.exception_type,
            message=failure.message,
            hint=MCP_BOOTSTRAP_FAILURE_HINT,
        )

    @staticmethod
    def as_wire(payload: McpBootstrapFailurePayload) -> McpBootstrapFailurePayloadWire:
        return McpBootstrapFailurePayloadWire(
            schema_version=payload.schema_version,
            ok=payload.ok,
            status=payload.status,
            service=payload.service,
            phase=payload.phase.value,
            exception_type=payload.exception_type,
            message=payload.message,
            hint=payload.hint,
        )


@dataclass(frozen=True, slots=True)
class McpBootstrapFailure:
    """Structured startup failure exposed over MCP instead of closing stdio."""

    phase: McpBootstrapFailurePhase
    exception_type: str
    message: str

    @classmethod
    def from_exception(
        cls,
        exception: BaseException,
        phase: McpBootstrapFailurePhase,
    ) -> "McpBootstrapFailure":
        return cls(
            phase=phase,
            exception_type=type(exception).__name__,
            message=str(exception),
        )

    def payload(self) -> McpBootstrapFailurePayloadWire:
        payload = McpBootstrapFailurePayloadAuthority.from_failure(self)
        return McpBootstrapFailurePayloadAuthority.as_wire(payload)


def build_bootstrap_failure_server(
    exception: BaseException,
    phase: McpBootstrapFailurePhase = McpBootstrapFailurePhase.BUILD_SERVER,
) -> "FastMCP":
    """Build a minimal MCP server that reports startup failure through health."""
    from mcp.server.fastmcp import FastMCP

    failure = McpBootstrapFailure.from_exception(exception, phase)
    server = FastMCP("OpenHCS", instructions=MCP_BOOTSTRAP_SERVER_INSTRUCTIONS)

    @server.tool()
    def openhcs_health_check() -> McpBootstrapFailurePayloadWire:
        """Report why the full OpenHCS MCP server could not start."""
        return failure.payload()

    @server.tool()
    def openhcs_bootstrap_failure() -> McpBootstrapFailurePayloadWire:
        """Return the OpenHCS MCP startup failure payload."""
        return failure.payload()

    return server


def build_bootstrapped_server(
    capability_surface_profile: "LocalCapabilitySurfaceProfile | None" = None,
) -> "FastMCP":
    """Build the full OpenHCS MCP server, or a fail-soft bootstrap server."""
    try:
        from openhcs.agent.capabilities import DesktopLocalCapabilitySurfaceProfile
        from openhcs.mcp.server import build_server

        return build_server(
            capability_surface_profile=(
                DesktopLocalCapabilitySurfaceProfile()
                if capability_surface_profile is None
                else capability_surface_profile
            )
        )
    except Exception as exc:
        return build_bootstrap_failure_server(
            exc, McpBootstrapFailurePhase.BUILD_SERVER
        )


MCP_SERVE_TRANSPORT_ARGUMENT = "--serve"
MCP_SERVE_TRANSPORT_SOCKET = "socket"
MCP_SERVE_TRANSPORT_STDIO = "stdio"
MCP_SOCKET_PATH_ARGUMENT = "--socket-path"
MCP_SOCKET_IDLE_EXIT_ARGUMENT = "--idle-exit-seconds"


def run_bootstrapped_server(
    capability_surface_profile: "LocalCapabilitySurfaceProfile | None" = None,
    *,
    serve_transport: str = MCP_SERVE_TRANSPORT_STDIO,
    socket_path=None,
    idle_exit_seconds: float | None = None,
) -> None:
    """Run the OpenHCS MCP server on the requested transport.

    The stdio transport owns the process protocol channel for exactly one
    session, matching MCP host clients. The socket transport keeps one
    constructed server resident and serves each client connection as an
    independent session, which lets development clients reuse server
    construction across command invocations.
    """

    if serve_transport == MCP_SERVE_TRANSPORT_SOCKET:
        _run_resident_socket_server(
            capability_surface_profile,
            socket_path=socket_path,
            idle_exit_seconds=idle_exit_seconds,
        )
        return
    from openhcs.mcp.stdio import McpStdioTransport

    with McpStdioTransport.reserve_process_stdio() as stdio_transport:
        try:
            server = (
                build_bootstrapped_server()
                if capability_surface_profile is None
                else build_bootstrapped_server(capability_surface_profile)
            )
            stdio_transport.run(server)
        except Exception as exc:
            stdio_transport.run(
                build_bootstrap_failure_server(
                    exc,
                    McpBootstrapFailurePhase.RUN_SERVER,
                )
            )


def _run_resident_socket_server(
    capability_surface_profile: "LocalCapabilitySurfaceProfile | None" = None,
    *,
    socket_path=None,
    idle_exit_seconds: float | None = None,
) -> None:
    """Build the server once and keep serving sessions on a unix socket."""

    from openhcs.mcp.socket import (
        MCP_SOCKET_IDLE_EXIT_SECONDS_DEFAULT,
        McpSocketTransport,
        mcp_dev_socket_path,
    )

    surface_name = (
        capability_surface_profile.name
        if capability_surface_profile is not None
        else "default"
    )
    resolved_socket_path = (
        Path(socket_path)
        if socket_path is not None
        else mcp_dev_socket_path(surface_name)
    )
    transport = McpSocketTransport(
        resolved_socket_path,
        idle_exit_seconds=(
            MCP_SOCKET_IDLE_EXIT_SECONDS_DEFAULT
            if idle_exit_seconds is None
            else idle_exit_seconds
        ),
    )
    try:
        server = (
            build_bootstrapped_server()
            if capability_surface_profile is None
            else build_bootstrapped_server(capability_surface_profile)
        )
    except Exception as exc:
        transport._log(
            "build_failed",
            exception_type=type(exc).__name__,
            message=str(exc),
        )
        raise SystemExit(1) from exc
    transport.serve(server)


def _build_parser() -> argparse.ArgumentParser:
    from openhcs.agent.capabilities import (
        DesktopLocalCapabilitySurfaceProfile,
        LocalCapabilitySurfaceProfile,
    )

    parser = argparse.ArgumentParser(description="Run the OpenHCS MCP stdio server.")
    parser.add_argument(
        "--surface",
        choices=LocalCapabilitySurfaceProfile.names(),
        default=os.environ.get(
            MCP_LOCAL_SURFACE_ENVIRONMENT_VARIABLE,
            DesktopLocalCapabilitySurfaceProfile.name,
        ),
        help=(
            "Capability surface exposed to the MCP client. The default desktop "
            "surface keeps normal UI and viewer workflows while hiding headless, "
            "runtime-server, fallback, and expert-only tools."
        ),
    )
    parser.add_argument(
        MCP_SERVE_TRANSPORT_ARGUMENT,
        choices=(MCP_SERVE_TRANSPORT_STDIO, MCP_SERVE_TRANSPORT_SOCKET),
        default=MCP_SERVE_TRANSPORT_STDIO,
        help=(
            "Protocol transport. stdio serves one session on the process "
            "channel for MCP host clients; socket keeps the constructed "
            "server resident for development clients."
        ),
    )
    parser.add_argument(
        MCP_SOCKET_PATH_ARGUMENT,
        default=None,
        help="Unix socket path for the resident socket transport.",
    )
    parser.add_argument(
        MCP_SOCKET_IDLE_EXIT_ARGUMENT,
        type=float,
        default=None,
        help="Seconds of connection inactivity before the resident server exits.",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> None:
    from openhcs.agent.capabilities import LocalCapabilitySurfaceProfile

    disabled_level = logging.root.manager.disable
    try:
        if os.getenv(MCP_VERBOSE_ENVIRONMENT_VARIABLE) is None:
            logging.disable(logging.INFO)
        args = _build_parser().parse_args(argv)
        idle_exit_seconds = getattr(args, "idle_exit_seconds", None)
        run_bootstrapped_server(
            LocalCapabilitySurfaceProfile.for_name(args.surface),
            serve_transport=args.serve,
            socket_path=getattr(args, "socket_path", None),
            idle_exit_seconds=idle_exit_seconds,
        )
    finally:
        logging.disable(disabled_level)
