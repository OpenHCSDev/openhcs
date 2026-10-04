"""MCP boundary DTOs for the headless OpenHCS agent API."""

from __future__ import annotations

from dataclasses import dataclass

from openhcs.agent.dto.common import AgentError, AgentTimedStatusEnvelope


@dataclass(frozen=True, slots=True)
class McpToolErrorResult:
    """The failed tool boundary, shared by its producer and wire consumer."""

    schema_version: str
    ok: bool
    tool: str
    errors: tuple[AgentError, ...]

    def __post_init__(self) -> None:
        if self.ok or not self.errors:
            raise ValueError("An MCP tool failure requires ok=False and its cause.")


@dataclass(frozen=True, slots=True)
class McpServerStaleErrorResult(McpToolErrorResult):
    """Failed boundary with the original stale-process recovery evidence."""

    server_process_id: int
    server_started_at_unix: float
    stale_source_paths: tuple[str, ...]
    recovery_reason: str
    installation_pointer_path: str | None
    installation_pointer_changed_since_import: bool
    installation_pointer_available: bool | None
    restart_required: bool
    restart_command: tuple[str, ...]
    restart_command_is_stable: bool
    reconnect_required: bool
    reconnect_owner: str | None
    retry_after_reconnect: bool
    automatic_recovery_on_reconnect: bool
    restart_hint: str


McpBoundaryFailure = McpToolErrorResult | McpServerStaleErrorResult


@dataclass(frozen=True, slots=True)
class McpServerHealthResult(AgentTimedStatusEnvelope):
    """Health payload returned by the OpenHCS MCP transport boundary."""

    service: str
    openhcs_version: str
    packaged_resources_ready: bool
    packaged_resource_count: int
    missing_packaged_resource_paths: tuple[str, ...]
    server_process_id: int
    server_source_path: str
    server_import_mtime_ns: int
    server_current_mtime_ns: int | None
    server_source_changed_since_import: bool
    stale_source_paths: tuple[str, ...]
    recovery_reason: str
    installation_pointer_path: str | None
    installation_pointer_changed_since_import: bool
    installation_pointer_available: bool | None
    restart_required: bool
    restart_command: tuple[str, ...]
    restart_command_is_stable: bool
    reconnect_required: bool
    reconnect_owner: str | None
    retry_after_reconnect: bool
    automatic_recovery_on_reconnect: bool
    restart_hint: str | None
