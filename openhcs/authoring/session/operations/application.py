"""Operations on the application hosting the session (desktop renderer only)."""

from __future__ import annotations

from openhcs.agent.dto.common import AgentWarning
from openhcs.authoring.session.operations import RendererOperation


class CheckForUpdates(RendererOperation):
    operation_id = "check_for_updates"
    label = "Check for Updates"
    tooltip = "Check the trusted release service for an OpenHCS update"
    description = "Checks for an OpenHCS update and may open an update confirmation."
    side_effects = ("checks_trusted_release_service", "may_open_update_confirmation")


class RestartApplication(RendererOperation):
    operation_id = "restart_session"
    label = "Restart OpenHCS and restore session (reconnect required)"
    tooltip = "Save every dataset and its history, then restart the application"
    description = (
        "Saves all dataset declarations and history and restarts the UI process. "
        "It returns before the old UI exits: rediscover the new UI bridge and "
        "verify restored state."
    )
    side_effects = (
        "saves_all_plate_declarations_and_history",
        "restarts_ui_process",
        "requires_ui_bridge_rediscovery",
    )
    confirmation_required = True
    warnings = (
        AgentWarning(
            code="ui_restart_reconnect_required",
            message=(
                "restart_session returns before the old UI exits. Rediscover the "
                "new UI bridge and verify restored state; the old process's "
                "operation status does not survive the restart."
            ),
        ),
    )


class ExitApplication(RendererOperation):
    operation_id = "exit"
    label = "Exit OpenHCS (disconnect expected)"
    tooltip = "Close the application"
    description = (
        "Runs the main window's close cleanup and exits; the UI bridge disconnects."
    )
    side_effects = (
        "runs_main_window_close_cleanup",
        "exits_ui_process",
        "retires_ui_bridge_descriptor",
    )
    confirmation_required = True
    warnings = (
        AgentWarning(
            code="ui_exit_disconnect_expected",
            message=(
                "exit returns before the UI process and bridge disconnect. Verify "
                "process and descriptor retirement without polling the vanished "
                "bridge."
            ),
        ),
    )
