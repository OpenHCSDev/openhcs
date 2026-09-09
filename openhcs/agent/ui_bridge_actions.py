"""Agent-facing UI bridge action declarations."""

from __future__ import annotations

from enum import Enum
from collections.abc import Callable
from typing import TYPE_CHECKING

from zmqruntime.startup import EndpointStartupPresentationTarget, EndpointStartupStatus
from openhcs.agent.dto.common import AgentError, AgentWarning

if TYPE_CHECKING:
    from openhcs.pyqt_gui.main import OpenHCSMainWindow
    from openhcs.pyqt_gui.widgets.plate_manager import PlateManagerWidget
    from openhcs.pyqt_gui.widgets.shared.services.widget_action_dispatch import (
        WidgetActionCallable,
    )


class PlateOperation(str, Enum):
    """Closed set of batch operations that validate visible plate rows."""

    INIT = "init"
    COMPILE = "compile"
    RUN = "run"


class ManagerButtonPresentationMixin:
    """Project an action declaration into the generic manager-button contract."""

    value: str
    label: str
    tooltip: str

    @property
    def button_config(self) -> tuple[str, str, str]:
        return self.label, self.value, self.tooltip


class MainWindowAction(str, Enum):
    """Closed set of agent-facing main-window actions."""

    title: str
    side_effects: tuple[str, ...]
    confirmation_required: bool
    enabled_for: Callable[[OpenHCSMainWindow], bool]
    invoke_on: Callable[[OpenHCSMainWindow], None]
    unavailable_error: AgentError
    warnings: tuple[AgentWarning, ...]

    def __new__(
        cls,
        value: str,
        title: str,
        side_effects: tuple[str, ...],
        confirmation_required: bool,
        enabled_for: Callable[[OpenHCSMainWindow], bool],
        invoke_on: Callable[[OpenHCSMainWindow], None],
        unavailable_error: AgentError,
        warnings: tuple[AgentWarning, ...] = (),
    ) -> "MainWindowAction":
        member = str.__new__(cls, value)
        member._value_ = value
        member.title = title
        member.side_effects = side_effects
        member.confirmation_required = confirmation_required
        member.enabled_for = enabled_for
        member.invoke_on = invoke_on
        member.unavailable_error = unavailable_error
        member.warnings = warnings
        return member

    CHECK_FOR_UPDATES = (
        "check_for_updates",
        "Check for Updates",
        ("checks_trusted_release_service", "may_open_update_confirmation"),
        False,
        lambda window: window.check_for_updates_action.isEnabled(),
        lambda window: window.check_for_updates(),
        AgentError(
            code="update_check_in_progress",
            message="An OpenHCS update check is already in progress.",
        ),
    )
    RESTART_SESSION = (
        "restart_session",
        "Restart OpenHCS and restore session (reconnect required)",
        (
            "saves_all_plate_declarations_and_history",
            "restarts_ui_process",
            "requires_ui_bridge_rediscovery",
        ),
        True,
        lambda window: window.session_restart_available(),
        lambda window: window.restart_session(),
        AgentError(
            code="session_restart_unavailable",
            message="Finish plate initialization, compilation and execution, and recover any pending restart first.",
        ),
        (
            AgentWarning(
                code="ui_restart_reconnect_required",
                message="restart_session returns an accepted receipt before the old UI exits. Rediscover the new UI bridge and verify restored state; the old process's operation receipt is not persistent across restart.",
            ),
        ),
    )


class PlateManagerAction(ManagerButtonPresentationMixin, str, Enum):
    """Closed set of PlateManager button actions and agent-facing semantics."""

    side_effects: tuple[str, ...]
    confirmation_required: bool
    plate_operation: PlateOperation | None

    def __new__(
        cls,
        value: str,
        label: str,
        tooltip: str,
        side_effects: tuple[str, ...],
        confirmation_required: bool,
        plate_operation: PlateOperation | None,
        handler: Callable[[PlateManagerWidget], WidgetActionCallable],
        has_button: bool = True,
        resolver: Callable[
            [PlateManagerAction, PlateManagerWidget], PlateManagerAction
        ] = lambda action, manager: action,
        selection_enabled: Callable[[bool], bool] = lambda initialized: initialized,
    ) -> "PlateManagerAction":
        member = str.__new__(cls, value)
        member._value_ = value
        member.label = label
        member.tooltip = tooltip
        member.side_effects = side_effects
        member.confirmation_required = confirmation_required
        member.plate_operation = plate_operation
        member.handler = handler
        member.has_button = has_button
        member.resolver = resolver
        member.selection_enabled = selection_enabled
        return member

    def resolved(self, manager: "PlateManagerWidget") -> "PlateManagerAction":
        return self.resolver(self, manager)

    def resolve_callable(self, manager: "PlateManagerWidget") -> "WidgetActionCallable":
        return self.resolved(manager).handler(manager)

    ADD_PLATE = (
        "add_plate",
        "Add",
        "Add new plate directory",
        ("opens_file_dialog", "mutates_plate_collection"),
        True,
        None,
        lambda widget: widget.action_add,
    )
    DELETE_PLATE = (
        "del_plate",
        "Del",
        "Delete selected plates",
        ("mutates_plate_collection",),
        True,
        None,
        lambda widget: widget.action_delete,
    )
    EDIT_CONFIG = (
        "edit_config",
        "Edit",
        "Edit plate configuration",
        ("opens_config_window", "may_mutate_plate_config"),
        True,
        None,
        lambda widget: widget.action_edit_config,
    )
    INIT_PLATE = (
        "init_plate",
        "Init",
        "Initialize selected plates",
        ("starts_initialization_workflow",),
        True,
        PlateOperation.INIT,
        lambda widget: widget.action_init_plate,
    )
    COMPILE_PLATE = (
        "compile_plate",
        "Compile",
        "Compile plate pipelines",
        ("starts_compile_workflow",),
        True,
        PlateOperation.COMPILE,
        lambda widget: widget.action_compile_plate,
        True,
        lambda action, widget: widget.compilation_action,
    )
    CONNECT_SERVER = (
        "connect_server",
        "Connect",
        "Connect to the execution server, starting it if needed",
        ("connects_or_starts_execution_server",),
        True,
        None,
        lambda widget: widget.ensure_execution_server,
        False,
        lambda action, widget: action,
        lambda initialized: True,
    )
    CONNECTING_SERVER = (
        "connecting_server",
        "Connecting…",
        "Waiting for the execution server to become ready",
        (),
        False,
        None,
        lambda widget: widget.ensure_execution_server,
        False,
        lambda action, widget: action,
        lambda initialized: False,
    )
    RUN_PLATE = (
        "run_plate",
        "Run",
        "Run/Stop plate execution",
        ("starts_or_stops_execution_workflow",),
        True,
        PlateOperation.RUN,
        lambda widget: (
            widget.action_stop_execution
            if widget.is_any_plate_running()
            else widget.action_run_plate
        ),
    )
    CODE_PLATE = (
        "code_plate",
        "Code",
        "Generate Python code",
        ("opens_code_document_window",),
        False,
        None,
        lambda widget: widget.action_code_plate,
    )
    VIEW_RESULTS = (
        "view_results",
        "Results",
        "View live measurement results",
        ("opens_results_window",),
        False,
        None,
        lambda widget: widget.action_view_live_results,
    )
    VIEW_METADATA = (
        "view_metadata",
        "Viewer",
        "View plate metadata",
        ("opens_metadata_window",),
        False,
        None,
        lambda widget: widget.action_view_metadata,
    )


class CompilationActionProjection(EndpointStartupPresentationTarget):
    """Ephemeral action projection through the endpoint phase's existing dispatch.

    No connection state is retained here: each query projects the live browser
    authority used by the status indicator.
    """

    action: PlateManagerAction

    @classmethod
    def from_status(cls, status: EndpointStartupStatus) -> PlateManagerAction:
        projection = cls()
        status.phase.present(projection, status.message)
        return projection.action

    def present_connected(self, message: str) -> None:
        self.action = PlateManagerAction.COMPILE_PLATE

    def present_disconnected(self, message: str) -> None:
        self.action = PlateManagerAction.CONNECT_SERVER

    def present_checking(self, message: str) -> None:
        self.action = PlateManagerAction.CONNECTING_SERVER

    present_warning = present_checking
