"""OpenHCS main-window providers for the UI bridge."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from formbridge.bridge.contracts import UiActionProviderIdentity
from openhcs.authoring.session.operations.application import (
    CheckForUpdates,
    ExitApplication,
    RestartApplication,
)
from openhcs.pyqt_gui.services.ui_bridge_session_actions import (
    SessionOperationActionProvider,
)
from formbridge.bridge.registry import UiBridgeProviderSetABC, UiBridgeRegistrationContext
from pyqt_reactive.bridge.windows import (
    MAIN_WINDOW_PROVIDER_ID,
    ManagedWindowActionProvider,
    WindowCatalogProjectionABC,
)
from openhcs.agent.ui_bridge_identities import MainWindowWidgetIdentity

if TYPE_CHECKING:
    from openhcs.pyqt_gui.main import OpenHCSMainWindow

MAIN_WINDOW_ACTION_PROVIDER_IDENTITY = UiActionProviderIdentity.from_widget_declaration(
    MainWindowWidgetIdentity,
    title="Main window actions",
)


@dataclass(frozen=True, slots=True)
class MainWindowBridgeProviderSet(UiBridgeProviderSetABC):
    """Provider set for main-window generic UI projections."""

    main_window: "OpenHCSMainWindow"
    registry_key = MAIN_WINDOW_PROVIDER_ID

    @classmethod
    def for_main_window(cls, main_window) -> "MainWindowBridgeProviderSet":
        return cls(main_window)

    def register(self, context: UiBridgeRegistrationContext) -> None:
        for provider_type in WindowCatalogProjectionABC.registered_types():
            context.registry.register_window_provider(
                provider_type.create(self.main_window)
            )
        context.registry.register_action_provider(
            SessionOperationActionProvider(
                identity=MAIN_WINDOW_ACTION_PROVIDER_IDENTITY,
                session=self.main_window.session,
                operations=(CheckForUpdates, RestartApplication, ExitApplication),
            )
        )
        context.registry.register_action_provider(ManagedWindowActionProvider())
