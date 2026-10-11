"""Composition root for the PyQt UI bridge."""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from openhcs.pyqt_gui.services.ui_agent_bridge import (
    UiAgentBridgeService,
    UiBridgeOperationTracker,
    UiObjectStateSnapshotProvider,
)
from openhcs.pyqt_gui.services.ui_bridge_registry import (
    CompositeUiBridgeProviderSet,
    UiBridgeProviderSetABC,
    UiBridgeRegistrationContext,
    UiBridgeSurfaceRegistry,
)


if TYPE_CHECKING:
    from openhcs.authoring.session.session import Session


@dataclass(frozen=True, slots=True)
class OpenHCSUiBridgeCompositionRoot:
    """Build a UI bridge service from registered provider sets."""

    provider_set: UiBridgeProviderSetABC
    session: "Session"

    @classmethod
    def for_main_window(cls, main_window) -> "OpenHCSUiBridgeCompositionRoot":
        return cls(
            CompositeUiBridgeProviderSet(
                tuple(
                    provider_set_type.for_main_window(main_window)
                    for provider_set_type in UiBridgeProviderSetABC.__registry__.values()
                    if provider_set_type.compose_for_main_window
                )
            ),
            main_window.session,
        )

    def build_service(self) -> UiAgentBridgeService:
        snapshot_provider = UiObjectStateSnapshotProvider(
            before_restore=self.session.require_definition_mutation_allowed,
        )
        operation_tracker = UiBridgeOperationTracker()
        registry = UiBridgeSurfaceRegistry()
        registry.register_live_overview_contributor(operation_tracker)
        self.provider_set.register(
            UiBridgeRegistrationContext(
                registry=registry,
                snapshot_provider=snapshot_provider,
            )
        )
        return UiAgentBridgeService(
            registry=registry,
            snapshot_provider=snapshot_provider,
            operation_tracker=operation_tracker,
            object_state_mutation_authorizer=(
                self.session.require_definition_mutation_allowed_for_object_scope
            ),
            session=self.session,
        )
