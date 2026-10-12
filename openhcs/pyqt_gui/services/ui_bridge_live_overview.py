"""OpenHCS contributions to the UI live overview: viewer sessions and the overview surface."""

from __future__ import annotations

from zmqruntime.viewer_state import ViewerInstance, ViewerStateManager
from formbridge.bridge.dto import (
    UiLiveOverviewItem,
    UiLiveOverviewMetric,
    UiLiveOverviewSection,
    UiLiveOverviewSeverity,
)
from openhcs.core.streaming_config_declarations import ViewerFamily
from formbridge.bridge.contracts import (
    UiLiveOverviewContributorABC,
    UiLiveOverviewContributorIdentity,
)
from openhcs.pyqt_gui.services.ui_window_ids import OpenHCSUiWindowId
from formbridge.bridge.identities import UiLiveOverviewStateSurfaceIdentityDeclaration
from formbridge.bridge.contracts import (
    UiOwnedStateSurfaceDeclaration,
    UiStateSurfaceProviderIdentity,
    state_surface_declaration_for_identity,
)
from formbridge.bridge.registry import (
    UiBridgeProviderSetABC,
    UiBridgeRegistrationContext,
)
from formbridge.bridge.live_overview import UiLiveOverviewStateSurfaceProvider


class ViewerSessionLiveOverviewContributor(UiLiveOverviewContributorABC):
    """Project the process-wide viewer lifecycle authority into the overview."""

    overview_identity = UiLiveOverviewContributorIdentity(
        section_id="viewer-sessions",
        title="Viewer sessions",
    )

    def __init__(
        self,
        viewer_state_manager: ViewerStateManager | None = None,
    ) -> None:
        if viewer_state_manager is None:
            viewer_state_manager = ViewerStateManager.get_instance()
        self._viewer_state_manager = viewer_state_manager

    def overview_sections(self) -> tuple[UiLiveOverviewSection, ...]:
        viewers = tuple(
            sorted(
                self._viewer_state_manager.list_viewers(),
                key=lambda viewer: (viewer.viewer_type, viewer.port),
            )
        )
        return (
            UiLiveOverviewSection(
                section_id=self.overview_identity.section_id,
                title=self.overview_identity.title,
                summary=f"{len(viewers)} viewers",
                metrics=(
                    UiLiveOverviewMetric(
                        key="viewers",
                        label="viewers",
                        value=str(len(viewers)),
                    ),
                    UiLiveOverviewMetric(
                        key="healthy",
                        label="healthy",
                        value=str(sum(1 for viewer in viewers if viewer.is_healthy)),
                    ),
                    UiLiveOverviewMetric(
                        key="queued_images",
                        label="queued images",
                        value=str(sum(viewer.queued_images for viewer in viewers)),
                    ),
                ),
                items=tuple(self._overview_item(viewer) for viewer in viewers),
            ),
        )

    @staticmethod
    def _overview_item(viewer: ViewerInstance) -> UiLiveOverviewItem:
        if viewer.error_message:
            severity = UiLiveOverviewSeverity.ERROR.value
        elif not viewer.is_healthy:
            severity = UiLiveOverviewSeverity.WARNING.value
        else:
            severity = UiLiveOverviewSeverity.INFO.value
        detail_parts = (
            f"port={viewer.port}",
            f"queued_images={viewer.queued_images}",
            f"processed_images={viewer.processed_images}",
        )
        if viewer.error_message:
            detail_parts = (*detail_parts, f"error={viewer.error_message}")
        return UiLiveOverviewItem(
            label=(
                f"{ViewerFamily.named(viewer.viewer_type).display_name} viewer"
            ),
            status=viewer.state.name.lower(),
            detail=" ".join(detail_parts),
            severity=severity,
            source_window_id=OpenHCSUiWindowId.zmq_server_manager,
        )


class LiveOverviewBridgeProviderSet(UiBridgeProviderSetABC):
    """Register the live overview surface after its source providers exist."""

    registry_key = UiLiveOverviewStateSurfaceIdentityDeclaration.require_value()

    def __init__(
        self,
        declaration: UiOwnedStateSurfaceDeclaration | None = None,
        *,
        widget_declaration=None,
    ) -> None:
        if declaration is None or widget_declaration is None:
            from openhcs.pyqt_gui.main import OpenHCSMainWindow

            declaration = state_surface_declaration_for_identity(
                OpenHCSMainWindow.UI_STATE_SURFACE_DECLARATIONS,
                UiLiveOverviewStateSurfaceIdentityDeclaration,
            )
            widget_declaration = OpenHCSMainWindow.UI_BRIDGE_WIDGET_IDENTITY
        self._declaration = declaration
        self._identity = UiStateSurfaceProviderIdentity.from_owner(
            declaration,
            widget_declaration=widget_declaration,
        )

    @classmethod
    def for_main_window(cls, main_window) -> "LiveOverviewBridgeProviderSet":
        del main_window
        return cls()

    def register(self, context: UiBridgeRegistrationContext) -> None:
        context.registry.register_live_overview_contributor(
            ViewerSessionLiveOverviewContributor()
        )
        context.registry.register_state_surface_provider(
            UiLiveOverviewStateSurfaceProvider(
                registry=context.registry,
                snapshot_provider=context.snapshot_provider,
                declaration=self._declaration,
                identity=self._identity,
            )
        )
