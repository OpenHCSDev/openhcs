"""OpenHCS's registered UI bridge identities: its windows, widgets, documents and surfaces."""

from __future__ import annotations

from formbridge.bridge.identities import (
    UiCodeDocumentIdentityDeclaration,
    UiStableWidgetIdentityDeclaration,
    UiStableWindowIdentityDeclaration,
    UiStateSurfaceIdentityDeclarationBase,
    UiWidgetIdentityDeclaration,
)


class UiSessionViewWidgetIdentityDeclaration(UiStableWidgetIdentityDeclaration):
    """Stable window rendering one session view; the view owns its title."""

    @classmethod
    def require_title(cls) -> str:
        from openhcs.authoring.session.views import SessionView

        return SessionView.rendered_in(cls).title

    @classmethod
    def has_title(cls) -> bool:
        return True


class DatasetListWidgetIdentity(UiSessionViewWidgetIdentityDeclaration):
    value = "datasets"


class PipelineEditorWidgetIdentity(UiSessionViewWidgetIdentityDeclaration):
    value = "pipeline_editor"


class PipelineDebugToolbarWidgetIdentity(UiWidgetIdentityDeclaration):
    value = "pipeline_debug_toolbar"


class MainWindowWidgetIdentity(UiStableWidgetIdentityDeclaration):
    value = "main_window"
    title = "OpenHCS"


class SystemMonitorWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "system_monitor"
    title = "System Monitor"


class ZmqServerManagerWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "zmq_server_manager"
    title = "ZMQ Server Manager"


class ImageBrowserWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "image_browser"
    title = "Image Browser"


class LogViewerWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "log_viewer"
    title = "Log Viewer"


class GlobalConfigWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "global_config"
    title = "Configure OpenHCS"
    manager_scope_alias = ""


class KnowledgeBaseWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "knowledge_base"
    title = "OpenHCS Knowledge Base"


class AboutOpenHCSWindowIdentity(UiStableWindowIdentityDeclaration):
    value = "about_openhcs"
    title = "About OpenHCS"


class DatasetListCodeDocumentIdentity(UiCodeDocumentIdentityDeclaration):
    value = "datasets.orchestrator_config"
    widget_identity = DatasetListWidgetIdentity


class DatasetListStateSurfaceIdentity(
    UiStateSurfaceIdentityDeclarationBase
):
    value = "datasets.state"


class DatasetLiveMeasurementsStateSurfaceIdentity(
    UiStateSurfaceIdentityDeclarationBase
):
    value = "datasets.live_measurements"


class PipelineEditorStateSurfaceIdentityDeclaration(
    UiStateSurfaceIdentityDeclarationBase
):
    value = "pipeline_editor.state"


class PipelineDebugSessionStateSurfaceIdentityDeclaration(
    UiStateSurfaceIdentityDeclarationBase
):
    value = "pipeline_debug_toolbar.session"
