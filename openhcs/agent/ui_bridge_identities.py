"""OpenHCS's registered UI bridge identities: its windows, widgets, documents and surfaces."""

from __future__ import annotations

from formbridge.bridge.identities import (
    UiCodeDocumentIdentityDeclaration,
    UiStableWidgetIdentityDeclaration,
    UiStableWindowIdentityDeclaration,
    UiStateSurfaceIdentityDeclarationBase,
    UiWidgetIdentityDeclaration,
)


class DatasetListWidgetIdentity(UiStableWidgetIdentityDeclaration):
    value = "datasets"
    title = "Datasets"


class PipelineEditorWidgetIdentity(UiStableWidgetIdentityDeclaration):
    value = "pipeline_editor"
    title = "Pipeline Editor"


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
