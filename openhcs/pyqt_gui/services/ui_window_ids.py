"""Agent-visible OpenHCS UI window identifiers."""

from __future__ import annotations

from typing import ClassVar

from openhcs.agent.ui_bridge_identities import (
    AboutOpenHCSWindowIdentity,
    GlobalConfigWindowIdentity,
    ImageBrowserWindowIdentity,
    KnowledgeBaseWindowIdentity,
    LogViewerWindowIdentity,
    MainWindowWidgetIdentity,
    PipelineEditorWidgetIdentity,
    DatasetListWidgetIdentity,
    SystemMonitorWindowIdentity,
    ZmqServerManagerWindowIdentity,
)


class OpenHCSUiWindowId:
    """Closed identifiers for stable windows exposed through the UI bridge."""

    main_window: ClassVar[str] = MainWindowWidgetIdentity.require_value()
    plate_manager: ClassVar[str] = DatasetListWidgetIdentity.require_value()
    pipeline_editor: ClassVar[str] = PipelineEditorWidgetIdentity.require_value()
    system_monitor: ClassVar[str] = SystemMonitorWindowIdentity.require_value()
    zmq_server_manager: ClassVar[str] = ZmqServerManagerWindowIdentity.require_value()
    image_browser: ClassVar[str] = ImageBrowserWindowIdentity.require_value()
    log_viewer: ClassVar[str] = LogViewerWindowIdentity.require_value()
    global_config: ClassVar[str] = GlobalConfigWindowIdentity.require_value()
    knowledge_base: ClassVar[str] = KnowledgeBaseWindowIdentity.require_value()
    about: ClassVar[str] = AboutOpenHCSWindowIdentity.require_value()
