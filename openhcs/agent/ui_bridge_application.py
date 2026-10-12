"""OpenHCS's declaration of its running-UI bridge."""

from __future__ import annotations

from pathlib import Path

from formbridge.bridge.application import UiBridgeApplication

from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG


class OpenHCSUiBridgeApplication(UiBridgeApplication):
    protocol_version = "openhcs.ui_bridge.v4"
    endpoint_application = OPENHCS_ENDPOINT_APPLICATION
    transport_config = OPENHCS_ZMQ_CONFIG
    runtime_name = "OpenHCS"
    descriptor_file_variable = "OPENHCS_UI_BRIDGE_DESCRIPTOR"
    descriptor_directory_variable = "OPENHCS_UI_BRIDGE_DESCRIPTOR_DIR"
    server_name = "OpenHCSUiBridgeServer"
    service_name = "openhcs.ui_bridge"

    @classmethod
    def window_snapshot_dir(cls) -> Path:
        from openhcs.agent.path_policy import DEFAULT_AGENT_WINDOW_SNAPSHOT_DIR

        return DEFAULT_AGENT_WINDOW_SNAPSHOT_DIR

    @classmethod
    def connection_environment(cls):
        from openhcs.agent.services.ui_bridge_service import UiBridgeEnvironment

        return UiBridgeEnvironment()

    @classmethod
    def output_path_policy(cls):
        from openhcs.agent.path_policy import AgentPathPolicy

        return AgentPathPolicy.from_environment()

    @classmethod
    def log_file_path(cls) -> str | None:
        from openhcs.core.log_utils import get_current_log_file_path

        return get_current_log_file_path()

