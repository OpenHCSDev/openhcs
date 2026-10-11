"""The OpenHCS UI-bridge operations and its bridge connection environment."""

from __future__ import annotations

from dataclasses import dataclass
from os import environ
from typing import Annotated
from python_introspect import EnvironmentVariable
from zmqruntime.config import (
    NonBlankString,
    PositiveInteger,
    SocketPort,
    TransportMode,
)
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.session import SessionEventBatch, SessionEventsRequest
from formbridge.bridge.dto import (
    ActionUnavailable,
    UI_BRIDGE_UNKNOWN_WIDGET,
    UiActionIdentity,
    UiActionInvokeResult,
    UiBridgeConnectionFields,
    UiBridgeConnectionSpec,
    UiMutationReceipt,
)
from openhcs.agent.dto.ui_bridge import (
    UiSelectedPlateWorkflowRequest,
    UiSelectedPlateWorkflowResult,
)
import openhcs.agent.ui_bridge_application  # noqa: F401  (declares the OpenHCS bridge application)
from formbridge.bridge.service import (
    DEFAULT_UI_BRIDGE_CONNECTION_SPEC,
    UiBridgeOperation,
    UiBridgeService,
)
from formbridge.runtime_platform import AgentRuntimePlatform

from openhcs.core.native_threading import native_thread_count_environment_keys
from openhcs.runtime.viewer_protocol import ViewerLaunchContext
from openhcs.utils.environment import OpenHCSProcessEnvironment


class UiBridgeSelectedPlateWorkflowOperation(UiBridgeOperation):
    name = "selected_plate_workflow"
    request_type = UiSelectedPlateWorkflowRequest
    result_type = UiSelectedPlateWorkflowResult
    bridge_feature = "selected_plate_workflows"

    @classmethod
    def failed(cls, request, errors):
        return UiSelectedPlateWorkflowResult(
            schema_version=SCHEMA_VERSION,
            workflow=request.workflow,
            action_result=UiActionInvokeResult(
                schema_version=SCHEMA_VERSION,
                identity=UiActionIdentity(
                    widget_id=UI_BRIDGE_UNKNOWN_WIDGET,
                    action_id=request.workflow.value,
                ),
                status=ActionUnavailable,
                receipt=UiMutationReceipt.rejected_for(request.request_token),
                errors=errors,
            ),
            errors=errors,
        )


class UiBridgeSessionEventsOperation(UiBridgeOperation):
    """The running UI's session events after a sequence (push, not polling)."""

    name = "session_events"
    request_type = SessionEventsRequest
    result_type = SessionEventBatch
    bridge_feature = "session_events"

    @classmethod
    def failed(cls, request, errors):
        return SessionEventBatch(
            events=(), last_sequence=request.after_sequence, errors=errors
        )


@dataclass(frozen=True, slots=True)
class UiBridgeEnvironment(UiBridgeConnectionFields):
    """The environment variables that override a UI bridge client's connection."""

    host: Annotated[
        NonBlankString | None,
        EnvironmentVariable("OPENHCS_UI_BRIDGE_HOST"),
    ] = None
    port: Annotated[
        SocketPort | None,
        EnvironmentVariable("OPENHCS_UI_BRIDGE_PORT"),
    ] = None
    transport_mode: Annotated[
        TransportMode | None,
        EnvironmentVariable("OPENHCS_UI_BRIDGE_TRANSPORT_MODE"),
    ] = None
    timeout_ms: Annotated[
        PositiveInteger | None,
        EnvironmentVariable("OPENHCS_UI_BRIDGE_TIMEOUT_MS"),
    ] = None
    auth_token: Annotated[
        NonBlankString | None,
        EnvironmentVariable("OPENHCS_UI_BRIDGE_AUTH_TOKEN"),
    ] = None


class OpenHCSUiBridgeService(UiBridgeService):
    """The UI-bridge client of OpenHCS agents, which also launches viewers beside the UI."""

    def viewer_launch_context(
        self,
        connection: UiBridgeConnectionSpec = DEFAULT_UI_BRIDGE_CONNECTION_SPEC,
    ) -> ViewerLaunchContext:
        """The running UI's graphical session when its bridge resolves, else this process's."""
        platform_authority = AgentRuntimePlatform.current()
        resolution = self.resolve(connection)
        if resolution.ok and resolution.process_id is not None:
            environment = platform_authority.graphical_process_environment(
                resolution.process_id,
                additional_keys=(
                    *OpenHCSProcessEnvironment.child_process_environment_keys(),
                    *native_thread_count_environment_keys(),
                ),
            )
            if (
                environment is not None
                and platform_authority.graphical_session_available(environment)
            ):
                return ViewerLaunchContext.projected_graphical_session(environment)
        if platform_authority.graphical_session_available(environ):
            return ViewerLaunchContext.inherited_graphical_session()
        return ViewerLaunchContext.headless()
