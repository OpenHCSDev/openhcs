"""Agent service boundary for a running OpenHCS PyQt UI bridge."""

from __future__ import annotations

import json
import os
import stat
import time
from abc import ABC, abstractmethod
from collections.abc import Callable
from dataclasses import dataclass, replace
from enum import Enum
from os import environ
from pathlib import Path
from typing import Annotated, ClassVar

from metaclass_registry import AutoRegisterMeta
from python_introspect import (
    EnvironmentVariable,
    JsonObject,
    dataclass_from_mapping,
    overlay_dataclass_from_environment,
    project_dataclass,
)
from zmqruntime.config import (
    NonBlankString,
    PositiveInteger,
    SocketPort,
    TransportMode,
)

from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError
from openhcs.agent.dto.session import SessionEventBatch, SessionEventsRequest
from openhcs.agent.dto.ui_bridge import (
    UI_BRIDGE_UNKNOWN_WIDGET,
    UNKNOWN_UI_BRIDGE_OPERATION_ROUTE,
    UiActionCatalog,
    UiActionIdentity,
    UiActionInvocationStatus,
    UiActionInvokeRequest,
    UiActionInvokeResult,
    UiBranchCatalog,
    UiBranchSwitchRequest,
    UiBridgeCatalog,
    UiBridgeConnectionFields,
    UiBridgeConnectionSpec,
    UiBridgeDescriptorFile,
    UiBridgeDescriptorSummary,
    UiBridgeDescriptorWirePayload,
    UiBridgeEndpointIdentity,
    UiBridgeOperationIdentity,
    UiBridgeOperationRef,
    UiBridgeOperationStatus,
    UiBridgeOperationStatusRequest,
    UiBridgeOperationWaitRequest,
    UiBridgeStatus,
    UiCodeDocument,
    UiCodeDocumentApplyRequest,
    UiCodeDocumentApplyResult,
    UiCodeDocumentCatalog,
    UiCodeDocumentIdentity,
    UiCodeDocumentRequest,
    UiCodeDocumentSelectionMode,
    UiCodeDocumentSummary,
    UiCodeDocumentValidationRequest,
    UiCodeDocumentValidationResult,
    UiMutationReceipt,
    UiMutationRequestToken,
    UiObjectStateFieldListQuery,
    UiObjectStateFieldListResult,
    UiObjectStateFieldMutationRequest,
    UiObjectStateFieldMutationResult,
    UiObjectStateScopeCatalog,
    UiObjectStateScopeListRequest,
    UiSelectedPlateWorkflowRequest,
    UiSelectedPlateWorkflowResult,
    UiSnapshotCatalog,
    UiSnapshotListRequest,
    UiSnapshotRestoreRequest,
    UiSnapshotRestoreResult,
    UiStateSurfaceCatalog,
    UiStateSurfaceDocument,
    UiStateSurfaceIdentity,
    UiStateSurfaceRequest,
    UiStateSurfaceSummary,
    UiTimeTravelHeadRequest,
    UiWidgetActionInvokeRequest,
    UiWidgetActionInvokeResult,
    UiWidgetTreeRequest,
    UiWidgetTreeResult,
    UiWindowCatalog,
    UiWindowCloseRequest,
    UiWindowCloseResult,
    UiWindowFocusRequest,
    UiWindowFocusResult,
    UiWindowNavigateRequest,
    UiWindowNavigateResult,
    UiWindowSnapshotRequest,
    UiWindowSnapshotResult,
)
from openhcs.agent.path_policy import AgentPathPolicy, AgentPathPolicyError
from openhcs.agent.runtime_platform import AgentRuntimePlatformAuthority
from openhcs.agent.services.object_state_field_projection import (
    ObjectStateFieldListProjector,
)
from openhcs.agent.ui_bridge_environment import UiBridgeDescriptorEnvironment
from openhcs.core.native_threading import native_thread_count_environment_keys
from openhcs.runtime.viewer_protocol import ViewerLaunchContext
from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.utils.environment import OpenHCSProcessEnvironment

UI_BRIDGE_PROTOCOL_VERSION = "openhcs.ui_bridge.v3"
DEFAULT_UI_BRIDGE_CONNECTION_SPEC = UiBridgeConnectionSpec()
DEFAULT_UI_BRIDGE_TIMEOUT_MS = DEFAULT_UI_BRIDGE_CONNECTION_SPEC.timeout_ms
UNAVAILABLE_UI_CODE_DOCUMENT_TITLE = "Unavailable UI code document"
UNAVAILABLE_UI_STATE_SURFACE_TITLE = "Unavailable UI state surface"


@dataclass(slots=True)
class UiBridgeRequestRejected(Exception):
    """A request the client refuses before it reaches the bridge."""

    errors: tuple[AgentError, ...]


class UiBridgeOperation(ABC, metaclass=AutoRegisterMeta):
    """One running-UI operation: its request, result and failure answer.

    The class is the operation. Gateways, ``UiBridgeService`` and the MCP
    capabilities are generic over it; the running UI serves it with one
    ``@serves`` method. Operations with a ``name`` cross the wire and are
    registered under it; operations without one are composed on the client.
    """

    __registry_key__ = "name"
    __skip_if_no_key__ = True

    name: ClassVar[str | None] = None
    request_type: ClassVar[type]
    result_type: ClassVar[type]
    requires_auth: ClassVar[bool] = True
    bridge_feature: ClassVar[str | None] = None
    success_outcome: ClassVar[str] = "completed"
    failure_error_code: ClassVar[str] = "ui_bridge_operation_failed"

    @classmethod
    def for_name(cls, operation_name: str) -> type["UiBridgeOperation"]:
        try:
            return cls.__registry__[operation_name]
        except KeyError as exc:
            raise KeyError(f"Unknown UI bridge operation: {operation_name}") from exc

    @classmethod
    def require_name(cls) -> str:
        if cls.name is None:
            raise ValueError(f"UI bridge operation {cls.__qualname__} has no name.")
        return cls.name

    @classmethod
    def supported_operation_names(cls) -> tuple[str, ...]:
        return tuple(cls.__registry__)

    @classmethod
    def supported_bridge_features(cls) -> tuple[str, ...]:
        return tuple(
            dict.fromkeys(
                operation.bridge_feature
                for operation in cls.__registry__.values()
                if operation.bridge_feature is not None
            )
        )

    # -- request on the wire ------------------------------------------------

    @classmethod
    def decode_request(cls, payload: JsonObject):
        return dataclass_from_mapping(cls.request_type, payload)

    @classmethod
    def validate_request(cls, request) -> None:
        if not isinstance(request, cls.request_type):
            raise TypeError(
                f"UI bridge operation {cls.name!r} requires "
                f"{cls.request_type.__name__} request."
            )

    @classmethod
    def serve(cls, handler: Callable, request):
        """Run the running UI's implementation of this operation."""
        return handler(request)

    @classmethod
    def as_served(cls, result, binding: UiBridgeConnectionSpec):
        """The result as the bridge server answers it."""
        del binding
        return result

    @classmethod
    def accepted(cls, request, bridge_operation: UiBridgeOperationRef):
        """The placeholder a queued mutation answers before it completes."""
        raise NotImplementedError(f"{cls.__name__} is not a queued mutation.")

    @classmethod
    def outcome(cls, result) -> str:
        """The tracker outcome of one completed mutation."""
        del result
        return cls.success_outcome

    # -- client side -------------------------------------------------------

    @classmethod
    def failed(cls, request, errors: tuple[AgentError, ...]):
        """The result reporting that the operation could not run."""
        raise NotImplementedError(f"{cls.__name__} declares no failure answer.")

    @classmethod
    def prepare(cls, service: "UiBridgeService", request):
        """Check or rewrite the request before it leaves the client."""
        del service
        return request

    @classmethod
    def call(cls, service: "UiBridgeService", connection, request):
        return service.gateway.invoke(connection, cls, request)

    @classmethod
    def respond(cls, service: "UiBridgeService", connection, request):
        try:
            request = cls.prepare(service, request)
        except UiBridgeRequestRejected as rejected:
            return cls.failed(request, rejected.errors)
        resolution = service.resolve(connection)
        if not resolution.ok:
            return cls.failed(request, resolution.errors)
        try:
            return cls.call(service, resolution, request)
        except Exception as exc:
            return cls.failed(
                request, ui_bridge_gateway_errors(exc, "ui_bridge_unavailable")
            )


class UiBridgeRequestlessOperation(UiBridgeOperation):
    """Operation that takes no request."""

    request_type: ClassVar[None] = None

    @classmethod
    def decode_request(cls, payload: JsonObject) -> None:
        if payload:
            raise ValueError(
                f"UI bridge operation {cls.name!r} does not accept a payload."
            )
        return None

    @classmethod
    def validate_request(cls, request) -> None:
        if request is not None:
            raise TypeError(
                f"UI bridge operation {cls.name!r} does not accept a request."
            )

    @classmethod
    def serve(cls, handler: Callable, request):
        del request
        return handler()


def serves(operation: type[UiBridgeOperation]) -> Callable[[Callable], Callable]:
    """Mark the running UI's implementation of one wire operation."""

    def mark(handler: Callable) -> Callable:
        handler.served_operation = operation
        return handler

    return mark


class UiBridgeOperationServer:
    """Implementation side of the family: one ``@serves`` method per operation."""

    served_operations: ClassVar[dict[type[UiBridgeOperation], Callable]] = {}

    def __init_subclass__(cls, **kwargs) -> None:
        super().__init_subclass__(**kwargs)
        cls.served_operations = {
            handler.served_operation: handler
            for klass in reversed(cls.__mro__)
            for handler in vars(klass).values()
            if hasattr(handler, "served_operation")
        }

    def invoke(self, operation: type[UiBridgeOperation], request=None):
        handler = self.served_operations[operation]
        return operation.serve(handler.__get__(self), request)


# -- operation groups: the status feature tag and shared failure answers -----


class UiCodeDocumentOperation(UiBridgeOperation):
    bridge_feature = "ui_code_documents"


class UiStateSurfaceOperation(UiBridgeOperation):
    bridge_feature = "ui_state_surfaces"


class UiActionOperation(UiBridgeOperation):
    bridge_feature = "ui_actions"


class UiWindowOperation(UiBridgeOperation):
    bridge_feature = "ui_windows"


class UiObjectStateScopeOperation(UiBridgeOperation):
    bridge_feature = "objectstate_scopes"


class UiObjectStateSnapshotOperation(UiBridgeOperation):
    bridge_feature = "objectstate_snapshots"


class UiObjectStateRestoreOperation(UiBridgeOperation):
    """Operations that move the running UI to another ObjectState snapshot."""

    result_type = UiSnapshotRestoreResult

    @classmethod
    def failed(cls, request, errors):
        del request
        return UiSnapshotRestoreResult(
            schema_version=SCHEMA_VERSION,
            restored=False,
            target_snapshot=None,
            current_snapshot=None,
            errors=errors,
        )

    @classmethod
    def accepted(cls, request, bridge_operation):
        del request
        return UiSnapshotRestoreResult(
            schema_version=SCHEMA_VERSION,
            restored=False,
            target_snapshot=None,
            operation_id=bridge_operation.identity.operation_id,
            receipt=UiMutationReceipt.accepted_for(
                UiMutationRequestToken(),
                bridge_operation_id=bridge_operation.identity.operation_id,
            ),
        )

    @classmethod
    def outcome(cls, result) -> str:
        return "restored" if result.restored else "not_restored"


class UiBridgeOperationStatusQuery(UiBridgeOperation):
    """Operations answering with one bridge operation's status."""

    result_type = UiBridgeOperationRef

    @classmethod
    def failed(cls, request, errors):
        return UiBridgeOperationRef(
            schema_version=SCHEMA_VERSION,
            identity=UiBridgeOperationIdentity(
                operation_id=request.operation_id,
                route=UNKNOWN_UI_BRIDGE_OPERATION_ROUTE,
            ),
            status=UiBridgeOperationStatus.UNAVAILABLE.value,
            started_at_unix=0.0,
            errors=errors,
        )


# -- the operations ----------------------------------------------------------


class UiBridgeStatusOperation(UiBridgeRequestlessOperation):
    name = "status"
    result_type = UiBridgeStatus
    requires_auth = False

    @classmethod
    def as_served(cls, result: UiBridgeStatus, binding: UiBridgeConnectionSpec):
        return replace(
            result,
            auth_required=True,
            bridge_instance_id=binding.bridge_instance_id,
            connection=binding.public_connection(),
            descriptor_file_path=binding.descriptor_file_path,
            supported_operations=UiBridgeOperation.supported_operation_names(),
            provider_catalog_schema_versions=(SCHEMA_VERSION,),
            bridge_features=UiBridgeOperation.supported_bridge_features(),
        )

    @classmethod
    def failed(cls, request, errors):
        del request
        return UiBridgeStatus(schema_version=SCHEMA_VERSION, reachable=False, errors=errors)

    @staticmethod
    def _unreachable(resolution: "UiBridgeConnectionResolution") -> UiBridgeStatus:
        return UiBridgeStatus(
            schema_version=SCHEMA_VERSION,
            reachable=False,
            connection=resolution.public_connection(),
            descriptor_file_path=resolution.descriptor_file_path,
            descriptor_status=resolution.descriptor.status,
            descriptors=resolution.descriptor.summaries,
            errors=resolution.errors,
        )

    @classmethod
    def respond(cls, service, connection, request):
        resolution = service.resolve(connection)
        if not resolution.ok:
            return cls._unreachable(resolution)
        try:
            status = cls.call(service, resolution, request)
        except Exception as exc:
            return cls._unreachable(
                UiBridgeConnectionResolution.from_connection(
                    resolution,
                    descriptor=resolution.descriptor,
                    errors=ui_bridge_gateway_errors(exc, "ui_bridge_unreachable"),
                )
            )
        validation_errors = resolution.validate_live_status(status)
        if validation_errors:
            return cls._unreachable(
                UiBridgeConnectionResolution.from_connection(
                    resolution,
                    descriptor=replace(
                        resolution.descriptor,
                        status=validation_errors[0].code,
                    ),
                    errors=validation_errors,
                )
            )
        return resolution.descriptor.project_status(status, connection=resolution)


class UiBridgeListDocumentsOperation(
    UiBridgeRequestlessOperation, UiCodeDocumentOperation
):
    name = "list_documents"
    result_type = UiCodeDocumentCatalog

    @classmethod
    def failed(cls, request, errors):
        return UiCodeDocumentCatalog(SCHEMA_VERSION, documents=(), errors=errors)


class UiBridgeListStateSurfacesOperation(
    UiBridgeRequestlessOperation, UiStateSurfaceOperation
):
    name = "list_state_surfaces"
    result_type = UiStateSurfaceCatalog

    @classmethod
    def failed(cls, request, errors):
        return UiStateSurfaceCatalog(SCHEMA_VERSION, surfaces=(), errors=errors)


class UiBridgeListActionsOperation(UiBridgeRequestlessOperation, UiActionOperation):
    name = "list_actions"
    result_type = UiActionCatalog

    @classmethod
    def failed(cls, request, errors):
        return UiActionCatalog(SCHEMA_VERSION, actions=(), errors=errors)


class UiBridgeListWindowsOperation(UiBridgeRequestlessOperation, UiWindowOperation):
    name = "list_windows"
    result_type = UiWindowCatalog

    @classmethod
    def failed(cls, request, errors):
        return UiWindowCatalog(schema_version=SCHEMA_VERSION, windows=(), errors=errors)


class UiBridgeListObjectStateScopesOperation(UiObjectStateScopeOperation):
    name = "list_object_state_scopes"
    request_type = UiObjectStateScopeListRequest
    result_type = UiObjectStateScopeCatalog

    @classmethod
    def failed(cls, request, errors):
        del request
        return UiObjectStateScopeCatalog(
            schema_version=SCHEMA_VERSION,
            object_state_token=0,
            current_branch="",
            current_snapshot_index=-1,
            active=False,
            scopes=(),
            errors=errors,
        )

    @classmethod
    def respond(cls, service, connection, request):
        return request.filtered_catalog(super().respond(service, connection, request))


class UiBridgeGetObjectStateFieldsOperation(UiObjectStateScopeOperation):
    """Field rows projected on the client from the scope catalog."""

    request_type = UiObjectStateFieldListQuery
    result_type = UiObjectStateFieldListResult

    @classmethod
    def respond(cls, service, connection, request):
        catalog = UiBridgeListObjectStateScopesOperation.respond(
            service, connection, request.scope_list_request()
        )
        return ObjectStateFieldListProjector.project_catalog(request, catalog)


class UiBridgeMutateObjectStateFieldOperation(UiBridgeOperation):
    name = "mutate_object_state_field"
    request_type = UiObjectStateFieldMutationRequest
    result_type = UiObjectStateFieldMutationResult
    bridge_feature = "objectstate_field_mutation"

    @classmethod
    def failed(cls, request, errors):
        return UiObjectStateFieldMutationResult(
            schema_version=SCHEMA_VERSION,
            address=request,
            mutated=False,
            reset=request.reset,
            receipt=UiMutationReceipt.rejected_for(request.request_token),
            errors=errors,
        )

    @classmethod
    def accepted(cls, request, bridge_operation):
        return UiObjectStateFieldMutationResult(
            schema_version=SCHEMA_VERSION,
            address=request,
            mutated=False,
            reset=request.reset,
            receipt=UiMutationReceipt.accepted_for(
                request.request_token,
                bridge_operation_id=bridge_operation.identity.operation_id,
            ),
        )

    @classmethod
    def outcome(cls, result) -> str:
        return "mutated" if result.mutated else "not_mutated"


class UiBridgeGetDocumentOperation(UiCodeDocumentOperation):
    name = "get_document"
    request_type = UiCodeDocumentRequest
    result_type = UiCodeDocument

    @classmethod
    def failed(cls, request, errors):
        return UiCodeDocument(
            schema_version=SCHEMA_VERSION,
            summary=UiCodeDocumentSummary(
                schema_version=SCHEMA_VERSION,
                identity=UiCodeDocumentIdentity(document_id=request.document_id),
                title=UNAVAILABLE_UI_CODE_DOCUMENT_TITLE,
                widget_id=UI_BRIDGE_UNKNOWN_WIDGET,
                readable=False,
                writable=False,
            ),
            source="",
            mime_type="text/x-python",
            size_bytes=0,
            sha256="",
            current_revision_token=None,
            current_snapshot=None,
            selection_mode=request.resolved_selection_mode(
                UiCodeDocumentSelectionMode.SELECTED
            ),
            selected_scope_ids=(),
            errors=errors,
        )


class UiBridgeGetStateSurfaceOperation(UiStateSurfaceOperation):
    name = "get_state_surface"
    request_type = UiStateSurfaceRequest
    result_type = UiStateSurfaceDocument

    @classmethod
    def failed(cls, request, errors):
        return UiStateSurfaceDocument(
            schema_version=SCHEMA_VERSION,
            summary=UiStateSurfaceSummary(
                schema_version=SCHEMA_VERSION,
                identity=UiStateSurfaceIdentity(surface_id=request.surface_id),
                title=UNAVAILABLE_UI_STATE_SURFACE_TITLE,
                widget_id=UI_BRIDGE_UNKNOWN_WIDGET,
                readable=False,
            ),
            payload_schema="openhcs.ui.unavailable_state_surface.v1",
            payload={},
            selection_mode=request.resolved_selection_mode(
                UiCodeDocumentSelectionMode.ALL
            ),
            selected_scope_ids=(),
            current_revision_token=None,
            current_snapshot=None,
            errors=errors,
        )


class UiBridgeInvokeActionOperation(UiActionOperation):
    name = "invoke_action"
    request_type = UiActionInvokeRequest
    result_type = UiActionInvokeResult

    @classmethod
    def failed(cls, request, errors):
        return UiActionInvokeResult(
            schema_version=SCHEMA_VERSION,
            identity=UiActionIdentity(
                widget_id=request.widget_id,
                action_id=request.action_id,
            ),
            status=UiActionInvocationStatus.UNAVAILABLE.value,
            receipt=UiMutationReceipt.rejected_for(request.request_token),
            errors=errors,
        )

    @classmethod
    def accepted(cls, request, bridge_operation):
        return UiActionInvokeResult(
            schema_version=SCHEMA_VERSION,
            identity=UiActionIdentity(
                widget_id=request.widget_id,
                action_id=request.action_id,
            ),
            status=UiActionInvocationStatus.ACCEPTED.value,
            receipt=UiMutationReceipt.accepted_for(
                request.request_token,
                bridge_operation_id=bridge_operation.identity.operation_id,
            ),
            target_scope_ids=request.selected_scope_ids,
            selection_revision_token=request.observed_selection_revision_token,
        )

    @classmethod
    def outcome(cls, result) -> str:
        return result.status


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
                status=UiActionInvocationStatus.UNAVAILABLE.value,
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


class UiBridgeFocusWindowOperation(UiWindowOperation):
    name = "focus_window"
    request_type = UiWindowFocusRequest
    result_type = UiWindowFocusResult

    @classmethod
    def failed(cls, request, errors):
        return UiWindowFocusResult(
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            focused=False,
            errors=errors,
        )


class UiBridgeNavigateWindowOperation(UiBridgeOperation):
    name = "navigate_window"
    request_type = UiWindowNavigateRequest
    result_type = UiWindowNavigateResult
    bridge_feature = "ui_window_navigation"
    success_outcome = "navigated"
    failure_error_code = "ui_window_navigation_failed"

    @classmethod
    def failed(cls, request, errors):
        return UiWindowNavigateResult(
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            focused=False,
            navigated=False,
            created=False,
            errors=errors,
        )


class UiBridgeCloseWindowOperation(UiWindowOperation):
    name = "close_window"
    request_type = UiWindowCloseRequest
    result_type = UiWindowCloseResult

    @classmethod
    def failed(cls, request, errors):
        return UiWindowCloseResult(
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            closed=False,
            errors=errors,
        )


class UiBridgeSnapshotWindowOperation(UiBridgeOperation):
    name = "snapshot_window"
    request_type = UiWindowSnapshotRequest
    result_type = UiWindowSnapshotResult
    bridge_feature = "ui_window_snapshots"
    success_outcome = "captured"
    failure_error_code = "ui_window_snapshot_failed"

    @classmethod
    def failed(cls, request, errors):
        return project_dataclass(
            UiWindowSnapshotResult,
            request,
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            captured=False,
            errors=errors,
        )

    @classmethod
    def prepare(cls, service, request):
        try:
            output_dir = service.path_policy.assert_writable(request.output_dir_path)
        except AgentPathPolicyError as exc:
            raise UiBridgeRequestRejected((exc.to_agent_error(),)) from exc
        return replace(request, output_dir_path=str(output_dir))


class UiBridgeWidgetTreeOperation(UiBridgeOperation):
    name = "widget_tree"
    request_type = UiWidgetTreeRequest
    result_type = UiWidgetTreeResult
    bridge_feature = "widget_tree_projection"

    @classmethod
    def failed(cls, request, errors):
        return UiWidgetTreeResult(
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            projected=False,
            errors=errors,
        )


class UiBridgeGetOperationStatusOperation(UiBridgeOperationStatusQuery):
    name = "get_operation_status"
    request_type = UiBridgeOperationStatusRequest
    bridge_feature = "operation_status"


class UiBridgeWaitForOperationReceiptOperation(UiBridgeOperationStatusQuery):
    """Wait on the client for an operation to reach a terminal status."""

    request_type = UiBridgeOperationWaitRequest

    @classmethod
    def call(cls, service, connection, request):
        deadline = time.monotonic() + request.timeout_seconds
        status_request = UiBridgeOperationStatusRequest(
            operation_id=request.operation_id
        )
        while True:
            operation = UiBridgeGetOperationStatusOperation.call(
                service, connection, status_request
            )
            try:
                status = UiBridgeOperationStatus(operation.status)
            except ValueError:
                return replace(
                    operation,
                    errors=(
                        *operation.errors,
                        AgentError(
                            code="invalid_ui_bridge_operation_status",
                            message=(
                                f"UI bridge operation {request.operation_id!r} returned "
                                f"unknown status {operation.status!r}."
                            ),
                        ),
                    ),
                )
            if status.is_terminal:
                return operation
            remaining_seconds = deadline - time.monotonic()
            if remaining_seconds <= 0.0:
                return replace(
                    operation,
                    errors=(
                        *operation.errors,
                        AgentError(
                            code="ui_bridge_operation_wait_timeout",
                            message=(
                                f"UI bridge operation {request.operation_id!r} did not "
                                f"reach a terminal status within "
                                f"{request.timeout_seconds:g} seconds."
                            ),
                            hint=(
                                "The bridge mutation receipt remains active; inspect "
                                "it with openhcs_ui_get_operation_status or call "
                                "openhcs_ui_wait_for_operation_receipt again. Receipt "
                                "completion does not establish domain workflow "
                                "completion."
                            ),
                        ),
                    ),
                )
            time.sleep(min(request.poll_interval_seconds, remaining_seconds))


class UiBridgeInvokeWidgetActionOperation(UiBridgeOperation):
    name = "invoke_widget_action"
    request_type = UiWidgetActionInvokeRequest
    result_type = UiWidgetActionInvokeResult
    bridge_feature = "widget_action_invocation"

    @classmethod
    def failed(cls, request, errors):
        return UiWidgetActionInvokeResult(
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            path_id=request.path_id,
            action_kind=request.action_kind,
            invoked=False,
            receipt=UiMutationReceipt.rejected_for(request.request_token),
            errors=errors,
        )

    @classmethod
    def accepted(cls, request, bridge_operation):
        return UiWidgetActionInvokeResult(
            schema_version=SCHEMA_VERSION,
            window_id=request.window_id,
            path_id=request.path_id,
            action_kind=request.action_kind,
            invoked=False,
            receipt=UiMutationReceipt.accepted_for(
                request.request_token,
                bridge_operation_id=bridge_operation.identity.operation_id,
            ),
        )

    @classmethod
    def outcome(cls, result) -> str:
        return result.outcome.value

    @classmethod
    def call(cls, service, connection, request):
        """Return the terminal fact an accepted action receipt stands for."""
        result = super().call(service, connection, request)
        operation_id = result.receipt.bridge_operation_id
        if result.invoked or not result.receipt.accepted or operation_id is None:
            return result
        operation = UiBridgeWaitForOperationReceiptOperation.call(
            service,
            connection,
            UiBridgeOperationWaitRequest(
                operation_id=operation_id,
                timeout_seconds=min(connection.timeout_ms / 1000.0, 120.0),
                poll_interval_seconds=0.05,
            ),
        )
        return result.resolve_operation(operation)


class UiBridgeValidateDocumentOperation(UiCodeDocumentOperation):
    name = "validate_document"
    request_type = UiCodeDocumentValidationRequest
    result_type = UiCodeDocumentValidationResult

    @classmethod
    def failed(cls, request, errors):
        return UiCodeDocumentValidationResult(
            schema_version=SCHEMA_VERSION,
            document_id=request.document_id,
            valid=False,
            errors=errors,
        )


class UiBridgeApplyDocumentOperation(UiCodeDocumentOperation):
    name = "apply_document"
    request_type = UiCodeDocumentApplyRequest
    result_type = UiCodeDocumentApplyResult

    @classmethod
    def failed(cls, request, errors):
        return UiCodeDocumentApplyResult(
            schema_version=SCHEMA_VERSION,
            document_id=request.document_id,
            applied=False,
            base_revision_token=request.base_revision_token,
            receipt=UiMutationReceipt.rejected_for(request.request_token),
            errors=errors,
        )

    @classmethod
    def accepted(cls, request, bridge_operation):
        return UiCodeDocumentApplyResult(
            schema_version=SCHEMA_VERSION,
            document_id=request.document_id,
            applied=False,
            base_revision_token=request.base_revision_token,
            outcome=UiBridgeOperationStatus.RUNNING.value,
            operation_id=bridge_operation.identity.operation_id,
            receipt=UiMutationReceipt.accepted_for(
                request.request_token,
                bridge_operation_id=bridge_operation.identity.operation_id,
            ),
        )

    @classmethod
    def outcome(cls, result) -> str:
        return result.outcome


class UiBridgeListSnapshotsOperation(UiObjectStateSnapshotOperation):
    name = "list_snapshots"
    request_type = UiSnapshotListRequest
    result_type = UiSnapshotCatalog

    @classmethod
    def failed(cls, request, errors):
        del request
        return UiSnapshotCatalog(
            schema_version=SCHEMA_VERSION,
            current_branch="",
            current_snapshot_index=-1,
            object_state_token=0,
            active=False,
            snapshots=(),
            branches=(),
            errors=errors,
        )


class UiBridgeRestoreSnapshotOperation(
    UiObjectStateRestoreOperation, UiObjectStateSnapshotOperation
):
    name = "restore_snapshot"
    request_type = UiSnapshotRestoreRequest

    @classmethod
    def prepare(cls, service, request):
        del service
        selectors = (request.snapshot_id, request.index, request.branch)
        if sum(selector is not None for selector in selectors) != 1:
            raise UiBridgeRequestRejected(
                (
                    AgentError(
                        code="invalid_snapshot_restore_request",
                        message="Exactly one snapshot restore selector is required.",
                    ),
                )
            )
        return request


class UiBridgeTimeTravelHeadOperation(
    UiObjectStateRestoreOperation, UiObjectStateSnapshotOperation
):
    name = "time_travel_head"
    request_type = UiTimeTravelHeadRequest


class UiObjectStateBranchOperation(UiBridgeOperation):
    bridge_feature = "objectstate_branches"


class UiBridgeListBranchesOperation(
    UiBridgeRequestlessOperation, UiObjectStateBranchOperation
):
    name = "list_branches"
    result_type = UiBranchCatalog

    @classmethod
    def failed(cls, request, errors):
        return UiBranchCatalog(
            SCHEMA_VERSION, current_branch="", branches=(), errors=errors
        )


class UiBridgeSwitchBranchOperation(
    UiObjectStateRestoreOperation, UiObjectStateBranchOperation
):
    name = "switch_branch"
    request_type = UiBranchSwitchRequest


class UiBridgeDescriptorDirectoryAuthority:
    """Filesystem location policy for live UI bridge descriptors."""

    @staticmethod
    def default_descriptor_dir() -> Path:
        return UiBridgeDescriptorDirectoryAuthority.descriptor_dirs()[0]

    @classmethod
    def descriptor_dirs(cls) -> tuple[Path, ...]:
        configured = environ.get(
            UiBridgeDescriptorEnvironment.descriptor_directory_path_key
        )
        if configured:
            return (AgentRuntimePlatformAuthority.resolved_path(configured),)

        return AgentRuntimePlatformAuthority.current().application_runtime_dirs(
            "OpenHCS",
            "ui-bridge",
        )


class UiBridgeGatewayABC(ABC):
    """Transport to a running OpenHCS UI bridge, generic over the operation."""

    @abstractmethod
    def invoke(
        self,
        connection: UiBridgeConnectionSpec,
        operation: type[UiBridgeOperation],
        request,
    ):
        raise NotImplementedError



class UiBridgeGatewayErrorABC(ABC):
    """Gateway-originated bridge failure that knows its agent-facing errors."""

    @abstractmethod
    def agent_errors(self, fallback_code: str) -> tuple[AgentError, ...]:
        raise NotImplementedError


@dataclass(slots=True)
class UiBridgeGatewayUnavailableError(ConnectionError, UiBridgeGatewayErrorABC):
    def __str__(self) -> str:
        return "No running OpenHCS UI bridge gateway is configured."

    def agent_errors(self, fallback_code: str) -> tuple[AgentError, ...]:
        del fallback_code
        return (
            AgentError.from_exception(
                "ui_bridge_unavailable",
                self,
                hint=self.discovery_hint(),
            ),
        )

    @staticmethod
    def discovery_hint() -> str:
        searched_dirs = ", ".join(
            str(path) for path in UiBridgeDescriptorDirectoryAuthority.descriptor_dirs()
        )
        return (
            "Pass descriptor_file_path, set OPENHCS_UI_BRIDGE_DESCRIPTOR, set "
            "OPENHCS_UI_BRIDGE_DESCRIPTOR_DIR, or restart the UI so its bridge "
            f"descriptor is written to one of the searched directories: {searched_dirs}."
        )


@dataclass(slots=True)
class UiBridgeGatewayResponseError(RuntimeError, UiBridgeGatewayErrorABC):
    errors: tuple[AgentError, ...]

    def __str__(self) -> str:
        if not self.errors:
            return "UI bridge returned an error response."
        return "; ".join(error.message for error in self.errors)

    def agent_errors(self, fallback_code: str) -> tuple[AgentError, ...]:
        del fallback_code
        return tuple(self._with_restart_hint(error) for error in self.errors)

    @staticmethod
    def _with_restart_hint(error: AgentError) -> AgentError:
        if error.code != "unsupported_ui_bridge_operation":
            return error
        if error.hint:
            return error
        return replace(
            error,
            hint=(
                "The running OpenHCS UI bridge does not expose this operation. "
                "Restart the UI or UI bridge process so it imports the current "
                "OpenHCS source, then retry the MCP call."
            ),
        )


@dataclass(slots=True)
class UiBridgeGatewayTimeoutError(TimeoutError, UiBridgeGatewayErrorABC):
    agent_error_code: ClassVar[str] = "ui_bridge_timeout"

    operation: str
    timeout_ms: int

    def __str__(self) -> str:
        return (
            f"UI bridge operation {self.operation!r} timed out after "
            f"{self.timeout_ms}ms."
        )

    def agent_errors(self, fallback_code: str) -> tuple[AgentError, ...]:
        del fallback_code
        return (
            AgentError(
                code=self.agent_error_code,
                message=str(self),
                hint=(
                    "The running UI may be blocked or busy; retry after the UI "
                    "event loop is responsive."
                ),
                exception_type=type(self).__name__,
            ),
        )


def ui_bridge_gateway_errors(
    exception: Exception,
    fallback_code: str,
) -> tuple[AgentError, ...]:
    """Project a gateway exception into agent-facing errors."""

    if isinstance(exception, UiBridgeGatewayErrorABC):
        return exception.agent_errors(fallback_code)
    return (AgentError.from_exception(fallback_code, exception),)


@dataclass(frozen=True, slots=True)
class UiBridgeDescriptorResolution:
    status: str | None = None
    summaries: tuple[UiBridgeDescriptorSummary, ...] = ()

    def project_status(
        self,
        status_result: UiBridgeStatus,
        *,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeStatus:
        descriptor_status = status_result.descriptor_status
        if self.status is not None:
            descriptor_status = self.status
        descriptors = status_result.descriptors
        if self.summaries:
            descriptors = self.summaries
        return replace(
            status_result,
            connection=connection.public_connection(),
            descriptor_status=descriptor_status,
            descriptors=descriptors,
        )


@dataclass(frozen=True, slots=True)
class UiBridgeConnectionResolution(UiBridgeConnectionSpec):
    descriptor: UiBridgeDescriptorResolution = UiBridgeDescriptorResolution()
    errors: tuple[AgentError, ...] = ()

    @classmethod
    def from_connection(
        cls,
        connection: UiBridgeConnectionSpec,
        *,
        descriptor: UiBridgeDescriptorResolution = UiBridgeDescriptorResolution(),
        errors: tuple[AgentError, ...] = (),
    ) -> "UiBridgeConnectionResolution":
        return project_dataclass(
            cls,
            connection,
            descriptor=descriptor,
            errors=errors,
        )

    @property
    def ok(self) -> bool:
        return not self.errors

    @property
    def process_id(self) -> int | None:
        """Return the sole validated UI process identity, when descriptor-backed."""
        if len(self.descriptor.summaries) != 1:
            return None
        return self.descriptor.summaries[0].pid

    def validate_live_status(
        self,
        status_result: UiBridgeStatus,
    ) -> tuple[AgentError, ...]:
        """Validate that a status response still belongs to the resolved descriptor."""
        if len(self.descriptor.summaries) != 1:
            return ()
        expected = self.descriptor.summaries[0]
        if expected.descriptor_file_path is None:
            return self._endpoint_identity_errors(
                "The resolved UI bridge descriptor has no descriptor-file identity."
            )
        reread = UiBridgeDescriptorReader.read(Path(expected.descriptor_file_path))
        if not reread.ok or reread.descriptor is None:
            return reread.errors
        current = reread.descriptor.public_summary(expected.status)
        if current != expected:
            return self._endpoint_identity_errors(
                "The UI bridge descriptor changed while its status was being checked."
            )
        if UiBridgeEndpointIdentity.from_value(
            status_result
        ) != UiBridgeEndpointIdentity.from_value(expected):
            return self._endpoint_identity_errors(
                "The responding UI bridge does not own the resolved descriptor endpoint."
            )
        return ()

    @staticmethod
    def _endpoint_identity_errors(message: str) -> tuple[AgentError, ...]:
        return (
            AgentError(
                code="ui_bridge_endpoint_identity_mismatch",
                message=message,
                hint="Resolve the live UI bridge again before retrying.",
            ),
        )


@dataclass(frozen=True, slots=True)
class UiBridgeDescriptorReadResult:
    descriptor: UiBridgeDescriptorFile | None
    path: Path
    errors: tuple[AgentError, ...] = ()
    stale_process_descriptor: bool = False

    @property
    def ok(self) -> bool:
        return self.descriptor is not None and not self.errors


@dataclass(slots=True)
class UiBridgeDescriptorProcessGoneError(ValueError):
    pid: int

    def __str__(self) -> str:
        return f"UI bridge process is not running: {self.pid}"


@dataclass(slots=True)
class UiBridgeDescriptorProcessIdentityError(ValueError):
    pid: int
    descriptor_started_at_unix: float
    process_started_at_unix: float

    def __str__(self) -> str:
        return (
            f"UI bridge descriptor process identity is stale for PID {self.pid}: "
            f"the current process started at {self.process_started_at_unix}, "
            f"after the descriptor timestamp {self.descriptor_started_at_unix}"
        )


class DescriptorSetCardinality(Enum):
    NONE = "none"
    ONE = "one"
    MANY = "many"


@dataclass(frozen=True, slots=True)
class LiveUiBridgeDescriptorSet:
    descriptors: tuple[UiBridgeDescriptorFile, ...]

    @property
    def cardinality(self) -> DescriptorSetCardinality:
        count = len(self.descriptors)
        if count == 0:
            return DescriptorSetCardinality.NONE
        if count == 1:
            return DescriptorSetCardinality.ONE
        return DescriptorSetCardinality.MANY

    def only_descriptor(self) -> UiBridgeDescriptorFile:
        if self.cardinality is not DescriptorSetCardinality.ONE:
            raise ValueError(
                "Live UI bridge descriptor set does not contain exactly one descriptor."
            )
        return self.descriptors[0]


@dataclass(frozen=True, slots=True)
class UiBridgeEnvironment(UiBridgeConnectionFields):
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

    @classmethod
    def current(cls) -> "UiBridgeEnvironment":
        return overlay_dataclass_from_environment(cls())

    def apply(self, connection: UiBridgeConnectionSpec) -> UiBridgeConnectionSpec:
        return UiBridgeConnectionSpec.from_fields(
            self,
            defaults=connection,
        )


class DescriptorSetResolutionRunner(ABC, metaclass=AutoRegisterMeta):
    """Registered resolver behavior for live UI bridge descriptor cardinality."""

    __registry_key__ = "cardinality"
    __skip_if_no_key__ = True

    cardinality: ClassVar[DescriptorSetCardinality | None] = None

    @classmethod
    def for_cardinality(
        cls,
        cardinality: DescriptorSetCardinality,
    ) -> "DescriptorSetResolutionRunner":
        return cls.__registry__[cardinality]()

    @abstractmethod
    def resolve(
        self,
        resolver: "UiBridgeDescriptorResolver",
        descriptor_set: LiveUiBridgeDescriptorSet,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        raise NotImplementedError


class NoDescriptorSetResolutionRunner(DescriptorSetResolutionRunner):
    cardinality = DescriptorSetCardinality.NONE

    def resolve(
        self,
        resolver: "UiBridgeDescriptorResolver",
        descriptor_set: LiveUiBridgeDescriptorSet,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        del resolver, descriptor_set
        return UiBridgeConnectionResolution.from_connection(
            UiBridgeEnvironment.current().apply(connection),
            descriptor=UiBridgeDescriptorResolution(),
        )


class SingleDescriptorSetResolutionRunner(DescriptorSetResolutionRunner):
    cardinality = DescriptorSetCardinality.ONE

    def resolve(
        self,
        resolver: "UiBridgeDescriptorResolver",
        descriptor_set: LiveUiBridgeDescriptorSet,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        return resolver._connection_from_descriptor(
            descriptor_set.only_descriptor(),
            connection,
            "ok",
        )


class AmbiguousDescriptorSetResolutionRunner(DescriptorSetResolutionRunner):
    cardinality = DescriptorSetCardinality.MANY

    def resolve(
        self,
        resolver: "UiBridgeDescriptorResolver",
        descriptor_set: LiveUiBridgeDescriptorSet,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        return UiBridgeConnectionResolution.from_connection(
            connection,
            descriptor=UiBridgeDescriptorResolution(
                status="ambiguous_ui_bridge",
                summaries=tuple(
                    descriptor.public_summary("live")
                    for descriptor in descriptor_set.descriptors
                ),
            ),
            errors=(
                AgentError(
                    code="ambiguous_ui_bridge",
                    message="Multiple running OpenHCS UI bridge descriptors were found.",
                    hint="Provide descriptor_file_path or bridge_instance_id.",
                ),
            ),
        )


class UiBridgeDescriptorReader:
    """Read, parse, and validate one UI bridge descriptor file."""

    @classmethod
    def read(cls, path: Path) -> UiBridgeDescriptorReadResult:
        resolved_path = path.expanduser().resolve(strict=False)
        try:
            cls._validate_descriptor_file_path(resolved_path)
            payload = json.loads(resolved_path.read_text(encoding="utf-8"))
            if not isinstance(payload, dict):
                raise ValueError("UI bridge descriptor must be a JSON object.")
            descriptor = cls._descriptor_from_payload(
                dataclass_from_mapping(UiBridgeDescriptorWirePayload, payload),
                resolved_path,
            )
            cls._validate_descriptor_process(descriptor)
            cls._validate_descriptor_compatibility(descriptor)
        except Exception as exc:
            return UiBridgeDescriptorReadResult(
                descriptor=None,
                path=resolved_path,
                errors=(AgentError.from_exception("stale_ui_bridge_descriptor", exc),),
                stale_process_descriptor=isinstance(
                    exc,
                    (
                        UiBridgeDescriptorProcessGoneError,
                        UiBridgeDescriptorProcessIdentityError,
                    ),
                ),
            )
        return UiBridgeDescriptorReadResult(descriptor=descriptor, path=resolved_path)

    @classmethod
    def _descriptor_from_payload(
        cls,
        descriptor_payload: UiBridgeDescriptorWirePayload,
        descriptor_path: Path,
    ) -> UiBridgeDescriptorFile:
        del cls
        return project_dataclass(
            UiBridgeDescriptorFile,
            descriptor_payload,
            descriptor_file_path=str(descriptor_path),
        )

    @staticmethod
    def _validate_descriptor_compatibility(
        descriptor: UiBridgeDescriptorFile,
    ) -> None:
        if descriptor.bridge_protocol_version != UI_BRIDGE_PROTOCOL_VERSION:
            raise ValueError(
                "Unsupported UI bridge protocol version: "
                f"{descriptor.bridge_protocol_version}"
            )
        OPENHCS_ENDPOINT_APPLICATION.compatibility_with(
            descriptor.application
        ).require_match()

    @staticmethod
    def _validate_descriptor_file_path(path: Path) -> None:
        stat_result = path.stat()
        if not stat.S_ISREG(stat_result.st_mode):
            raise PermissionError("UI bridge descriptor must be a regular file.")
        platform_authority = AgentRuntimePlatformAuthority.current()
        if not platform_authority.supports_posix_permissions():
            return
        uid = platform_authority.current_user_id()
        if uid is None:
            return
        if stat_result.st_uid != uid:
            raise PermissionError(
                "UI bridge descriptor is not owned by the current user."
            )
        if stat_result.st_mode & (stat.S_IRWXG | stat.S_IRWXO):
            raise PermissionError(
                "UI bridge descriptor must not be group/world accessible."
            )
        parent_stat = path.parent.stat()
        parent_mode = parent_stat.st_mode
        parent_is_sticky = bool(parent_mode & stat.S_ISVTX)
        if parent_mode & (stat.S_IWGRP | stat.S_IWOTH) and not parent_is_sticky:
            raise PermissionError(
                "UI bridge descriptor parent directory is writable by other users."
            )

    @staticmethod
    def _validate_descriptor_process(descriptor: UiBridgeDescriptorFile) -> None:
        process_started_at_unix = AgentRuntimePlatformAuthority.process_started_at_unix(
            descriptor.pid
        )
        if process_started_at_unix is None:
            raise UiBridgeDescriptorProcessGoneError(descriptor.pid)
        if process_started_at_unix > descriptor.started_at_unix:
            raise UiBridgeDescriptorProcessIdentityError(
                pid=descriptor.pid,
                descriptor_started_at_unix=descriptor.started_at_unix,
                process_started_at_unix=process_started_at_unix,
            )


class UiBridgeDescriptorCatalog:
    """Discover the descriptor set selected for the current process."""

    @staticmethod
    def selected_descriptor_path() -> Path | None:
        """Return the exact descriptor selected by the shared environment contract."""

        configured = environ.get(UiBridgeDescriptorEnvironment.descriptor_file_path_key)
        if not configured:
            return None
        return AgentRuntimePlatformAuthority.resolved_path(configured)

    @classmethod
    def live_descriptors(cls) -> tuple[UiBridgeDescriptorFile, ...]:
        descriptors: list[UiBridgeDescriptorFile] = []
        for result in cls._read_descriptor_results():
            if result.ok and result.descriptor is not None:
                descriptors.append(result.descriptor)
        return tuple(descriptors)

    @classmethod
    def descriptor_catalog(cls) -> UiBridgeCatalog:
        descriptors: list[UiBridgeDescriptorSummary] = []
        errors: list[AgentError] = []
        for result in cls._read_descriptor_results():
            if result.descriptor is not None and not result.errors:
                descriptors.append(result.descriptor.public_summary("live"))
                continue
            errors.extend(result.errors)
        return UiBridgeCatalog(
            schema_version=SCHEMA_VERSION,
            bridges=tuple(descriptors),
            errors=tuple(errors),
        )

    @classmethod
    def _read_descriptor_results(cls) -> tuple[UiBridgeDescriptorReadResult, ...]:
        selected_path = cls.selected_descriptor_path()
        if selected_path is not None:
            return (UiBridgeDescriptorReader.read(selected_path),)

        descriptor_paths: list[Path] = []
        results: list[UiBridgeDescriptorReadResult] = []
        for directory in UiBridgeDescriptorDirectoryAuthority.descriptor_dirs():
            if not directory.exists():
                continue
            for path in sorted(directory.glob("ui_bridge_*.json")):
                descriptor_paths.append(path)
        descriptor_paths.extend(
            UiBridgeProcessAdvertisedDescriptorCatalog.descriptor_paths()
        )

        for path in dict.fromkeys(
            AgentRuntimePlatformAuthority.resolved_path(path)
            for path in descriptor_paths
        ):
            result = UiBridgeDescriptorReader.read(path)
            if result.stale_process_descriptor:
                cls._remove_stale_process_descriptor(result.path)
                continue
            results.append(result)
        return tuple(results)

    @staticmethod
    def _remove_stale_process_descriptor(path: Path) -> None:
        try:
            path.unlink()
        except OSError:
            return


class UiBridgeProcessAdvertisedDescriptorCatalog:
    """Find descriptor files explicitly advertised by running local UI processes."""

    proc_root = Path("/proc")
    descriptor_environment_name = UiBridgeDescriptorEnvironment.descriptor_file_path_key

    @classmethod
    def descriptor_paths(cls) -> tuple[Path, ...]:
        paths: list[Path] = []
        for process_dir in cls._process_dirs():
            descriptor_path = cls._descriptor_path_from_process(process_dir)
            if descriptor_path is not None:
                paths.append(descriptor_path)
        return tuple(dict.fromkeys(paths))

    @classmethod
    def _process_dirs(cls) -> tuple[Path, ...]:
        try:
            return tuple(
                path for path in cls.proc_root.iterdir() if path.name.isdigit()
            )
        except (FileNotFoundError, PermissionError, OSError):
            return ()

    @classmethod
    def _descriptor_path_from_process(cls, process_dir: Path) -> Path | None:
        try:
            environment_payload = (process_dir / "environ").read_bytes()
        except (FileNotFoundError, PermissionError, ProcessLookupError, OSError):
            return None
        return cls._descriptor_path_from_environment(environment_payload)

    @classmethod
    def _descriptor_path_from_environment(cls, payload: bytes) -> Path | None:
        prefix = f"{cls.descriptor_environment_name}=".encode()
        for entry in payload.split(b"\0"):
            if not entry.startswith(prefix):
                continue
            value = entry.removeprefix(prefix)
            if not value:
                return None
            return Path(os.fsdecode(value))
        return None


class UiBridgeDescriptorResolver:
    """Resolve UI bridge descriptors without widening the general path policy."""

    def resolve(
        self,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        if connection.descriptor_file_path is not None:
            return self._resolve_explicit_file(
                AgentRuntimePlatformAuthority.resolved_path(
                    connection.descriptor_file_path
                ),
                connection,
            )

        selected_descriptor_path = UiBridgeDescriptorCatalog.selected_descriptor_path()
        if selected_descriptor_path is not None:
            return self._resolve_explicit_file(
                selected_descriptor_path,
                connection,
            )

        if connection.bridge_instance_id is not None:
            return self._resolve_instance(connection.bridge_instance_id, connection)

        descriptor_set = LiveUiBridgeDescriptorSet(
            UiBridgeDescriptorCatalog.live_descriptors()
        )
        return DescriptorSetResolutionRunner.for_cardinality(
            descriptor_set.cardinality
        ).resolve(self, descriptor_set, connection)

    def _resolve_explicit_file(
        self,
        path: Path,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        result = UiBridgeDescriptorReader.read(path)
        if not result.ok or result.descriptor is None:
            return UiBridgeConnectionResolution.from_connection(
                replace(connection, descriptor_file_path=str(result.path)),
                descriptor=UiBridgeDescriptorResolution(
                    status="stale_ui_bridge_descriptor",
                ),
                errors=result.errors,
            )
        return self._connection_from_descriptor(result.descriptor, connection, "ok")

    def _resolve_instance(
        self,
        bridge_instance_id: str,
        connection: UiBridgeConnectionSpec,
    ) -> UiBridgeConnectionResolution:
        live_descriptors = UiBridgeDescriptorCatalog.live_descriptors()
        matches = tuple(
            descriptor
            for descriptor in live_descriptors
            if descriptor.bridge_instance_id == bridge_instance_id
        )
        if not matches:
            return UiBridgeConnectionResolution.from_connection(
                connection,
                descriptor=UiBridgeDescriptorResolution(
                    status="ui_bridge_descriptor_not_found",
                    summaries=tuple(
                        descriptor.public_summary("live")
                        for descriptor in live_descriptors
                    ),
                ),
                errors=(
                    AgentError(
                        code="ui_bridge_descriptor_not_found",
                        message=f"No live OpenHCS UI bridge descriptor matches {bridge_instance_id!r}.",
                        hint=(
                            "Use one of the returned descriptors' bridge_instance_id "
                            "values, pass descriptor_file_path, or omit both when "
                            "exactly one live bridge is available."
                        ),
                    ),
                ),
            )
        return self._connection_from_descriptor(matches[0], connection, "ok")

    def _connection_from_descriptor(
        self,
        descriptor: UiBridgeDescriptorFile,
        connection: UiBridgeConnectionSpec,
        status: str,
    ) -> UiBridgeConnectionResolution:
        return UiBridgeConnectionResolution.from_connection(
            descriptor.resolve_connection(connection),
            descriptor=UiBridgeDescriptorResolution(
                status=status,
                summaries=(descriptor.public_summary(status),),
            ),
        )


DEFAULT_UI_BRIDGE_DESCRIPTOR_RESOLVER = UiBridgeDescriptorResolver()


class UiBridgeService:
    """Run UI-bridge operations against the running UI an agent names."""

    def __init__(
        self,
        gateway: UiBridgeGatewayABC | None = None,
        descriptor_resolver: UiBridgeDescriptorResolver = DEFAULT_UI_BRIDGE_DESCRIPTOR_RESOLVER,
        path_policy: AgentPathPolicy | None = None,
    ) -> None:
        if gateway is None:
            from openhcs.agent.services.ui_bridge_transport import ZMQUiBridgeGateway

            gateway = ZMQUiBridgeGateway()
        self.gateway = gateway
        self._descriptor_resolver = descriptor_resolver
        self.path_policy = path_policy or AgentPathPolicy.from_environment()

    def invoke(
        self,
        operation: type[UiBridgeOperation],
        request=None,
        connection: UiBridgeConnectionSpec = DEFAULT_UI_BRIDGE_CONNECTION_SPEC,
    ):
        """Run one operation; failures come back as the operation's own result."""
        return operation.respond(self, connection, request)

    def resolve(self, connection: UiBridgeConnectionSpec) -> UiBridgeConnectionResolution:
        return self._descriptor_resolver.resolve(connection)

    def connection_from_args(
        self,
        *,
        host: str | None = None,
        port: int | None = None,
        transport_mode: TransportMode | None = None,
        timeout_ms: int | None = None,
        auth_token: str | None = None,
        descriptor_file_path: str | None = None,
        bridge_instance_id: str | None = None,
        persistent: bool | None = None,
    ) -> UiBridgeConnectionSpec:
        return self.connection_from_fields(
            UiBridgeConnectionFields(
                host=host,
                port=port,
                transport_mode=transport_mode,
                persistent=persistent,
                timeout_ms=timeout_ms,
                auth_token=auth_token,
                descriptor_file_path=descriptor_file_path,
                bridge_instance_id=bridge_instance_id,
            )
        )

    def connection_from_fields(
        self,
        fields: UiBridgeConnectionFields,
    ) -> UiBridgeConnectionSpec:
        return UiBridgeConnectionSpec.from_fields(
            fields,
            defaults=DEFAULT_UI_BRIDGE_CONNECTION_SPEC,
        )

    def list_bridges(self) -> UiBridgeCatalog:
        return UiBridgeDescriptorCatalog.descriptor_catalog()

    def viewer_launch_context(
        self,
        connection: UiBridgeConnectionSpec = DEFAULT_UI_BRIDGE_CONNECTION_SPEC,
    ) -> ViewerLaunchContext:
        """Resolve one typed detached-viewer context from UI or current process."""
        platform_authority = AgentRuntimePlatformAuthority.current()
        resolution = self._descriptor_resolver.resolve(connection)
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
