"""ZMQ transport for the OpenHCS running-UI bridge."""

from __future__ import annotations

import uuid
from collections.abc import Mapping

from python_introspect import JsonObject, dataclass_from_mapping, to_jsonable

import openhcs.agent.services.ui_bridge_service as ui_bridge_service
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.ui_bridge import (
    UiActionCatalog,
    UiActionInvokeRequest,
    UiActionInvokeResult,
    UiBranchCatalog,
    UiBranchSwitchRequest,
    UiBridgeConnectionSpec,
    UiBridgeOperationRef,
    UiBridgeOperationStatusRequest,
    UiBridgeRequestEnvelope,
    UiBridgeResponseEnvelope,
    UiBridgeStatus,
    UiCodeDocument,
    UiCodeDocumentApplyRequest,
    UiCodeDocumentApplyResult,
    UiCodeDocumentCatalog,
    UiCodeDocumentRequest,
    UiCodeDocumentValidationRequest,
    UiCodeDocumentValidationResult,
    UiObjectStateFieldHelpRequest,
    UiObjectStateFieldHelpResult,
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
    UiStateSurfaceRequest,
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
from openhcs.agent.services.ui_bridge_service import (
    DEFAULT_UI_BRIDGE_TIMEOUT_MS,
    UI_BRIDGE_PROTOCOL_VERSION,
    UiBridgeGatewayABC,
    UiBridgeGatewayResponseError,
    UiBridgeGatewayTimeoutError,
    UiBridgeGatewayUnavailableError,
    UiBridgeOperationContract,
)
from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

UI_BRIDGE_CONTROL_TIMEOUT_MAX_MS = DEFAULT_UI_BRIDGE_TIMEOUT_MS
UI_BRIDGE_CONTROL_TIMEOUT_MIN_MS = 1


class UiBridgeControlClient:
    """Small JSON/ZMQ client for the UI bridge control socket."""

    def request(
        self,
        connection: UiBridgeConnectionSpec,
        contract: UiBridgeOperationContract,
        payload=None,
    ) -> JsonObject:
        if connection.port is None:
            raise UiBridgeGatewayUnavailableError
        contract.validate_request_payload(payload)

        request = UiBridgeRequestEnvelope(
            schema_version=SCHEMA_VERSION,
            bridge_protocol_version=UI_BRIDGE_PROTOCOL_VERSION,
            application=OPENHCS_ENDPOINT_APPLICATION,
            request_id=str(uuid.uuid4()),
            operation=contract.name,
            auth_token=connection.auth_token,
            payload=self._payload_object(payload),
        )
        response_payload = self._send(connection, to_jsonable(request))
        response = dataclass_from_mapping(
            UiBridgeResponseEnvelope,
            response_payload,
        )
        self._validate_response(request, response)
        if not response.ok:
            raise UiBridgeGatewayResponseError(response.errors)
        return response.payload

    def _send(
        self,
        connection: UiBridgeConnectionSpec,
        request_payload: JsonObject,
    ) -> JsonObject:
        import zmq

        context = zmq.Context.instance()
        socket = context.socket(zmq.REQ)
        timeout_ms = self._socket_timeout_ms(connection)
        request_operation = self._request_operation(request_payload)
        socket.setsockopt(zmq.LINGER, 0)
        socket.setsockopt(zmq.RCVTIMEO, timeout_ms)
        socket.setsockopt(zmq.SNDTIMEO, timeout_ms)
        try:
            socket.connect(connection.zmq_data_url(OPENHCS_ZMQ_CONFIG))
            socket.send_json(request_payload)
            response = socket.recv_json()
        except zmq.Again as exc:
            raise UiBridgeGatewayTimeoutError(
                operation=request_operation,
                timeout_ms=timeout_ms,
            ) from exc
        finally:
            socket.close(linger=0)
        if not isinstance(response, Mapping):
            raise TypeError(
                f"UI bridge response must be a JSON object, got {type(response).__name__}"
            )
        return dict(response)

    @staticmethod
    def _socket_timeout_ms(connection: UiBridgeConnectionSpec) -> int:
        return min(
            max(connection.timeout_ms, UI_BRIDGE_CONTROL_TIMEOUT_MIN_MS),
            UI_BRIDGE_CONTROL_TIMEOUT_MAX_MS,
        )

    @staticmethod
    def _request_operation(request_payload: JsonObject) -> str:
        if "operation" not in request_payload:
            raise ValueError(
                "UI bridge request payload missing required field 'operation'."
            )
        operation = request_payload["operation"]
        if not isinstance(operation, str):
            raise TypeError(
                "UI bridge request payload field 'operation' must be a string."
            )
        return operation

    @staticmethod
    def _payload_object(payload) -> JsonObject:
        if payload is None:
            return {}
        json_payload = to_jsonable(payload)
        if not isinstance(json_payload, Mapping):
            raise TypeError(
                f"UI bridge request payload must serialize to a JSON object, "
                f"got {type(json_payload).__name__}"
            )
        return json_payload

    @staticmethod
    def _validate_response(
        request: UiBridgeRequestEnvelope,
        response: UiBridgeResponseEnvelope,
    ) -> None:
        if response.schema_version != SCHEMA_VERSION:
            raise ValueError(
                f"Unsupported agent schema version: {response.schema_version}"
            )
        if response.bridge_protocol_version != UI_BRIDGE_PROTOCOL_VERSION:
            raise ValueError(
                f"Unsupported UI bridge protocol version: {response.bridge_protocol_version}"
            )
        OPENHCS_ENDPOINT_APPLICATION.compatibility_with(
            response.application
        ).require_match()
        if response.request_id != request.request_id:
            raise ValueError("UI bridge response request_id does not match request.")


class ZMQUiBridgeGateway(UiBridgeGatewayABC):
    """Gateway that connects MCP/agent services to a running PyQt UI bridge."""

    registry_key = "zmq"

    def __init__(self, client: UiBridgeControlClient | None = None) -> None:
        if client is None:
            client = UiBridgeControlClient()
        self._client = client

    def _request(
        self,
        connection: UiBridgeConnectionSpec,
        contract: UiBridgeOperationContract,
        payload=None,
    ) -> JsonObject:
        return self._client.request(connection, contract, payload)

    def status(self, connection: UiBridgeConnectionSpec) -> UiBridgeStatus:
        payload = self._request(connection, ui_bridge_service.UiBridgeStatusOperation)
        return dataclass_from_mapping(UiBridgeStatus, payload)

    def list_documents(
        self,
        connection: UiBridgeConnectionSpec,
    ) -> UiCodeDocumentCatalog:
        payload = self._request(
            connection, ui_bridge_service.UiBridgeListDocumentsOperation
        )
        return dataclass_from_mapping(UiCodeDocumentCatalog, payload)

    def list_state_surfaces(
        self,
        connection: UiBridgeConnectionSpec,
    ) -> UiStateSurfaceCatalog:
        payload = self._request(
            connection, ui_bridge_service.UiBridgeListStateSurfacesOperation
        )
        return dataclass_from_mapping(UiStateSurfaceCatalog, payload)

    def list_actions(
        self,
        connection: UiBridgeConnectionSpec,
    ) -> UiActionCatalog:
        payload = self._request(
            connection, ui_bridge_service.UiBridgeListActionsOperation
        )
        return dataclass_from_mapping(UiActionCatalog, payload)

    def list_windows(
        self,
        connection: UiBridgeConnectionSpec,
    ) -> UiWindowCatalog:
        payload = self._request(
            connection, ui_bridge_service.UiBridgeListWindowsOperation
        )
        return dataclass_from_mapping(UiWindowCatalog, payload)

    def list_object_state_scopes(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiObjectStateScopeListRequest,
    ) -> UiObjectStateScopeCatalog:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeListObjectStateScopesOperation,
            request,
        )
        return dataclass_from_mapping(UiObjectStateScopeCatalog, payload)

    def describe_object_state_field(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiObjectStateFieldHelpRequest,
    ) -> UiObjectStateFieldHelpResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeDescribeObjectStateFieldOperation,
            request,
        )
        return dataclass_from_mapping(
            UiObjectStateFieldHelpResult,
            payload,
        )

    def mutate_object_state_field(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiObjectStateFieldMutationRequest,
    ) -> UiObjectStateFieldMutationResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeMutateObjectStateFieldOperation,
            request,
        )
        return dataclass_from_mapping(
            UiObjectStateFieldMutationResult,
            payload,
        )

    def get_document(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiCodeDocumentRequest,
    ) -> UiCodeDocument:
        payload = self._request(
            connection, ui_bridge_service.UiBridgeGetDocumentOperation, request
        )
        return dataclass_from_mapping(UiCodeDocument, payload)

    def get_state_surface(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiStateSurfaceRequest,
    ) -> UiStateSurfaceDocument:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeGetStateSurfaceOperation,
            request,
        )
        return dataclass_from_mapping(UiStateSurfaceDocument, payload)

    def invoke_action(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiActionInvokeRequest,
    ) -> UiActionInvokeResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeInvokeActionOperation,
            request,
        )
        return dataclass_from_mapping(UiActionInvokeResult, payload)

    def selected_plate_workflow(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiSelectedPlateWorkflowRequest,
    ) -> UiSelectedPlateWorkflowResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeSelectedPlateWorkflowOperation,
            request,
        )
        return dataclass_from_mapping(
            UiSelectedPlateWorkflowResult,
            payload,
        )

    def focus_window(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiWindowFocusRequest,
    ) -> UiWindowFocusResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeFocusWindowOperation,
            request,
        )
        return dataclass_from_mapping(UiWindowFocusResult, payload)

    def navigate_window(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiWindowNavigateRequest,
    ) -> UiWindowNavigateResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeNavigateWindowOperation,
            request,
        )
        return dataclass_from_mapping(UiWindowNavigateResult, payload)

    def close_window(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiWindowCloseRequest,
    ) -> UiWindowCloseResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeCloseWindowOperation,
            request,
        )
        return dataclass_from_mapping(UiWindowCloseResult, payload)

    def snapshot_window(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiWindowSnapshotRequest,
    ) -> UiWindowSnapshotResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeSnapshotWindowOperation,
            request,
        )
        return dataclass_from_mapping(UiWindowSnapshotResult, payload)

    def widget_tree(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiWidgetTreeRequest,
    ) -> UiWidgetTreeResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeWidgetTreeOperation,
            request,
        )
        return dataclass_from_mapping(UiWidgetTreeResult, payload)

    def invoke_widget_action(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiWidgetActionInvokeRequest,
    ) -> UiWidgetActionInvokeResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeInvokeWidgetActionOperation,
            request,
        )
        return dataclass_from_mapping(
            UiWidgetActionInvokeResult,
            payload,
        )

    def validate_document(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiCodeDocumentValidationRequest,
    ) -> UiCodeDocumentValidationResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeValidateDocumentOperation,
            request,
        )
        return dataclass_from_mapping(
            UiCodeDocumentValidationResult,
            payload,
        )

    def apply_document(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiCodeDocumentApplyRequest,
    ) -> UiCodeDocumentApplyResult:
        payload = self._request(
            connection,
            ui_bridge_service.UiBridgeApplyDocumentOperation,
            request,
        )
        return dataclass_from_mapping(UiCodeDocumentApplyResult, payload)

    def list_snapshots(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiSnapshotListRequest,
    ) -> UiSnapshotCatalog:
        payload = self._request(
            connection,
            ui_bridge_service.UiBridgeListSnapshotsOperation,
            request,
        )
        return dataclass_from_mapping(UiSnapshotCatalog, payload)

    def restore_snapshot(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiSnapshotRestoreRequest,
    ) -> UiSnapshotRestoreResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeRestoreSnapshotOperation,
            request,
        )
        return dataclass_from_mapping(UiSnapshotRestoreResult, payload)

    def time_travel_head(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiTimeTravelHeadRequest,
    ) -> UiSnapshotRestoreResult:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeTimeTravelHeadOperation,
            request,
        )
        return dataclass_from_mapping(UiSnapshotRestoreResult, payload)

    def list_branches(self, connection: UiBridgeConnectionSpec) -> UiBranchCatalog:
        payload = self._request(
            connection, ui_bridge_service.UiBridgeListBranchesOperation
        )
        return dataclass_from_mapping(UiBranchCatalog, payload)

    def switch_branch(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiBranchSwitchRequest,
    ) -> UiSnapshotRestoreResult:
        payload = self._request(
            connection,
            ui_bridge_service.UiBridgeSwitchBranchOperation,
            request,
        )
        return dataclass_from_mapping(UiSnapshotRestoreResult, payload)

    def get_operation_status(
        self,
        connection: UiBridgeConnectionSpec,
        request: UiBridgeOperationStatusRequest,
    ) -> UiBridgeOperationRef:
        payload = self._client.request(
            connection,
            ui_bridge_service.UiBridgeGetOperationStatusOperation,
            request,
        )
        return dataclass_from_mapping(UiBridgeOperationRef, payload)
