"""Catalog control uses the original connection owner, never an address owner."""

from __future__ import annotations

import asyncio
import json
from dataclasses import dataclass, replace

import pytest
from zmqruntime.client import AttachedEndpointConnection
from zmqruntime.messages import (
    ControlMessageType,
    EndpointApplication,
    MessageFields,
    PongResponse,
    ProcessIdentity,
    ServerRole,
)

from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    FunctionCatalogControlMessageType,
    FunctionCatalogControlRequest,
    FunctionCatalogControlRequestABC,
    FunctionCatalogPreparationStartRequest,
    FunctionDetailControlRequest,
    FunctionReferenceControlRequest,
    FunctionSearchRequest,
)
from openhcs.agent.services.endpoint_function_catalog_service import (
    ZMQFunctionCatalogService,
)
from openhcs.mcp.context import OpenHCSAgentContext
from openhcs.mcp.server import build_server
from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.zmq_execution_client import (
    FunctionCatalogEndpointUnavailableError,
    ZMQExecutionClient,
)


def _handshake(client: ZMQExecutionClient) -> PongResponse:
    return PongResponse(
        port=client.port,
        control_port=client.control_port,
        ready=True,
        server="engineering execution",
        server_role=ServerRole.EXECUTION,
        application=OPENHCS_ENDPOINT_APPLICATION,
        process_identity=ProcessIdentity.current(),
    )


@pytest.fixture
def connection(monkeypatch):
    client = ZMQExecutionClient(port=22319, persistent=True)
    expected = _handshake(client)
    client._connection = AttachedEndpointConnection(expected)
    observed = []

    def send(payload, *, timeout_ms):
        observed.append(payload)
        assert 0 < timeout_ms <= 5000
        return expected.to_dict()

    monkeypatch.setattr(client, "_send_control_request", send)
    monkeypatch.setattr(
        client, "connect", lambda **kwargs: pytest.fail("No implicit startup")
    )
    return client, expected, observed


def test_exited_native_rejects_before_any_foreign_message(connection, monkeypatch):
    client, expected, observed = connection
    monkeypatch.setattr(client, "known_server_process_is_alive", lambda: False)
    for query in ("background", "reconstruction", "opening"):
        with pytest.raises(FunctionCatalogEndpointUnavailableError, match="has exited"):
            client.search_function_catalog(FunctionSearchRequest(query=query))
    assert observed == []
    assert client.connected_endpoint is expected


@pytest.mark.parametrize(
    "replacement", ("viewer", "new_incarnation", "missing_identity", "application")
)
def test_current_peer_cannot_replace_connection_owner(
    connection, monkeypatch, replacement
):
    client, expected, observed = connection
    choices = {
        "viewer": replace(expected, server_role=ServerRole.VIEWER),
        "new_incarnation": replace(
            expected,
            process_identity=replace(expected.process_identity, create_time=0.0),
        ),
        "missing_identity": replace(expected, process_identity=None),
        "application": replace(expected, application=EndpointApplication("other", "1")),
    }

    def ping(payload, *, timeout_ms):
        observed.append(payload)
        return choices[replacement].to_dict()

    monkeypatch.setattr(client, "_send_control_request", ping)
    with pytest.raises(
        FunctionCatalogEndpointUnavailableError, match="no longer belongs"
    ):
        client.search_function_catalog(FunctionSearchRequest(query="background"))
    assert len(observed) == 1
    assert observed[0][MessageFields.TYPE] == ControlMessageType.PING.value
    assert client.connected_endpoint is expected


@pytest.mark.parametrize("bad_handshake", ("viewer", "missing_identity", "application"))
def test_initial_attachment_requires_execution_proof(connection, bad_handshake):
    client, expected, observed = connection
    choices = {
        "viewer": replace(expected, server_role=ServerRole.VIEWER),
        "missing_identity": replace(expected, process_identity=None),
        "application": replace(expected, application=None),
    }
    client._connection = AttachedEndpointConnection(choices[bad_handshake])
    with pytest.raises(FunctionCatalogEndpointUnavailableError):
        client.search_function_catalog(FunctionSearchRequest())
    assert observed == []


@pytest.mark.parametrize(
    "invoke",
    (
        lambda c: c.get_function_catalog(FunctionCatalogControlRequest()),
        lambda c: c.search_function_catalog(FunctionSearchRequest()),
        lambda c: c.get_function_detail(
            FunctionDetailControlRequest(function_id="cpu:a", catalog_revision="rev")
        ),
        lambda c: c.get_function_reference(
            FunctionReferenceControlRequest(function_id="cpu:a", catalog_revision="rev")
        ),
        lambda c: c.function_catalog_preparation(
            FunctionCatalogPreparationStartRequest(ExecutionConnectionSpec(port=22319))
        ),
        lambda c: c.custom_function_registration_destination(
            CustomFunctionRegistrationDestinationRequest(function_name="a")
        ),
        lambda c: c.register_custom_function(
            CustomFunctionRegistrationRequest(source_code="never sent", persist=False)
        ),
    ),
)
def test_entire_control_family_uses_same_incarnation_admission(
    connection, monkeypatch, invoke
):
    client, expected, observed = connection
    monkeypatch.setattr(client, "known_server_process_is_alive", lambda: False)
    with pytest.raises(FunctionCatalogEndpointUnavailableError):
        invoke(client)
    assert observed == []
    assert client.connected_endpoint is expected


def test_new_request_declaration_and_cooperative_capability_need_no_consumer_edit(
    monkeypatch,
):
    @dataclass(frozen=True, slots=True)
    class IndependentCatalogProbe(FunctionCatalogControlRequestABC):
        marker: str = "independent"
        message_type = FunctionCatalogControlMessageType.READ_CATALOG

    events = []

    class AuditCapability:
        def _send_function_catalog_exchange(self, request, **kwargs):
            events.append(("before", request.marker))
            response = super()._send_function_catalog_exchange(request, **kwargs)
            events.append(("after", response))
            return response

    class AuditedCatalogClient(AuditCapability, ZMQExecutionClient):
        pass

    client = AuditedCatalogClient(port=22319, persistent=True)
    expected = _handshake(client)
    client._connection = AttachedEndpointConnection(expected)
    observed = []
    result = {"status": "ok", "independent": "result"}

    def send(payload, *, timeout_ms):
        observed.append(payload)
        if payload[MessageFields.TYPE] == ControlMessageType.PING.value:
            return expected.to_dict()
        assert payload["request"] is request
        return result

    monkeypatch.setattr(client, "_send_control_request", send)
    request = IndependentCatalogProbe()
    assert client._send_function_catalog_exchange(request) is result
    assert events == [("before", "independent"), ("after", result)]
    assert len(observed) == 2
    assert AuditedCatalogClient.__mro__[:3] == (
        AuditedCatalogClient,
        AuditCapability,
        ZMQExecutionClient,
    )


def test_generated_public_search_reports_recoverable_closed_owner(
    connection, monkeypatch
):
    client, expected, observed = connection
    monkeypatch.setattr(client, "known_server_process_is_alive", lambda: False)
    service = ZMQFunctionCatalogService(
        lambda: OPENHCS_ZMQ_CONFIG, client_factory=lambda config: client
    )
    context = OpenHCSAgentContext(endpoint_function_catalog=service)

    async def invoke():
        server = build_server(context)
        for query in ("background", "opening"):
            response = await server.call_tool(
                "openhcs_search_functions", {"query": query}
            )
            content = response[0] if isinstance(response, tuple) else response.content
            payload = json.loads(content[0].text)
            assert (
                payload["errors"][0]["code"] == "function_catalog_endpoint_unavailable"
            )
            assert "explicitly" in payload["errors"][0]["hint"].lower()

    asyncio.run(invoke())
    assert observed == []
    assert client.connected_endpoint is expected
    service.close()
