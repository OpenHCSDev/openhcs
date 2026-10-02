"""Catalog control uses the original connection owner, never an address owner."""

from __future__ import annotations

import asyncio
import json
import threading
from dataclasses import dataclass, replace

import pytest
from zmqruntime.client import AttachedEndpointConnection
from zmqruntime.config import TransportMode
from zmqruntime.messages import (
    ControlMessageType,
    EndpointApplication,
    MessageFields,
    PongResponse,
    ProcessIdentity,
    ServerRole,
)
from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import (
    CustomFunctionRegistrationDestinationRequest,
    CustomFunctionRegistrationRequest,
    FunctionCatalogControlMessageType,
    FunctionCatalogControlRequest,
    FunctionCatalogControlRequestABC,
    FunctionCatalogControlResponse,
    FunctionCatalogPreparationCancelRequest,
    FunctionCatalogPreparationHandle,
    FunctionCatalogPreparationOutcome,
    FunctionCatalogPreparationStartRequest,
    FunctionCatalogPreparationState,
    FunctionCatalogPreparationStateControlResponse,
    FunctionCatalogPreparationStatusRequest,
    FunctionDetailControlRequest,
    FunctionReferenceControlRequest,
    FunctionSearchRequest,
    catalog_page,
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
    FunctionCatalogExecutionClient,
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
    "replacement",
    (
        "viewer",
        "new_incarnation",
        "missing_identity",
        "application",
        "data_port",
        "control_port",
    ),
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
        "data_port": replace(expected, port=expected.port + 1),
        "control_port": replace(expected, control_port=expected.control_port + 1),
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


@pytest.mark.parametrize("failure", ("malformed", "unknown", "timeout"))
def test_unverifiable_ping_is_recoverable_without_catalog_delivery(
    connection, monkeypatch, failure
):
    client, expected, observed = connection

    def send(payload, *, timeout_ms):
        observed.append(payload)
        if failure == "timeout":
            raise TimeoutError("original ping could not respond")
        return {} if failure == "malformed" else {"type": "unknown"}

    monkeypatch.setattr(client, "_send_control_request", send)
    with pytest.raises(
        FunctionCatalogEndpointUnavailableError, match="Could not verify"
    ) as caught:
        client.search_function_catalog(FunctionSearchRequest())
    assert caught.value.__cause__ is not None
    assert len(observed) == 1
    assert client.connected_endpoint is expected


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
        lambda c: c.function_catalog_preparation(
            FunctionCatalogPreparationStatusRequest(
                FunctionCatalogPreparationHandle(
                    ExecutionConnectionSpec(port=22319), ProcessIdentity.current()
                )
            )
        ),
        lambda c: c.function_catalog_preparation(
            FunctionCatalogPreparationCancelRequest(
                FunctionCatalogPreparationHandle(
                    ExecutionConnectionSpec(port=22319), ProcessIdentity.current()
                )
            )
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

    class AuditedCatalogClient(AuditCapability, FunctionCatalogExecutionClient):
        def endpoint_compatibility(self):
            return OPENHCS_ENDPOINT_APPLICATION.compatibility_with(
                self.connected_endpoint.application
            )

        def serialize_task(self, task, config=None):
            pytest.fail("This independent catalog client does not submit science")

        def _spawn_server_process(self):
            pytest.fail("Catalog-only declarations must not create a runtime")

        def send_data(self, data):
            pytest.fail("Catalog controls do not send scientific arrays")

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
        FunctionCatalogExecutionClient,
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


@pytest.mark.parametrize("selection", ("valid", "viewer", "wrong_response_connection"))
def test_explicit_selection_alone_can_replace_closed_session(monkeypatch, selection):
    config = replace(OPENHCS_ZMQ_CONFIG, default_port=22319)
    old = ZMQExecutionClient(config=config)
    expired = replace(
        _handshake(old),
        process_identity=replace(ProcessIdentity.current(), create_time=0),
    )
    old._connection = AttachedEndpointConnection(expired)
    fresh = ZMQExecutionClient(config=config)
    expected = _handshake(fresh)
    if selection == "viewer":
        expected = replace(expected, server_role=ServerRole.VIEWER)
    actual_connection = ExecutionConnectionSpec(port=22319)
    response_connection = (
        actual_connection
        if selection != "wrong_response_connection"
        else ExecutionConnectionSpec(port=22320)
    )
    state = FunctionCatalogPreparationState(
        schema_version="openhcs.agent.v1",
        handle=FunctionCatalogPreparationHandle(
            response_connection, expected.process_identity
        ),
        outcome=FunctionCatalogPreparationOutcome.READY,
        progress=EndpointStartupStatus(EndpointStartupPhase.CONNECTED, "source ready"),
    )
    page = catalog_page(
        items=(), catalog_items=(), total=0, limit=1, query=None, library=None
    )
    delivered = []

    def attach(timeout):
        fresh._connection = AttachedEndpointConnection(expected)
        return True

    def send(payload, *, timeout_ms):
        delivered.append(payload)
        if payload[MessageFields.TYPE] == ControlMessageType.PING.value:
            return expected.to_dict()
        if (
            payload["request"].message_type
            is FunctionCatalogControlMessageType.START_PREPARATION
        ):
            return FunctionCatalogPreparationStateControlResponse(
                state
            ).to_control_response()
        return FunctionCatalogControlResponse(page).to_control_response()

    monkeypatch.setattr(fresh, "_is_port_in_use", lambda port: True)
    monkeypatch.setattr(fresh, "_attach_existing_endpoint", attach)
    monkeypatch.setattr(
        fresh,
        "connect",
        lambda **kwargs: pytest.fail("Explicit selection must not start native"),
    )
    monkeypatch.setattr(fresh, "_send_control_request", send)
    clients = iter((old, fresh))
    service = ZMQFunctionCatalogService(
        lambda: config, client_factory=lambda endpoint: next(clients)
    )
    original = service._client_for(config)
    with pytest.raises(FunctionCatalogEndpointUnavailableError, match="has exited"):
        service.search(query="original closed owner")
    if selection == "valid":
        assert service.start_catalog_preparation(actual_connection) is state
        assert service._client_session.client is fresh
        assert service.search(query="new explicit owner") is page
        assert original.connected_endpoint is None
    else:
        with pytest.raises((FunctionCatalogEndpointUnavailableError, RuntimeError)):
            service.start_catalog_preparation(actual_connection)
        assert service._client_session.client is original
        assert original.connected_endpoint is expired
        assert not fresh.is_connected()
    service.close()


def test_original_req_transport_checks_current_peer_before_catalog():
    """Source-only REP peer; no application, viewer, JVM or child process."""
    import zmq

    context = zmq.Context()
    socket = context.socket(zmq.REP)
    socket.setsockopt(zmq.LINGER, 0)
    control_port = socket.bind_to_random_port("tcp://127.0.0.1")
    client = ZMQExecutionClient(
        port=control_port - OPENHCS_ZMQ_CONFIG.control_port_offset,
        host="127.0.0.1",
        transport_mode=TransportMode.TCP,
        persistent=True,
    )
    expected = _handshake(client)
    client._connection = AttachedEndpointConnection(expected)
    foreign = replace(expected, server_role=ServerRole.VIEWER)
    observed = []

    def peer():
        if socket.poll(2000):
            payload = socket.recv_pyobj()
            observed.append(payload)
            socket.send_pyobj(foreign.to_dict())
            # A foreign peer must not receive a following catalog control.
            if socket.poll(100):
                observed.append(socket.recv_pyobj())
                socket.send_pyobj({"status": "error"})

    worker = threading.Thread(target=peer)
    worker.start()
    try:
        with pytest.raises(
            FunctionCatalogEndpointUnavailableError, match="no longer belongs"
        ):
            client.search_function_catalog(FunctionSearchRequest(query="background"))
        worker.join(timeout=3)
        assert not worker.is_alive()
        assert [payload[MessageFields.TYPE] for payload in observed] == [
            ControlMessageType.PING.value
        ]
        assert client.connected_endpoint is expected
    finally:
        worker.join(timeout=3)
        client.disconnect()
        socket.close()
        context.term()


def test_async_catalog_refresh_keeps_original_session_owner(monkeypatch):
    config = replace(OPENHCS_ZMQ_CONFIG, default_port=22319)
    owner = ZMQExecutionClient(config=config)
    expected = _handshake(owner)
    owner._connection = AttachedEndpointConnection(expected)
    senders = []
    sent = []
    page = catalog_page(
        items=(), catalog_items=(), total=0, limit=1, query=None, library=None
    )

    def factory(endpoint):
        if not senders:
            senders.append(owner)
            return owner
        sender = ZMQExecutionClient(config=endpoint)

        def send(payload, *, timeout_ms):
            sent.append(payload)
            if payload[MessageFields.TYPE] == ControlMessageType.PING.value:
                return expected.to_dict()
            return FunctionCatalogControlResponse(page).to_control_response()

        monkeypatch.setattr(sender, "_send_control_request", send)
        monkeypatch.setattr(
            sender,
            "connect_existing",
            lambda **kwargs: pytest.fail("Worker must not select a replacement"),
        )
        senders.append(sender)
        return sender

    service = ZMQFunctionCatalogService(lambda: config, client_factory=factory)
    try:
        assert service.prepare().result(timeout=2) is page
        assert service._client_session.client is owner
        assert owner.connected_endpoint is expected
        assert all(not sender.is_connected() for sender in senders[1:])
        assert len(sent) == 2
        monkeypatch.setattr(owner, "known_server_process_is_alive", lambda: False)
        with pytest.raises(FunctionCatalogEndpointUnavailableError, match="has exited"):
            service.prepare().result(timeout=2)
        assert len(sent) == 2
        assert service._client_session.client is owner
        assert owner.connected_endpoint is expected
    finally:
        service.close()
    assert not owner.is_connected()
