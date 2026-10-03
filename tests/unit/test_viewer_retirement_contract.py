"""Declaration-owned MCP/CLI request, receipt and error projection; no server launch."""
import argparse
import asyncio
import json
from types import SimpleNamespace

import pytest
from polystore.streaming.identity import StreamProducerIdentity
from zmqruntime.config import TransportMode

from openhcs.agent.capabilities import RetireViewerWindowLayersCapability
from openhcs.agent.dto.common import SCHEMA_VERSION
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import (
    ViewerWindowLayerRetirementRequest, ViewerWindowLayerRetirementResult,
)
from openhcs.agent.services.viewer_window_service import (
    ViewerWindowService, ZMQViewerWindowGateway,
)
from openhcs.mcp.server import (
    GeneratedMcpViewerRequestToolBinding, build_server,
    generated_viewer_request_capability_declarations,
)
from openhcs.mcp.dev_client_commands.viewer import RetireViewerCommandSpec
from openhcs.runtime.viewer_protocol import ViewerLayerRetirementReceipt
from openhcs.serialization.json import to_jsonable


def producers():
    return {"exact-route": [to_jsonable(StreamProducerIdentity(
        origin="pipeline", output_kind="main", output_key="candidate",
        projection_key="candidate", invocation_key="original-incarnation",
    ))]}


def request():
    return ViewerWindowLayerRetirementRequest.from_fields(
        connection=ExecutionConnectionSpec(port=5584, transport_mode=TransportMode.TCP),
        expected_producers=producers(),
    )


def test_generated_mcp_binding_discovers_and_executes_new_declaration_without_consumer_edits():
    assert RetireViewerWindowLayersCapability in generated_viewer_request_capability_declarations()
    captured = []
    received = []
    class Service:
        def presentation(self, value):
            received.append(value)
            return ViewerWindowLayerRetirementResult(
                schema_version=SCHEMA_VERSION, connection=value.connection,
                observed=True, applied=True, retired_route_keys=("exact-route",),
                remaining_route_keys=("retained-raw",),
            )
    def tool_decorator(*, capability):
        def register(function):
            captured.append((capability, function))
            return function
        return register
    # This is the original generated callable/codec/invocation, not a mirrored tool.
    GeneratedMcpViewerRequestToolBinding.bind_to_server(
        RetireViewerWindowLayersCapability,
        SimpleNamespace(viewer_window_service=Service()), tool_decorator,
    )
    capability, tool = captured[0]
    result = tool(port=5584, transport_mode="tcp", expected_producers=producers())
    assert capability.name == "openhcs_retire_viewer_window_layers"
    assert len(received) == 1 and isinstance(received[0], ViewerWindowLayerRetirementRequest)
    assert received[0].retirement.expected_producers["exact-route"][0].invocation_key == "original-incarnation"
    assert result["applied"] and result["retired_route_keys"] == ["exact-route"]
    assert result["remaining_route_keys"] == ["retained-raw"]
    assert "operation_deadline" not in tool.__signature__.parameters


def test_cli_leaf_projects_same_typed_request_and_connection():
    command = RetireViewerCommandSpec()
    parser = argparse.ArgumentParser()
    command.configure_parser(parser)
    arguments = command.tool_arguments(parser.parse_args([
        "5584", "--transport-mode", "tcp", "--expected-producers", json.dumps(producers()),
    ]))
    assert arguments == request().as_tool_arguments()


def test_real_fastmcp_constructs_and_decodes_original_producer_identity():
    # A fake registration decorator cannot exercise FastMCP's schema generation.
    server = build_server()
    capability = RetireViewerWindowLayersCapability.to_spec()
    registered = server._tool_manager.get_tool(capability.name)
    model = registered.fn_metadata.arg_model
    payload = request().as_tool_arguments()
    arguments = model.model_validate(payload)
    identity = arguments.expected_producers['exact-route'][0]
    assert isinstance(identity, StreamProducerIdentity)
    assert identity == request().retirement.expected_producers['exact-route'][0]
    projected = ViewerWindowLayerRetirementRequest.from_fields(
        connection=request().connection,
        expected_producers=arguments.expected_producers,
    )
    assert projected.as_tool_arguments() == payload
    tools = asyncio.run(server.list_tools())
    advertised = next(tool for tool in tools if tool.name == capability.name)
    producer_schema = advertised.inputSchema['$defs']['StreamProducerIdentity']
    assert set(producer_schema['properties']) == set(identity.to_payload())
    from pydantic import ValidationError
    with pytest.raises(ValidationError):
        model.model_validate({**payload, 'expected_producers': {'exact-route': [{}]}})
    with pytest.raises(ValidationError):
        model.model_validate({**payload, 'undeclared': 'must not dispatch'})


@pytest.mark.parametrize("native", [
    {"status": "error", "message": "original terminal error"},
    {"status": "success", "retirement": {"applied": True, "retired_route_keys": ["foreign"], "remaining_route_keys": []}},
    {"status": "success", "retirement": {"applied": True, "retired_route_keys": ["exact-route"], "remaining_route_keys": ["exact-route"]}},
])
def test_service_rejects_failed_or_mismatched_retirement_receipt(native):
    class NativeReplyGateway(ZMQViewerWindowGateway):
        def _send_control_message(self, value, message):
            assert value.operation_deadline is not None
            return native
    result = ViewerWindowService(NativeReplyGateway()).presentation(request())
    assert not result.applied and not result.observed and result.errors
    assert not result.retired_route_keys


def test_receipt_uses_original_declaration_codec_and_envelope_error_mro():
    receipt = ViewerLayerRetirementReceipt.from_wire_mapping({
        "applied": True, "retired_route_keys": ["exact-route"], "remaining_route_keys": ["raw"],
    })
    assert receipt.retired_route_keys == ("exact-route",)
    with pytest.raises(ValueError, match="undeclared"):
        ViewerLayerRetirementReceipt.from_wire_mapping({"extra": 1})
    assert request().start_operation().control_deadline().timeout_ms == 5000
