"""Typed input declarations through unchanged generated command consumers."""

from dataclasses import dataclass, field, replace
import json

import pytest
from python_introspect import dataclass_from_mapping
from zmqruntime.config import TransportMode
from zmqruntime.messages import ProcessIdentity

from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    StartFunctionCatalogPreparationCapability,
)
from openhcs.agent.dto.common import AgentDataclassCliRequest
from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
from openhcs.agent.dto.functions import FunctionCatalogPreparationHandle
from openhcs.mcp.dev_client import _build_parser, _calls_from_args
from openhcs.mcp.dev_client_core import McpDevCliUsageError
from openhcs.serialization.json import to_jsonable


@pytest.fixture(scope="module")
def parser():
    return _build_parser()


def call(parser, *argv):
    return _calls_from_args(parser.parse_args(argv))[0]


def test_generated_start_uses_actual_connection_owner(parser):
    request = ExecutionConnectionSpec(
        host="localhost", port=5993, transport_mode=TransportMode.TCP, persistent=False
    )
    observed = call(
        parser,
        "start-function-catalog-preparation",
        "--port",
        "5993",
        "--host",
        "localhost",
        "--transport-mode",
        "tcp",
        "--no-persistent",
    )
    assert observed.name == "openhcs_start_function_catalog_preparation"
    assert observed.arguments == request.tool_arguments() == request.as_tool_arguments()
    recovered = dataclass_from_mapping(ExecutionConnectionSpec, observed.arguments)
    assert recovered == request
    assert recovered.require_port("catalog preparation") == 5993


def test_default_absence_remains_owned_not_implicit_route(parser):
    observed = call(parser, "start-function-catalog-preparation")
    request = dataclass_from_mapping(ExecutionConnectionSpec, observed.arguments)
    assert request == ExecutionConnectionSpec()
    with pytest.raises(ValueError, match="requires an explicit port"):
        request.require_port("catalog preparation")


@pytest.mark.parametrize("mode", tuple(TransportMode))
@pytest.mark.parametrize("persistent", (True, False))
def test_generated_connection_enum_boolean_and_zero_contract(parser, mode, persistent):
    observed = call(
        parser,
        "start-function-catalog-preparation",
        "--port",
        "0",
        "--transport-mode",
        mode.value,
        "--persistent" if persistent else "--no-persistent",
    )
    assert (
        observed.arguments
        == ExecutionConnectionSpec(
            port=0, transport_mode=mode, persistent=persistent
        ).tool_arguments()
    )


@pytest.mark.parametrize("port", ("-1", "65536"))
def test_generated_port_keeps_annotated_constraints(parser, port):
    with pytest.raises(McpDevCliUsageError):
        call(parser, "start-function-catalog-preparation", "--port", port)


@pytest.mark.parametrize("argv", (("--port", "true"), ("--transport-mode", "bogus")))
def test_malformed_scalar_never_reaches_call_dispatch(parser, argv):
    with pytest.raises(SystemExit) as error:
        call(parser, "start-function-catalog-preparation", *argv)
    assert error.value.code == 2


@pytest.mark.parametrize(
    "command",
    (
        "get-function-catalog-preparation-status",
        "cancel-function-catalog-preparation",
    ),
)
def test_exact_nested_handle_survives_real_generated_and_generic_calls(parser, command):
    owner = ProcessIdentity.current()
    handle = FunctionCatalogPreparationHandle(
        connection=ExecutionConnectionSpec(port=5993, transport_mode=TransportMode.TCP),
        server_identity=owner,
    )
    arguments = to_jsonable(handle)
    generated = call(
        parser,
        command,
        "--connection",
        json.dumps(arguments["connection"]),
        "--server-identity",
        json.dumps(arguments["server_identity"]),
    )
    generic = call(
        parser,
        "call",
        generated.name,
        "--arguments",
        json.dumps(arguments),
    )
    assert generated.arguments == generic.arguments == arguments
    recovered = dataclass_from_mapping(
        FunctionCatalogPreparationHandle, generated.arguments
    )
    assert recovered == handle
    recovered.require_current_owner()
    with pytest.raises(RuntimeError, match="owner changed"):
        replace(
            recovered, server_identity=replace(owner, create_time=owner.create_time + 1)
        ).require_current_owner()


@pytest.mark.parametrize(
    "bad",
    (
        {"port": True},
        {"port": 65536},
        {"host": " "},
        {"port": "5993"},
        {"port": 5993, "extra": "not declared"},
    ),
)
def test_nested_connection_errors_keep_real_contract_before_dispatch(parser, bad):
    with pytest.raises(McpDevCliUsageError):
        call(
            parser,
            "get-function-catalog-preparation-status",
            "--connection",
            json.dumps(bad),
            "--server-identity",
            json.dumps(to_jsonable(ProcessIdentity.current())),
        )


@pytest.mark.parametrize("text", ("[]", "null", "{broken"))
def test_nested_malformed_json_is_cli_error(parser, text):
    with pytest.raises(SystemExit) as error:
        call(parser, "get-function-catalog-preparation-status", "--connection", text)
    assert error.value.code == 2


def test_missing_handle_is_local_error_not_new_owner(parser):
    with pytest.raises(McpDevCliUsageError):
        call(parser, "get-function-catalog-preparation-status")


@pytest.mark.parametrize("reverse", (False, True))
def test_single_declaration_extension_and_cooperative_diamond(reverse, monkeypatch):
    events = []
    decoded = []

    class CanonicalHost(AgentDataclassCliRequest):
        @classmethod
        def from_fields(cls, **kwargs):
            events.append("host")
            return super().from_fields(**{**kwargs, "host": kwargs["host"].lower()})

    class EphemeralConnection(AgentDataclassCliRequest):
        @classmethod
        def from_fields(cls, **kwargs):
            events.append("ephemeral")
            return super().from_fields(**{**kwargs, "persistent": False})

    bases = (
        (EphemeralConnection, CanonicalHost)
        if reverse
        else (CanonicalHost, EphemeralConnection)
    )

    @dataclass(frozen=True, kw_only=True)
    class ExtendedConnection(*bases, ExecutionConnectionSpec):
        request_tag: str = "new"
        trace_enabled: bool = True

    import openhcs.agent.dto.common as common

    original_decode = common.dataclass_from_mapping

    def observe_decode(target, values):
        result = original_decode(target, values)
        decoded.append(result)
        return result

    monkeypatch.setattr(common, "dataclass_from_mapping", observe_decode)

    class NewCapability(StartFunctionCatalogPreparationCapability):
        name = "openhcs_s1_generated_input_extension"
        cli_command = "s1-generated-input-extension"
        input_contract = ExtendedConnection

    try:
        generated = call(
            _build_parser(),
            NewCapability.cli_command,
            "--host",
            "LOCALHOST",
            "--port",
            "5993",
            "--request-tag",
            "retained",
            "--no-trace-enabled",
        )
        assert generated.arguments == {
            "host": "localhost",
            "port": 5993,
            "transport_mode": None,
            "persistent": False,
            "request_tag": "retained",
            "trace_enabled": False,
        }
        assert events == (["ephemeral", "host"] if reverse else ["host", "ephemeral"])
        assert len(decoded) == 1 and type(decoded[0]) is ExtendedConnection
        assert decoded[0].request_tag == "retained"
        # CLI input retains the subclass's fields; the distinct credential-free
        # execution projection still carries only the public connection owner.
        assert (
            decoded[0].tool_arguments()
            == ExecutionConnectionSpec(port=5993, persistent=False).tool_arguments()
        )
        assert ExtendedConnection.__mro__.count(AgentDataclassCliRequest) == 1
        assert ExtendedConnection.__mro__.count(ExecutionConnectionSpec) == 1
    finally:
        del AgentCapabilityDeclaration.__registry__[NewCapability.name]


@pytest.mark.parametrize("negative", (False, True))
def test_new_declared_default_factory_runs_only_at_typed_construction(negative):
    constructed = []

    def default_probe():
        constructed.append("default")
        return True

    @dataclass(frozen=True, kw_only=True)
    class FactoryConnection(ExecutionConnectionSpec):
        probe: bool = field(default_factory=default_probe)

    class FactoryCapability(StartFunctionCatalogPreparationCapability):
        name = "openhcs_s1_generated_factory_extension"
        cli_command = "s1-generated-factory-extension"
        input_contract = FactoryConnection

    try:
        parser = _build_parser()
        assert not constructed
        observed = call(
            parser,
            FactoryCapability.cli_command,
            "--port",
            "5993",
            *(("--no-probe",) if negative else ()),
        )
        assert observed.arguments["probe"] is (not negative)
        assert constructed == ([] if negative else ["default"])
    finally:
        del AgentCapabilityDeclaration.__registry__[FactoryCapability.name]
