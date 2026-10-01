"""Original successful native receipt, replayed offline: NEVER start a process."""
from dataclasses import dataclass
import json
from pathlib import Path

import pytest

from openhcs.agent.capabilities import AgentResultFamilyContract, StartOwnedRuntimeCapability
from openhcs.agent.dto.common import AgentError, AgentResultEnvelope, SCHEMA_VERSION
from openhcs.agent.dto.execution import RuntimeBootstrapState, RuntimeBootstrapHandle
from openhcs.mcp.dev_client_core import (
    McpDevToolBatchResponse, McpDevToolResult, McpDevPayloadFailure,
    state_surface_document, state_surface_payload, ui_bridge_operation_result,
    workflow_result_payload,
)
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer
from openhcs.serialization.json import to_jsonable


def test_actual_saved_successful_startup_descends_without_presentation():
    path = Path(__file__).resolve().parents[2] / "fixtures/mcp/start-owned-runtime-400.json"
    response = McpDevToolBatchResponse.for_rendering(json.loads(path.read_text()))
    value = response.payload_for(StartOwnedRuntimeCapability.to_spec())
    assert type(value) is RuntimeBootstrapState
    assert isinstance(value.handle, RuntimeBootstrapHandle)
    assert value.handle.process_identity.pid == 2153942
    assert value.handle.process_identity.create_time == 1790885239.3
    assert value.handle.connection.port == 5993
    assert isinstance(value.handle.launch_plan.storage_dir, Path)
    assert value.progress.sequence == 0 and value.process_alive is True and value.ready is False
    # This is a response replay, NOT current process liveness or live readiness.


@dataclass(frozen=True, kw_only=True)
class DeclaredFact:
    value: str


@dataclass(frozen=True, kw_only=True)
class OwnedResult(AgentResultEnvelope):
    fact: DeclaredFact

    def describe(self):
        return self.fact.value


class IndependentDescriptionCapability:
    def describe(self):
        return "independent:" + super().describe()


@dataclass(frozen=True, kw_only=True)
class RenderlessResult(IndependentDescriptionCapability, OwnedResult):
    pass


class RenderlessCapability(StartOwnedRuntimeCapability):
    name = "openhcs_decoder_renderless_case400"
    cli_command = "decoder-renderless-case400"
    output_contract = RenderlessResult


def test_renderless_new_declaration_decodes_and_executes_cooperative_mro():
    assert McpDevOutputRenderer.for_output_contract(RenderlessResult) is None
    original = RenderlessResult(schema_version=SCHEMA_VERSION, fact=DeclaredFact(value="owned"))
    result = McpDevToolResult(RenderlessCapability.name, False, (to_jsonable(original),)).decoded_for_rendering()
    value = result.first_decoded_payload()
    assert type(value) is RenderlessResult and type(value.fact) is DeclaredFact
    assert value.describe() == "independent:owned"
    assert result.decoded_for_rendering().first_decoded_payload() is value


def test_renderless_malformed_record_is_rejected_with_original_receipt():
    raw = {"schema_version": SCHEMA_VERSION, "fact": {}}
    result = McpDevToolResult(RenderlessCapability.name, False, (raw,)).decoded_for_rendering()
    assert result.first_decoded_payload() is None
    assert isinstance(result.payloads[0], McpDevPayloadFailure)
    assert result.payloads[0].receipt is raw and result.has_errors()
    assert result.decoded_for_rendering().payloads[0] is result.payloads[0]


@pytest.mark.parametrize("raw", (
    {"schema_version": SCHEMA_VERSION, "fact": {"value": "owned"}, "unknown": True},
    {"schema_version": SCHEMA_VERSION, "fact": {"value": "owned", "unknown": True}},
    {"schema_version": SCHEMA_VERSION, "fact": {"value": 7}},
))
def test_original_contract_rejects_extra_fields_and_invalid_nested_values(raw):
    result = McpDevToolResult(RenderlessCapability.name, False, (raw,)).decoded_for_rendering()
    assert isinstance(result.payloads[0], McpDevPayloadFailure)
    assert result.payloads[0].receipt is raw and result.first_decoded_payload() is None
    assert result.has_errors() and len(result.payloads[0].errors) == 1


def test_declared_errors_remain_typed_and_unknown_tool_stays_external():
    error = AgentError(code="original_failure", message="retain")
    original = RenderlessResult(schema_version=SCHEMA_VERSION, fact=DeclaredFact(value="owned"), errors=(error,))
    result = McpDevToolResult(RenderlessCapability.name, True, (to_jsonable(original),)).decoded_for_rendering()
    assert result.has_errors() and result.first_decoded_payload().errors == (error,)
    unknown = McpDevToolResult("external_unknown_tool400", False, ({"external": True},))
    assert unknown.decoded_for_rendering() is unknown
    empty = McpDevToolResult(RenderlessCapability.name, False, ())
    assert empty.decoded_for_rendering().first_decoded_payload() is None


@dataclass(frozen=True, kw_only=True)
class AnotherDeclaredResult(AgentResultEnvelope):
    token: int


def declared_alternatives() -> RenderlessResult | AnotherDeclaredResult:
    raise AssertionError("Producer declaration is introspected, NEVER invoked")


class UnionCapability(StartOwnedRuntimeCapability):
    name = "openhcs_decoder_union_case400"
    cli_command = "decoder-union-case400"
    output_contract = AgentResultFamilyContract(RenderlessResult, declared_alternatives)


@pytest.mark.parametrize("original", (
    RenderlessResult(schema_version=SCHEMA_VERSION, fact=DeclaredFact(value="one")),
    AnotherDeclaredResult(schema_version=SCHEMA_VERSION, token=7),
))
def test_producer_declared_union_without_any_presentation_roster(original):
    result = McpDevToolResult(UnionCapability.name, False, (to_jsonable(original),)).decoded_for_rendering()
    assert type(result.first_decoded_payload()) is type(original)
    assert result.first_decoded_payload() == original


def test_unknown_union_shape_preserves_each_rejection():
    raw = {"schema_version": SCHEMA_VERSION}
    result = McpDevToolResult(UnionCapability.name, False, (raw,)).decoded_for_rendering()
    assert result.first_decoded_payload() is None
    assert isinstance(result.payloads[0], McpDevPayloadFailure)
    assert len(result.payloads[0].errors) == 2 and result.payloads[0].receipt is raw


@pytest.mark.parametrize("tool", ("external_unknown_tool400", RenderlessCapability.name))
def test_unknown_raw_or_rejected_records_cannot_masquerade_as_ui_contract(tool):
    raw = {"payload": {"rows": []}, "status": "completed"}
    result = McpDevToolResult(tool, False, (raw,))
    assert state_surface_document(result) is None
    assert state_surface_payload(result) == {}
    assert ui_bridge_operation_result(result) is None
    assert workflow_result_payload(result) is None


def test_nominal_member_access_does_not_accept_other_declared_union_branch():
    original = AnotherDeclaredResult(schema_version=SCHEMA_VERSION, token=9)
    result = McpDevToolResult(UnionCapability.name, False, (to_jsonable(original),))
    assert result.decoded_payload_as(RenderlessResult) is None
    accepted = result.decoded_payload_as(AnotherDeclaredResult)
    assert type(accepted) is AnotherDeclaredResult and accepted == original
