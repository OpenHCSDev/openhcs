"""Bounded source journeys through original commands, ingress and presentation."""

from __future__ import annotations

import ast
import asyncio
from dataclasses import dataclass, replace
from pathlib import Path
import subprocess
import sys

import pytest

from openhcs.agent.capabilities import SamplePlateImageCapability, agent_capabilities
from openhcs.agent.dto.common import AgentError, SCHEMA_VERSION
from openhcs.agent.dto.plate import PlateImageSampleResult, SelectedPlateImageSampleResult
from openhcs.agent.dto.ui_bridge import UiPlateManagerRowState
from openhcs.agent.dto.viewer import ViewerWindowImageSampleRecord, ViewerWindowImageSampleResult
from openhcs.mcp import dev_client
from openhcs.mcp.dev_client_commanding import CapabilityBackedCommandSpec
from openhcs.mcp.dev_client_core import (
    McpDevClientPhase, McpDevPayloadFailure, McpDevServerSpec,
    McpDevToolBatchResponse, McpDevToolResult,
)
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer
from openhcs.mcp.dev_client_renderers.plate import PlateImageSampleRenderer, SelectedPlateSampleRenderer
from openhcs.mcp.dev_client_renderers.viewer import ViewerImageSampleRenderer
from openhcs.runtime.viewer_protocol import ViewerArrayValueSummary
from python_introspect import to_jsonable


@pytest.fixture(autouse=True)
def forbid_native_or_provider(monkeypatch):
    def forbidden(*args, **kwargs):
        raise AssertionError("Source sampling controls must not spawn a process")
    monkeypatch.setattr(subprocess, "Popen", forbidden)
    monkeypatch.setattr(asyncio, "create_subprocess_exec", forbidden)
    monkeypatch.setattr(asyncio, "create_subprocess_shell", forbidden)


def sample(**kwargs):
    return replace(PlateImageSampleResult(
        schema_version=SCHEMA_VERSION, plate_path="source-plate", requested_image_path="image.tif",
        virtual_path="images/image.tif", source_path="physical/image.tif",
        shape=(1, 2, 2), resolution_shape=(1, 2, 2), dtype="uint16",
        minimum=0, maximum=4, mean=2.5, selected_resolution_index=0,
        resolution_count=1, downsample_yx=(1.0, 1.0), statistics_scope="source_resolution",
        sample_shape=(1, 2, 2), sample_included=True, sample_values=[[[0, 2], [3, 4]]],
    ), **kwargs)


def selected_row():
    return UiPlateManagerRowState(
        plate_scope_id="selected-root", name="selection", plate_root="selected-root",
        cppipe_path=None, selected=True, initialized=True, compiled=False,
        init_pending=False, compile_pending=False, execution_active=False,
        status_prefix="", orchestrator_state=None, execution_id=None,
        terminal_status=None, runtime_state=None, runtime_percent=None, queue_position=None,
    )


def selected(value):
    return SelectedPlateImageSampleResult(
        schema_version=SCHEMA_VERSION,
        selected_plate=to_jsonable(selected_row()),
        image_path="image.tif", auto_selected_image_path=False, sample=value,
    )


def batch(value, capability):
    receipt = {"isError": False, "structuredContent": to_jsonable(value), "content": []}
    return McpDevToolBatchResponse.from_results(
        McpDevServerSpec(sys.executable), (McpDevToolResult.from_payload(capability.name, receipt),),
    )


def command_render(response, argv):
    args = dev_client._build_parser().parse_args(argv)
    return dev_client.McpDevCommandSpec.for_name(args.command).render_result(response, args)


@pytest.mark.parametrize("structured", [False, True])
@pytest.mark.parametrize("selected_case", [False, True])
def test_original_session_framing_to_generated_sampling_command(structured, selected_case, monkeypatch):
    from test_mcp_dev_client_pipeline_results import ControlledWireSession
    import openhcs.mcp.dev_client_core as ingress

    value = selected(sample()) if selected_case else sample()
    argv = ("selected-plate-sample",) if selected_case else ("sample-plate-image", "source-plate", "image.tif")
    args = dev_client._build_parser().parse_args(argv)
    command = dev_client.McpDevCommandSpec.for_name(args.command)
    peer = ControlledWireSession((value,), structured=structured)
    decoded = []
    original_decode = ingress.dataclass_from_mapping
    def observe(contract, receipt):
        decoded.append(contract)
        return original_decode(contract, receipt)
    monkeypatch.setattr(ingress, "dataclass_from_mapping", observe)
    response = asyncio.run(command.run_session(peer, args))
    assert decoded == [type(value)]
    assert len(peer.calls) == 1
    before = to_jsonable(response)
    assert "Image: images/image.tif" in command.render_result(response, args)
    assert to_jsonable(response) == before
    assert decoded == [type(value)]


@pytest.mark.parametrize("selected_case", [False, True])
@pytest.mark.parametrize("generic_call", [False, True])
def test_generated_commands_retain_decoded_sampling_facts(monkeypatch, selected_case, generic_call):
    capability = agent_capabilities.ui_sample_selected_plate_image if selected_case else agent_capabilities.sample_plate_image
    value = selected(sample()) if selected_case else sample()
    response = batch(value, capability)
    decoded = response.results[0].first_decoded_payload()
    assert type(decoded) is type(value)
    if selected_case:
        assert type(decoded.sample) is PlateImageSampleResult
        assert decoded.selected_plate == to_jsonable(selected_row())

    def forbidden(value):
        raise AssertionError("Typed sampling must not flatten an owned result to JSON")
    monkeypatch.setattr(dev_client, "to_jsonable", forbidden)
    monkeypatch.setattr("python_introspect.jsonable.to_jsonable", forbidden)
    argv = ("call", capability.name, "--arguments", "{}") if generic_call else (
        ("selected-plate-sample",) if selected_case else ("sample-plate-image", "source-plate", "image.tif")
    )
    rendered = command_render(response, argv)
    assert "Image: images/image.tif" in rendered
    assert "Source: physical/image.tif" in rendered
    assert "source_shape=1x2x2 resolution_shape=1x2x2 downsample_yx=1.0x1.0" in rendered
    assert "mean=2.500" in rendered
    assert "Sample values:" in rendered
    if selected_case:
        assert "Selected plate: selection root=selected-root target=selected" in rendered
        assert "Selected image: image.tif auto=False" in rendered


@pytest.mark.parametrize("selected_case", [False, True])
@pytest.mark.parametrize("reason,shape,hint", [
    ("max_array_elements_exceeded", (1, 8, 8), "--max-array-elements 64 or smaller --width/--height"),
    ("sample has 256 elements, above max_array_elements=40", (1, 16, 16), "--max-array-elements 256"),
    ("array_values_not_requested", (1, 2, 2), "--include-array-values --max-array-elements 4"),
    ("empty", (), "Sample values omitted: empty"),
    ("max_array_elements_exceeded", (1, 0, 2), "--max-array-elements 0"),
])
def test_omission_and_budget_advice_preserved(selected_case, reason, shape, hint):
    value = sample(sample_included=False, sample_values=(), sample_shape=shape, sample_omitted_reason=reason)
    capability = agent_capabilities.ui_sample_selected_plate_image if selected_case else agent_capabilities.sample_plate_image
    response = batch(selected(value) if selected_case else value, capability)
    renderer = SelectedPlateSampleRenderer if selected_case else PlateImageSampleRenderer
    assert hint in renderer.render(response)


def test_legitimate_absent_sample_and_false_zero_empty_are_distinct():
    response = batch(selected(None), agent_capabilities.ui_sample_selected_plate_image)
    rendered = SelectedPlateSampleRenderer.render(response)
    assert "Sample: <none>" in rendered
    assert "auto=False" in rendered
    zero = sample(virtual_path="", dtype="", mean=0.0, minimum=False, maximum=0,
                  sample_shape=(), sample_values=[], sample_included=True)
    rendered = PlateImageSampleRenderer.render(batch(zero, agent_capabilities.sample_plate_image))
    assert "Image: \n" in rendered
    assert "dtype= min=False max=0 mean=0.000" in rendered
    assert "shape= included=True" in rendered
    assert "Sample values:\n[]" in rendered


@pytest.mark.parametrize("values,count", [([False, 0, "", None], 3), (list(range(65)), 65), ({"a": [0, False], "b": ""}, 3)])
def test_shared_preview_policy_and_richer_viewer_owner(values, count):
    assert McpDevOutputRenderer.json_value_count(values) == count
    response = batch(sample(sample_values=values), agent_capabilities.sample_plate_image)
    rendered = PlateImageSampleRenderer.render(response)
    assert ("65 elements; pass --json" in rendered) == (count > 64)
    record = ViewerWindowImageSampleRecord(
        layer_route_key="layer", layer_title="image", payload_route_key="payload",
        data_type="image", path="source", components={}, array_values=(values,),
        array_value_summary=ViewerArrayValueSummary(requested=True, included=True, shape=(1, count)),
    )
    viewer = ViewerWindowImageSampleResult(schema_version=SCHEMA_VERSION, observed=True, records=(record,))
    text = ViewerImageSampleRenderer.render(batch(viewer, agent_capabilities.sample_viewer_window_image))
    assert ("sample values:" in text) == (count <= 64)
    assert record.array_value_summary.shape_element_count == count


@pytest.mark.parametrize("selected_case", [False, True])
def test_original_typed_diagnostics_retained_once(selected_case):
    error = AgentError("sample_failure", "retained cause", "retained hint")
    value = sample(errors=(error,))
    capability = agent_capabilities.ui_sample_selected_plate_image if selected_case else agent_capabilities.sample_plate_image
    response = batch(replace(selected(value), errors=(error,)) if selected_case else value, capability)
    text = (SelectedPlateSampleRenderer if selected_case else PlateImageSampleRenderer).render(response)
    assert "failed" in text
    assert text.count("sample_failure") == 1
    assert "retained cause" in text and "retained hint" in text
    assert response.has_errors()


@pytest.mark.parametrize("receipt", [{"alien": 1}, {"schema_version": SCHEMA_VERSION}, {"schema_version": SCHEMA_VERSION, "plate_path": "p", "requested_image_path": "i", "sample_included": "false"}])
def test_malformed_receipt_never_becomes_successful_empty_sample(receipt):
    result = McpDevToolResult.from_payload(agent_capabilities.sample_plate_image.name, {"structuredContent": receipt})
    response = McpDevToolBatchResponse.from_results(McpDevServerSpec(sys.executable), (result,))
    assert isinstance(result.payloads[0], McpDevPayloadFailure)
    assert result.payloads[0].payload == receipt
    rejection = to_jsonable(response)["results"][0]["payloads"][0]
    assert rejection["payload"] == receipt
    assert rejection["errors"] == to_jsonable(result.diagnostic_errors())
    text = PlateImageSampleRenderer.render(response)
    assert "mcp_payload_invalid" in text
    assert "Image:" not in text


def test_transport_missing_and_unknown_receipts_keep_original_diagnostics():
    server = McpDevServerSpec(sys.executable)
    missing = McpDevToolBatchResponse.from_results(server, (McpDevToolResult(agent_capabilities.sample_plate_image.name, False, ()),))
    assert "mcp_payload_missing" in PlateImageSampleRenderer.render(missing)
    response = McpDevToolBatchResponse.from_transport_failure(server, McpDevClientPhase.CALL_TOOL, RuntimeError("wire lost"))
    assert "wire lost" in PlateImageSampleRenderer.render(response)
    receipt = {"opaque": {"false": False, "zero": 0, "empty": ""}}
    unknown = McpDevToolResult.from_payload("unregistered-external-tool", {"structuredContent": receipt})
    assert unknown.payloads == (receipt,)
    assert to_jsonable(unknown)["payloads"] == [receipt]


@pytest.mark.parametrize("reverse_order", [False, True])
def test_new_declaration_composes_real_cooperative_sampling_hooks(reverse_order):
    @dataclass(frozen=True, kw_only=True)
    class NewSample(PlateImageSampleResult):
        independent_fact: str = "owned"

    events = []
    class SourceFact(PlateImageSampleRenderer):
        @classmethod
        def render_payload(cls, payload, options):
            events.append("source")
            return super().render_payload(payload, options) + "\n" + payload.independent_fact

    class AuditFact(PlateImageSampleRenderer):
        @classmethod
        def render_payload(cls, payload, options):
            events.append("audit")
            return super().render_payload(payload, options) + "\naudit-once"

    bases = (AuditFact, SourceFact) if reverse_order else (SourceFact, AuditFact)
    NewRenderer = type("NewSampleRenderer", bases, {"output_contract": NewSample})
    class NewCapability(SamplePlateImageCapability):
        name = f"openhcs_s1_new_sample_{int(reverse_order)}"
        cli_command = f"s1-new-sample-{int(reverse_order)}"
        output_contract = NewSample

    value = NewSample(schema_version=SCHEMA_VERSION, plate_path="new-plate", requested_image_path="new-image")
    response = batch(value, NewCapability)
    assert type(response.results[0].first_decoded_payload()) is NewSample
    command = CapabilityBackedCommandSpec.for_capability_name(NewCapability.name)
    text = command.render_call_result(response)
    assert events == (["audit", "source"] if reverse_order else ["source", "audit"])
    assert text.count("owned") == text.count("audit-once") == text.count("Image:") == 1
    assert NewRenderer.__mro__.count(PlateImageSampleRenderer) == 1
    assert McpDevOutputRenderer.__registry__[NewSample] is NewRenderer


def test_sampling_renderers_share_the_json_preview_count():
    assert "_json_value_count" not in vars(PlateImageSampleRenderer)
    assert "_json_value_count" not in vars(ViewerImageSampleRenderer)
    assert PlateImageSampleRenderer.json_value_count.__func__ is ViewerImageSampleRenderer.json_value_count.__func__
