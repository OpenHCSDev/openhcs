"""Public declaration/descent/presentation behavior; never launch a viewer."""

from dataclasses import dataclass
import ast
import inspect
import json
from pathlib import Path

import pytest

from openhcs.agent.capabilities import (
    GetViewerWindowStateCapability,
    ProbeViewerWindowCapability,
    ValidateViewerWindowStateCapability,
)
from openhcs.agent.dto.common import AgentError, AgentWarning, SCHEMA_VERSION
from openhcs.agent.dto.execution import ExecutionConnectionSpec
from openhcs.agent.dto.viewer import (
    ViewerWindowDescriptor,
    ViewerWindowLayerValidationSummary,
    ViewerWindowLayerState,
    ViewerWindowProbeResult,
    ViewerWindowValidationPolicy,
    ViewerWindowValidationSummaryResult,
    ViewerWindowStateResult,
)
from openhcs.runtime.viewer_controls import ViewerNativeDimensions
from zmqruntime.viewer_protocol import (
    ViewerNativeImageIntensityPresentation,
    ViewerNativeLayerTransform,
    ViewerNativeViewportPresentation,
)
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.mcp.dev_client import McpDevCommandSpec, _build_parser
from openhcs.mcp.dev_client_core import (
    McpDevServerIdentity, McpDevToolBatchResponse, McpDevToolResult,
)
from openhcs.mcp.dev_client_renderers.viewer import ViewerProbeRenderer, ViewerStateRenderer
from openhcs.mcp.dev_client_rendering import McpDevOutputRenderer
from openhcs.mcp.dev_client_rendering import McpDevTypedOutputRenderer
from openhcs.serialization.json import to_jsonable


def response(capability, value):
    return to_jsonable(McpDevToolBatchResponse(
        server=McpDevServerIdentity(command="readonly-source", module="openhcs.mcp"),
        results=(McpDevToolResult(capability.name, False, (value,)),),
    ))


def probe(**values):
    return ViewerWindowProbeResult(
        schema_version=SCHEMA_VERSION,
        connection=ExecutionConnectionSpec(port=5992),
        reachable=False,
        viewer=ViewerWindowDescriptor(ViewerType.NAPARI, ""),
        **values,
    )


def test_public_probe_command_preserves_false_zero_empty_and_decoded_identity():
    raw = response(ProbeViewerWindowCapability, probe())
    decoded = McpDevToolBatchResponse.for_rendering(raw)
    payload = decoded.payload_for(ProbeViewerWindowCapability.to_spec())
    assert type(payload) is ViewerWindowProbeResult
    assert type(payload.viewer) is ViewerWindowDescriptor
    assert payload.viewer.viewer_type is ViewerType.NAPARI
    assert McpDevToolBatchResponse.for_rendering(decoded).payload_for(
        ProbeViewerWindowCapability.to_spec()
    ) is payload
    args = _build_parser().parse_args(("probe-viewer", "5992"))
    rendered = McpDevCommandSpec.for_name("probe-viewer").render_response(decoded, args)
    assert 'reachable=False observed=False type=napari title=""' in rendered
    assert "port=5992 layers=0 component_groups=0 component_items=0" in rendered


def test_validation_descends_inherited_counters_policy_and_layer_records():
    original = ViewerWindowValidationSummaryResult(
        schema_version=SCHEMA_VERSION,
        connection=ExecutionConnectionSpec(port=5992),
        valid=False,
        observed=True,
        validation_policy=ViewerWindowValidationPolicy(
            expected_layer_count=0, require_nonzero_payloads=False,
            required_component_labels=("channel",),
        ),
        layer_summaries=(ViewerWindowLayerValidationSummary(
            route_key="native::A01", title="", mounted=False, item_count=0,
            axis_labels=("Y", "X"), component_labels=("channel",),
        ),),
        warnings=(AgentWarning(code="review", message="retain", hint="inspect"),),
    )
    decoded = McpDevToolBatchResponse.for_rendering(
        response(ValidateViewerWindowStateCapability, original)
    )
    value = decoded.payload_for(ValidateViewerWindowStateCapability.to_spec())
    assert type(value.layer_summaries[0]) is ViewerWindowLayerValidationSummary
    assert value.validation_policy.require_nonzero_payloads is False
    args = _build_parser().parse_args(("validate-viewer", "5992"))
    rendered = McpDevCommandSpec.for_name("validate-viewer").render_response(decoded, args)
    assert "valid=False observed=True layers=0 mounted=0 pending=0" in rendered
    assert "expected_layers=0 required_axes=<none> required_components=channel require_nonzero=False" in rendered
    assert 'native::A01: valid=False mounted=False items=0 axes=Y,X' in rendered
    assert 'Warnings:\n- review: retain hint="inspect"' in rendered


@pytest.mark.parametrize("value", (1, "false"))
def test_invalid_boolean_contract_remains_a_failure_with_original_raw_receipt(value):
    raw = response(ProbeViewerWindowCapability, probe())
    original = raw["results"][0]["payloads"][0]
    original["reachable"] = value
    decoded = McpDevToolBatchResponse.for_rendering(raw)
    assert decoded.payload_for(ProbeViewerWindowCapability.to_spec()) is None
    assert decoded.results[0].payloads[0].receipt is original
    rendered = ViewerProbeRenderer.render(decoded)
    assert rendered.startswith("Viewer probe: unavailable\n")
    assert "mcp_payload_invalid" in rendered


def test_agent_error_missing_and_malformed_result_are_distinct():
    original = probe(errors=(AgentError(code="native_failed", message="exact cause"),))
    rendered = ViewerProbeRenderer.render(response(ProbeViewerWindowCapability, original))
    assert "native_failed: exact cause" in rendered
    assert "reachable=False" in rendered
    empty = response(ProbeViewerWindowCapability, original)
    empty["results"][0]["payloads"] = []
    assert "mcp_payload_missing" in ViewerProbeRenderer.render(empty)
    bad = response(ProbeViewerWindowCapability, original)
    bad["results"][0]["payloads"] = [{}]
    assert "mcp_payload_invalid" in ViewerProbeRenderer.render(bad)


def state(**values):
    return ViewerWindowStateResult(
        schema_version=SCHEMA_VERSION, observed=True,
        connection=ExecutionConnectionSpec(port=5992), **values,
    )


def render_state(raw):
    decoded = McpDevToolBatchResponse.for_rendering(raw)
    value = decoded.payload_for(GetViewerWindowStateCapability.to_spec())
    assert value is not None
    binding = McpDevOutputRenderer.for_output_contract(type(value))
    assert binding.renderer_type is ViewerStateRenderer
    return value, binding.render_result(decoded, binding.renderer_type.render_options_type())


def test_original_installed_state_reports_native_facts_without_mutating_receipt():
    fixture = Path(__file__).resolve().parents[3] / (
        "docs/validation/s1_typed_viewer_20261001/post406-installed-state.json"
    )
    raw = json.loads(fixture.read_text())
    before = json.dumps(raw, sort_keys=True)
    value, rendered = render_state(raw)
    assert type(value.native_viewport) is ViewerNativeViewportPresentation
    assert type(value.native_dimensions) is ViewerNativeDimensions
    assert value.native_viewport.center == (0.0, 264.342, 1043.812)
    assert value.native_viewport.zoom == 5
    assert value.native_dimensions.canvas_size == (962, 442)
    assert value.native_dimensions.displayed_axes == ("y", "x")
    assert value.native_dimensions.ndisplay == 2
    visible = tuple(layer for layer in value.layers if layer.visible)
    assert len(visible) == 1
    route = visible[0]
    assert type(route.native_intensity) is ViewerNativeImageIntensityPresentation
    assert route.native_intensity.contrast_limits == (141, 450)
    assert route.native_intensity.gamma == 1
    # The saved wire receipt names this route selected_images, not calcein.
    # Biological channel names are not reconstructed by presentation.
    assert route.title == "selected_images"
    for fact in ("264.342", "1043.812", "zoom=5", "width=962", "height=442",
                 "displayed_axes=y,x", "ndisplay=2"):
        assert fact in rendered
    route_report = rendered.split(route.route_key + ":", 1)[1].split("\n- ", 1)[0]
    assert "141.0" in route_report and "450.0" in route_report
    assert "gamma=1.0" in route_report
    assert "visible=True" in route_report
    assert "scale=" in route_report and "1.3556" in route_report
    assert json.dumps(raw, sort_keys=True) == before
    assert to_jsonable(value) == raw["results"][0]["payloads"][0]
    args = _build_parser().parse_args(("viewer-state", "5992"))
    assert McpDevCommandSpec.for_name("viewer-state").render_response(raw, args) == rendered


def test_native_sections_distinguish_absence_from_supplied_zero_and_empty_facts():
    absent, rendered = render_state(response(GetViewerWindowStateCapability, state()))
    assert absent.native_viewport is None and absent.native_dimensions is None
    assert "Native viewport:" not in rendered
    assert "Native dimensions:" not in rendered
    assert "Native canvas:" not in rendered
    original = state(
        native_viewport=ViewerNativeViewportPresentation(center=(0, 0, 0), zoom=1),
        native_dimensions=ViewerNativeDimensions(
            order=(0, 1), ndisplay=2, displayed_axes=("y", "x"),
            point=(0, 0), camera_angles=(0, 0, 0), canvas_size=(0, 0),
        ),
        layers=(ViewerWindowLayerState(
            route_key="exact::route", title="", mounted=False, item_count=0,
            visible=False, selected=False,
            native_intensity=ViewerNativeImageIntensityPresentation((0, 1), 1),
            native_transform=ViewerNativeLayerTransform(scale=(1.3556, 1.3556), translate=(0, 0)),
            component_values=({"channel": 0, "note": ""},),
            payload_summaries=tuple({"shape": [1, 2], "min": index} for index in range(4)),
            payload_summary_count=4,
        ),),
    )
    _, rendered = render_state(response(GetViewerWindowStateCapability, original))
    assert "center=[0.0, 0.0, 0.0]" in rendered
    assert "width=0 height=0" in rendered
    assert "contrast_limits=[0.0, 1.0]" in rendered
    assert "translate=[0.0, 0.0]" in rendered
    assert 'title="" visible=False selected=False items=0' in rendered
    assert "channel=0" in rendered
    assert rendered.count("  payload summary:") == 3
    assert '"min": 3' not in rendered
    assert "payload summaries: 4" in rendered


@pytest.mark.parametrize("member,bad", (("native_viewport", {"center": [0, 0], "zoom": 5}),
                                       ("native_intensity", {"contrast_limits": [450, 141], "gamma": 1})))
def test_malformed_native_declarations_remain_errors_not_absent_sections(member, bad):
    raw = response(GetViewerWindowStateCapability, state(layers=(ViewerWindowLayerState(
        route_key="bad", title="bad", mounted=True, item_count=1,
    ),)))
    original = raw["results"][0]["payloads"][0]
    if member == "native_intensity":
        original["layers"][0][member] = bad
    else:
        original[member] = bad
    decoded = McpDevToolBatchResponse.for_rendering(raw)
    assert decoded.payload_for(GetViewerWindowStateCapability.to_spec()) is None
    assert decoded.results[0].payloads[0].receipt is original
    rendered = ViewerStateRenderer.render(decoded)
    assert "mcp_payload_invalid" in rendered
    assert "Viewer state: failed" in rendered


@dataclass(frozen=True, kw_only=True)
class IndependentProbeResult(ViewerWindowProbeResult):
    observation_note: str = "independent"


class IndependentProbeCapability(ProbeViewerWindowCapability):
    name = "openhcs_s1_independent_probe"
    cli_command = "s1-independent-probe"
    output_contract = IndependentProbeResult


def test_independent_dto_and_capability_inherit_original_renderer_without_roster_edit():
    original = IndependentProbeResult(
        schema_version=SCHEMA_VERSION, reachable=True,
        connection=ExecutionConnectionSpec(port=5992),
    )
    decoded = McpDevToolBatchResponse.for_rendering(
        response(IndependentProbeCapability, original)
    )
    payload = decoded.payload_for(IndependentProbeCapability.to_spec())
    assert type(payload) is IndependentProbeResult
    binding = McpDevOutputRenderer.for_output_contract(type(payload))
    assert binding.renderer_type is ViewerProbeRenderer
    rendered = binding.render_result(decoded, binding.renderer_type.render_options_type())
    assert "reachable=True observed=False type=<none> title=<none>" in rendered


def test_independent_presentation_capabilities_execute_cooperative_hooks():
    calls = []

    class ObservedPresentation:
        @classmethod
        def render_payload(cls, payload, options):
            calls.append("observe")
            return super().render_payload(payload, options)

    class AuditedPresentation:
        @classmethod
        def render_payload(cls, payload, options):
            calls.append("audit")
            return super().render_payload(payload, options)

    @dataclass(frozen=True, kw_only=True)
    class AuditedProbeResult(IndependentProbeResult):
        pass

    class AuditedProbeCapability(IndependentProbeCapability):
        name = "openhcs_s1_audited_probe"
        cli_command = "s1-audited-probe"
        output_contract = AuditedProbeResult

    class AuditedProbeRenderer(ObservedPresentation, AuditedPresentation, ViewerProbeRenderer):
        output_contract = AuditedProbeResult

    original = AuditedProbeResult(
        schema_version=SCHEMA_VERSION, reachable=True,
        connection=ExecutionConnectionSpec(port=5992),
        warnings=(AgentWarning(code="notice", message="shown"),),
    )
    rendered = AuditedProbeRenderer.render(response(AuditedProbeCapability, original))
    assert calls == ["observe", "audit"]
    assert "reachable=True" in rendered
    assert "Warnings:\n- notice: shown" in rendered


def test_typed_viewer_declarations_do_not_reintroduce_known_raw_record_readers():
    for declaration in McpDevOutputRenderer.declaration_types():
        if (declaration.__module__ != ViewerProbeRenderer.__module__
                or not issubclass(declaration, McpDevTypedOutputRenderer)):
            continue
        source = ast.parse(inspect.getsource(declaration))
        for node in ast.walk(source):
            if isinstance(node, ast.Call):
                assert not (
                    isinstance(node.func, ast.Attribute)
                    and node.func.attr == "get"
                    and node.args
                    and isinstance(node.args[0], ast.Constant)
                ), (declaration, node.lineno)
