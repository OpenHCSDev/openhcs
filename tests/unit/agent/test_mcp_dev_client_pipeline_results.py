"""Production command journeys with controlled wire receipts, never a runtime."""

from __future__ import annotations

import ast
import asyncio
import json
import sys
from dataclasses import dataclass, replace
from pathlib import Path

import pytest
from zmqruntime.execution import ExecutionProgressObservation

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import (
    SCHEMA_VERSION,
    AgentError,
    AgentWarning,
    RenderedSource,
)
from openhcs.agent.dto.execution import (
    ArtifactInputPlanSummary,
    ArtifactMaterializationPathSummary,
    ArtifactMaterializationPlanSummary,
    ArtifactPlanInspection,
    ArtifactPlanSummary,
    CompiledStepPlanSummary,
    ExecutionJobRef,
    ExecutionJobStatus,
    MainFlowMaterializationPlanSummary,
    OrchestratorSessionRef,
    SourceWorkspaceFileRecord,
    SourceWorkspaceSummary,
    ViewerStreamingPlanSummary,
)
from openhcs.agent.dto.pipeline import (
    FunctionSpecRef,
    FunctionStepSpec,
    PipelineRef,
    PipelineSpec,
    PipelineValidationResult,
)
from openhcs.core.streaming_config_declarations import ViewerType
from openhcs.mcp import dev_client
from openhcs.mcp.dev_client_commanding import CapabilityBackedCommandSpec
from openhcs.mcp.dev_client_core import (
    McpDevPayloadFailure,
    McpDevServerSpec,
    McpDevToolBatchResponse,
    McpDevToolResult,
)
from openhcs.mcp.dev_client_rendering import (
    McpDevOutputRenderer,
    McpDevTypedOutputRenderer,
)
from openhcs.mcp.dev_client_renderers.pipeline import PipelineArtifactPlanRenderer
from openhcs.serialization.json import to_jsonable


class ControlledWireSession:
    """Only replace the wire peer; retain real framing, commands and rendering."""

    def __init__(self, receipts, *, structured=True):
        self.server_spec = McpDevServerSpec(sys.executable)
        self.receipts = iter(receipts)
        self.calls = []
        self.structured = structured

    async def call_tool(self, name, arguments, *, timeout_seconds):
        self.calls.append((name, arguments, timeout_seconds))
        receipt = to_jsonable(next(self.receipts))
        if self.structured:
            return {"isError": False, "structuredContent": receipt, "content": []}
        return {
            "isError": False,
            "content": [{"type": "text", "text": json.dumps(receipt)}],
        }


def batch(capability, value):
    wire = {"isError": False, "structuredContent": to_jsonable(value), "content": []}
    return McpDevToolBatchResponse.from_results(
        McpDevServerSpec(sys.executable),
        (McpDevToolResult.from_payload(capability.name, wire),),
    )


@pytest.mark.parametrize("registered_count, code", (
    (0, "custom_function_registration_uncertain"),
    (1, "custom_function_local_projection_failed"),
))
def test_registration_renderer_retains_typed_error_receipt_and_handle(registered_count, code):
    from openhcs.agent.dto.execution_connection import ExecutionConnectionSpec
    from openhcs.agent.dto.functions import CustomFunctionRegistrationHandle, CustomFunctionRegistrationResult
    from openhcs.mcp.dev_client_renderers.knowledge import CustomFunctionRegistrationRenderer
    from zmqruntime.messages import ProcessIdentity

    handle = CustomFunctionRegistrationHandle(
        ExecutionConnectionSpec(port=15993), ProcessIdentity.current(),
        "a" * 64, "engineering_registration", False, None,
    )
    original = CustomFunctionRegistrationResult(
        schema_version=SCHEMA_VERSION, registered_count=registered_count,
        connection=handle.connection, server_identity=handle.server_identity,
        observation_handle=handle,
        errors=(AgentError(code=code, message="original cause", hint="Do not replay.", exception_type="ValueError"),),
    )
    response = batch(agent_capabilities.register_custom_function, original)
    decoded = McpDevToolBatchResponse.for_rendering(to_jsonable(response))
    assert decoded.payload_for(agent_capabilities.register_custom_function) == original
    text = CustomFunctionRegistrationRenderer.render(to_jsonable(response))
    assert "incomplete observation or projection" in text
    assert f"registered_count: {registered_count}" in text
    assert "zero/absent does not prove no mutation" in text
    assert text.count(f"{code}: original cause") == 1
    assert "Do not replay." in text
    marker = "Read-only observation handle: "
    rendered_handle = next(line.removeprefix(marker) for line in text.splitlines() if line.startswith(marker))
    assert json.loads(rendered_handle) == to_jsonable(handle)


def test_registration_renderer_uses_declared_success_entries_without_mapping_reads():
    from openhcs.agent.dto.functions import CustomFunctionRegistrationResult, FunctionCatalogEntry
    from openhcs.mcp.dev_client_renderers.knowledge import CustomFunctionRegistrationRenderer

    entry = FunctionCatalogEntry(
        function_id="openhcs:engineering_registration", import_path="openhcs.processing.custom_functions.engineering_registration",
        name="engineering_registration", module="openhcs.processing.custom_functions", library="openhcs",
        signature="engineering_registration(image)", summary="Original declared summary", backend_tags=("numpy",),
    )
    original = CustomFunctionRegistrationResult(
        schema_version=SCHEMA_VERSION, registered_count=1, persisted=False,
        storage_dir="/engineering", source_file_paths=("/engineering/original.py",), functions=(entry,),
    )
    text = CustomFunctionRegistrationRenderer.render(to_jsonable(batch(agent_capabilities.register_custom_function, original)))
    assert "registered=1 persisted=False storage=/engineering" in text
    assert "Files: /engineering/original.py" in text
    assert f"{entry.function_id}: {entry.signature} tags=numpy" in text
    assert entry.summary in text and "Lifetime: process-local only" in text
    assert f"draft-pipeline-step {entry.function_id}" in text


def args_for(*argv):
    return dev_client._build_parser().parse_args(argv)


def plan_fixture():
    checkpoint = ArtifactMaterializationPlanSummary(
        persistent_enabled=True,
        persistent_backend="disk",
        paths=tuple(
            ArtifactMaterializationPathSummary(
                str(index), f"image-{index}", (f"result-{index}.tif",)
            )
            for index in range(4)
        ),
        filename_uses_source_identity=True,
        note="receipt retained",
    )
    workspace = SourceWorkspaceSummary(
        file_count=7,
        files=tuple(
            SourceWorkspaceFileRecord(
                f"virtual-{index}",
                f"/full/virtual-{index}",
                f"physical-{index}",
                {"new_component": {"identity": index}},
            )
            for index in range(7)
        ),
        axis_file_counts={"A": 7},
    )
    step = CompiledStepPlanSummary(
        1,
        "Owned step",
        "A",
        "result-dir",
        execution_groups=("g",),
        main_flow_axis_persistence_enabled=True,
        main_flow_materialization=MainFlowMaterializationPlanSummary(
            "result-dir", "disk", "plate-root", "sub-dir"
        ),
        viewer_streaming=(
            ViewerStreamingPlanSummary(
                "napari", ViewerType.NAPARI, "memory", {"new_option": [1, 2]}
            ),
        ),
        artifact_inputs=(
            ArtifactInputPlanSummary(
                "input",
                "image",
                "input-path",
                ("g",),
                source_step_id=2,
                source_step_scope_id="scope-2",
            ),
        ),
        artifact_outputs=(
            ArtifactPlanSummary(
                "output", "image", "output-path", ("g",), materialization=checkpoint
            ),
        ),
    )
    return ArtifactPlanInspection(
        schema_version=SCHEMA_VERSION,
        plate_path="source-only-plate",
        axis_count=1,
        axes=("A",),
        step_count=1,
        steps=(step,),
        worker_assignments={"worker": ["A"]},
        source_workspace=workspace,
        progress_event_count=3,
    )


@pytest.mark.parametrize("structured", [True, False])
def test_draft_journey_decodes_once_then_renders_real_command(structured, monkeypatch):
    ref = PipelineRef("pipeline-1", "openhcs://pipelines/pipeline-1")
    spec = PipelineSpec(
        SCHEMA_VERSION,
        "pipeline-1",
        "config-1",
        (
            FunctionStepSpec(
                "step-1",
                "Count cells",
                (FunctionSpecRef("function-1", {"extension": [1, 2]}),),
            ),
        ),
    )
    validation = PipelineValidationResult(
        schema_version=SCHEMA_VERSION,
        valid=False,
        pipeline_ref=ref,
        errors=(
            AgentError(
                "missing_function_kwargs",
                "Missing required agent kwargs: threshold.",
                "required agent kwargs: threshold.",
            ),
        ),
        warnings=(AgentWarning("note", "Pipeline is small."),),
    )
    source = RenderedSource(
        SCHEMA_VERSION, "Pipeline", "pipeline_steps = [FunctionStep(...)]\n"
    )
    peer = ControlledWireSession((ref, spec, validation, source), structured=structured)
    args = args_for("draft-pipeline-step", "function-1", "--max-source-chars", "10")
    command = dev_client.McpDevCommandSpec.for_name(args.command)
    import openhcs.mcp.dev_client_core as ingress

    decoded_contracts = []
    decode = ingress.dataclass_from_mapping

    def observed_decode(contract, payload):
        decoded_contracts.append(contract)
        return decode(contract, payload)

    monkeypatch.setattr(ingress, "dataclass_from_mapping", observed_decode)
    response = asyncio.run(command.run_session(peer, args))
    assert [call[0] for call in peer.calls] == [
        agent_capabilities.create_pipeline.name,
        agent_capabilities.add_function_step.name,
        agent_capabilities.validate_pipeline.name,
        agent_capabilities.render_pipeline_source.name,
    ]
    assert peer.calls[1][1]["pipeline_id"] == ref.pipeline_id
    assert isinstance(response.results[1].payloads[0], PipelineSpec)
    assert response.results[1].payloads[0].steps[0].functions[0].kwargs == {
        "extension": [1, 2]
    }
    before = to_jsonable(response)
    render = command.render_result(response, args)
    assert "id=pipeline-1 valid=False steps=1" in render
    assert "functions=function-1" in render
    assert "missing_function_kwargs" in render and "threshold" in render
    assert "note: Pipeline is small." in render
    assert "Next: function function-1" in render and "Retry shape:" in render
    assert "truncated" in render
    assert to_jsonable(response) == before
    assert decoded_contracts == [
        PipelineRef,
        PipelineSpec,
        PipelineValidationResult,
        RenderedSource,
    ]
    assert command.render_result(
        response, replace_namespace(args, json=True)
    ) == json.dumps(before, indent=2, sort_keys=True)


def replace_namespace(args, **values):
    import argparse

    return argparse.Namespace(**(vars(args) | values))


def test_nested_artifact_contract_and_receipt_survive_compact_limits():
    original = plan_fixture()
    response = batch(agent_capabilities.inspect_pipeline_source_artifact_plan, original)
    decoded = response.results[0].payloads[0]
    assert isinstance(decoded, ArtifactPlanInspection)
    assert isinstance(decoded.source_workspace.files[6], SourceWorkspaceFileRecord)
    assert decoded.steps[0].viewer_streaming[0].viewer_type is ViewerType.NAPARI
    assert decoded.steps[0].artifact_outputs[0].materialization.paths[
        3
    ].candidate_paths == ("result-3.tif",)
    assert to_jsonable(decoded) == to_jsonable(original)
    args = args_for(
        "artifact-plan", "source-only-plate", "--source-text", "pipeline_steps = []"
    )
    rendered = dev_client.McpDevCommandSpec.for_name(args.command).render_result(
        response, args
    )
    for fact in (
        "source-only-plate",
        "axes=1",
        "progress_events=3",
        "new_component",
        "source_scope=scope-2",
        "backend=disk",
        "sub_dir=sub-dir",
        "viewer=napari",
        "result-2.tif",
        "truncated=1",
        "receipt retained",
    ):
        assert fact in rendered
    assert "physical-6" not in rendered
    assert len(decoded.source_workspace.files) == 7
    assert len(decoded.steps[0].artifact_outputs[0].materialization.paths) == 4
    assert to_jsonable(decoded) == to_jsonable(original)


@pytest.mark.parametrize("waited", [True, False])
def test_execute_journey_preserves_native_variants_progress_and_errors(waited):
    session = OrchestratorSessionRef(
        session_id="session-1",
        schema_version=SCHEMA_VERSION,
        uri="openhcs://sessions/1",
    )
    identity = dict(
        schema_version=SCHEMA_VERSION,
        job_id="job-1",
        session_id="session-1",
        kind="execute",
        status="failed" if waited else "queued",
        uri="openhcs://jobs/1",
        server_execution_id="execution-1",
    )
    job = (
        ExecutionJobStatus(
            **identity,
            response={"native_extension": {"retain": [1, 2]}, "status": "failed"},
            progress=ExecutionProgressObservation(
                3, {"phase": "processing", "extension": {"done": 2}}
            ),
            errors=(
                AgentError("execution_failed", "Failure retained", "Inspect receipt"),
            ),
            warnings=(AgentWarning("wait", "Deadline reached"),),
        )
        if waited
        else ExecutionJobRef(**identity)
    )
    peer = ControlledWireSession((session, job))
    args = args_for(
        "execute-source",
        "source-only-plate",
        "--source-text",
        "pipeline_steps = []",
        "--wait" if waited else "--no-wait",
    )
    command = dev_client.McpDevCommandSpec.for_name(args.command)
    response = asyncio.run(command.run_session(peer, args))
    decoded = response.results[1].payloads[0]
    assert type(decoded) is type(job)
    assert to_jsonable(decoded) == to_jsonable(job)
    assert peer.calls[1][1]["session_id"] == "session-1"
    rendered = command.render_result(response, args)
    assert (
        "id=session-1" in rendered
        and "id=job-1" in rendered
        and "server_execution=execution-1" in rendered
    )
    if waited:
        assert decoded.progress.sequence == 3
        assert decoded.progress.event["extension"]["done"] == 2
        for fact in (
            "native_extension",
            "processing",
            "Failure retained",
            "Inspect receipt",
            "Deadline reached",
        ):
            assert fact in rendered
        assert response.has_errors()
    else:
        assert not response.has_errors()


@pytest.mark.parametrize(
    "broken",
    [
        {"schema_version": SCHEMA_VERSION, "plate_path": "source-only", "steps": [42]},
        {
            "schema_version": SCHEMA_VERSION,
            "plate_path": "source-only",
            "axis_count": True,
        },
        {
            "schema_version": SCHEMA_VERSION,
            "plate_path": "source-only",
            "source_workspace": {"files": [{"virtual_path": "v"}]},
        },
        {
            "schema_version": SCHEMA_VERSION,
            "plate_path": "source-only",
            "undeclared": "not metadata",
        },
        {
            "schema_version": SCHEMA_VERSION,
            "ok": False,
            "errors": [
                {
                    "code": "server_stale",
                    "message": "Reconnect first",
                    "hint": "No retry",
                }
            ],
            "restart_required": True,
        },
    ],
)
def test_malformed_contract_is_explicit_and_keeps_entire_receipt(broken):
    response = batch(agent_capabilities.inspect_pipeline_source_artifact_plan, broken)
    failed = response.results[0].payloads[0]
    assert isinstance(failed, McpDevPayloadFailure)
    assert failed.receipt == broken
    assert to_jsonable(failed) == broken
    assert response.has_errors()
    rendered = PipelineArtifactPlanRenderer.render(response)
    assert "mcp_payload_invalid" in rendered and "unavailable" in rendered
    if "errors" in broken:
        assert "Reconnect first" in rendered and "No retry" in rendered


def test_not_run_missing_transport_and_mcp_errors_are_distinct():
    args = args_for("draft-pipeline-step", "function-1")
    command = dev_client.McpDevCommandSpec.for_name(args.command)
    empty = McpDevToolBatchResponse.from_results(McpDevServerSpec(sys.executable), ())
    assert "valid=<not-run>" in command.render_result(empty, args)
    missing = replace(
        empty,
        results=(
            McpDevToolResult(agent_capabilities.validate_pipeline.name, False, ()),
        ),
    )
    assert "mcp_payload_missing" in command.render_result(missing, args)
    tool_error = replace(
        empty,
        results=(
            McpDevToolResult(agent_capabilities.validate_pipeline.name, True, ()),
        ),
    )
    assert "mcp_tool_error" in command.render_result(tool_error, args)
    failure = command.transport_failure_response(
        McpDevServerSpec(sys.executable),
        command.execution_phase,
        RuntimeError("connection lost"),
        server_stderr_tail="full retained stderr",
    )
    rendered = command.render_result(failure, args)
    assert "connection lost" in rendered and "mcp_transport_failed" in rendered
    assert failure.errors[0].server_stderr_tail == "full retained stderr"


def test_single_declaration_extension_uses_output_mro_without_consumer_edits():
    from openhcs.agent.capabilities import InspectPipelineSourceArtifactPlanCapability

    @dataclass(frozen=True, slots=True, kw_only=True)
    class ExtendedInspection(ArtifactPlanInspection):
        extension_fact: str = "retained"

    binding = McpDevOutputRenderer.for_output_contract(ExtendedInspection)
    assert binding.renderer_type is PipelineArtifactPlanRenderer
    value = McpDevToolResult._decode_payload(
        to_jsonable(
            ExtendedInspection(schema_version=SCHEMA_VERSION, plate_path="extended")
        ), (ExtendedInspection,)
    )
    assert type(value) is ExtendedInspection and value.extension_fact == "retained"
    assert "plate=extended" in binding.renderer_type.render_payload_value(
        value, binding.renderer_type.render_options_type()
    )

    # One capability declaration selects the new output at real wire ingress;
    # presentation inherits the existing owner, without adding a roster entry.
    class ExtensionCapability(InspectPipelineSourceArtifactPlanCapability):
        name = "openhcs_s1_extension_inspection"
        cli_command = "s1-extension-inspection"
        output_contract = ExtendedInspection

    response = batch(ExtensionCapability.to_spec(), value)
    assert type(response.results[0].first_decoded_payload()) is ExtendedInspection
    assert "plate=extended" in PipelineArtifactPlanRenderer.render(response)
    command = CapabilityBackedCommandSpec.for_capability_name(ExtensionCapability.name)
    assert "plate=extended" in command.render_result(
        response, command.call_render_args({})
    )


@pytest.mark.parametrize("value", [None, False, 0, ""])
def test_shared_optional_presentation_preserves_native_absence(value):
    from openhcs.mcp.dev_client_rendering import McpDevTypedOutputRenderer

    observed = []

    def present(fact):
        observed.append(fact)
        return (str(fact),)

    lines = McpDevTypedOutputRenderer.optional_lines(value, present)
    assert lines == (() if value is None else (str(value),))
    assert observed == ([] if value is None else [value])


@pytest.mark.parametrize("reverse_order", [False, True])
def test_cooperative_diamond_renderer_identity_is_visited_once(reverse_order):
    from openhcs.agent.capabilities import InspectPipelineSourceArtifactPlanCapability

    @dataclass(frozen=True, slots=True)
    class NewResult:
        value: str

    events = []

    class ValueRenderer(McpDevTypedOutputRenderer):
        @classmethod
        def render_payload(cls, payload: NewResult, options):
            events.append("ancestor")
            return payload.value

    class Left(ValueRenderer):
        @classmethod
        def render_payload(cls, payload, options):
            events.append("left")
            return super().render_payload(payload, options)

    class Right(ValueRenderer):
        @classmethod
        def render_payload(cls, payload, options):
            events.append("right")
            return super().render_payload(payload, options)

    bases = (Right, Left) if reverse_order else (Left, Right)
    Diamond = type("Diamond", bases, {"output_contract": NewResult})

    class DiamondCapability(InspectPipelineSourceArtifactPlanCapability):
        name = f"openhcs_s1_diamond_{int(reverse_order)}"
        cli_command = f"s1-diamond-{int(reverse_order)}"
        output_contract = NewResult

    binding = McpDevOutputRenderer.for_output_contract(NewResult)
    value = McpDevToolResult._decode_payload({"value": "one-declaration"}, (NewResult,))
    assert (
        binding.renderer_type.render_payload_value(
            value, binding.renderer_type.render_options_type()
        )
        == "one-declaration"
    )
    expected = ["right", "left"] if reverse_order else ["left", "right"]
    assert events == [*expected, "ancestor"]
    events.clear()
    response = batch(DiamondCapability.to_spec(), value)
    command = CapabilityBackedCommandSpec.for_capability_name(DiamondCapability.name)
    assert command.render_result(response, command.call_render_args({})) == value.value
    assert events == [*expected, "ancestor"]
    assert Diamond.__mro__.count(ValueRenderer) == 1
    assert tuple(McpDevOutputRenderer.declaration_types()).count(Diamond) == 1
    # Registry views are projections of declaration identity, not a second roster.
    assert McpDevOutputRenderer.__registry__[NewResult] is Diamond


def test_pipeline_guard_forbids_raw_reader_reintroduction():
    import openhcs.mcp.dev_client_renderers.pipeline as pipeline

    tree = ast.parse(Path(pipeline.__file__).read_text())
    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
            assert node.func.attr not in {
                "get",
                "nested_mapping",
                "sequence_of_mappings",
                "first_tool_payload",
                "tool_payload",
            }
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
            assert node.func.id not in {
                "isinstance",
                "getattr",
                "hasattr",
                "optional_int",
                "optional_bool",
            }


def test_submission_declaration_preserves_advertised_external_contract():
    from typing import get_type_hints
    from openhcs.agent.capabilities import require_agent_type_contract
    from openhcs.agent.services.execution_session_service import ExecutionSessionService
    from openhcs.mcp.server import _mcp_tool_meta

    for capability in (
        agent_capabilities.submit_compile,
        agent_capabilities.submit_pipeline_execution,
    ):
        assert (
            capability.output_contract.producer is ExecutionSessionService._submit_job
        )
        assert (
            capability.output_contract.result_type
            == get_type_hints(ExecutionSessionService._submit_job, include_extras=True)[
                "return"
            ]
        )
        assert capability.output_contract_types == (ExecutionJobRef, ExecutionJobStatus)
        assert (
            require_agent_type_contract(capability.output_contract) is ExecutionJobRef
        )
        assert _mcp_tool_meta(capability) == {
            "openhcs/outputContract": "ExecutionJobRef"
        }


def test_typed_diagnostics_do_not_reserialize_or_rescan_error_records(monkeypatch):
    import openhcs.mcp.dev_client_core as core

    error = AgentError("nested_failure", "Retained typed diagnosis", "Retained hint")
    response = batch(
        agent_capabilities.validate_pipeline,
        PipelineValidationResult(
            schema_version=SCHEMA_VERSION,
            valid=False,
            pipeline_ref=PipelineRef("p", "openhcs://pipelines/p"),
            errors=(error,),
        ),
    )

    def forbidden_serialization(value):
        raise AssertionError("Typed diagnostics must not round-trip through JSON")

    monkeypatch.setattr(core, "to_jsonable", forbidden_serialization)
    assert response.has_errors()
    assert response.results[0].agent_error_codes() == ("nested_failure",)
    assert response.diagnostic_errors()[0] == error
    assert "Retained hint" in dev_client.McpDevCommandSpec.for_name(
        "draft-pipeline-step"
    ).render_result(response, args_for("draft-pipeline-step", "function-1"))


@pytest.mark.parametrize("json_output", [False, True])
def test_actual_cli_main_renders_without_runtime(monkeypatch, capsys, json_output):
    response = batch(
        agent_capabilities.inspect_pipeline_source_artifact_plan, plan_fixture()
    )

    async def controlled_entry(args):
        assert args.command == "artifact-plan"
        return response

    monkeypatch.setattr(dev_client, "_run_async", controlled_entry)
    argv = [
        "artifact-plan",
        "source-only-plate",
        "--source-text",
        "pipeline_steps = []",
    ]
    if json_output:
        argv.append("--json")
    assert dev_client.main(argv) == 0
    printed = capsys.readouterr().out
    if json_output:
        assert json.loads(printed) == to_jsonable(response)
    else:
        assert "Owned step" in printed and "new_component" in printed


def test_generic_call_cli_uses_nominal_typed_contract_without_json_roundtrip(
    monkeypatch, capsys
):
    import openhcs.serialization.json as serialization

    response = batch(
        agent_capabilities.inspect_pipeline_source_artifact_plan, plan_fixture()
    )

    async def controlled_entry(args):
        return response

    def forbidden_serialization(value):
        raise AssertionError("Compact migrated call must consume the typed result")

    monkeypatch.setattr(dev_client, "_run_async", controlled_entry)
    monkeypatch.setattr(serialization, "to_jsonable", forbidden_serialization)
    assert (
        dev_client.main(
            ["call", agent_capabilities.inspect_pipeline_source_artifact_plan.name]
        )
        == 0
    )
    assert "Owned step" in capsys.readouterr().out


def test_generic_call_preserves_pending_workflow_native_receipt(monkeypatch, capsys):
    from openhcs.agent.dto.ui_bridge import (
        UiActionIdentity,
        UiActionInvokeResult,
        UiMutationReceipt,
        UiMutationRequestToken,
        UiSelectedPlateWorkflowKind,
        UiSelectedPlateWorkflowResult,
    )

    native = UiSelectedPlateWorkflowResult(
        SCHEMA_VERSION,
        UiSelectedPlateWorkflowKind("run_plate"),
        UiActionInvokeResult(
            SCHEMA_VERSION,
            UiActionIdentity(widget_id="plate_manager", action_id="run_plate"),
            "accepted",
            UiMutationReceipt(UiMutationRequestToken(), accepted=True),
            target_scope_ids=("scope-1",),
        ),
    )
    response = batch(
        agent_capabilities.ui_selected_plate_workflow,
        native,
    )

    async def controlled_entry(args):
        return response

    monkeypatch.setattr(dev_client, "_run_async", controlled_entry)
    assert (
        dev_client.main(
            [
                "call",
                agent_capabilities.ui_selected_plate_workflow.name,
                "--json",
                "--arguments",
                '{"workflow":"run_plate"}',
            ]
        )
        == 0
    )
    rendered = capsys.readouterr().out
    assert "run_plate" in rendered and "accepted" in rendered and "scope-1" in rendered
    assert json.loads(rendered) == to_jsonable(response)


@pytest.mark.parametrize("malformed", [False, True])
def test_persistent_client_execute_uses_real_command_boundary_without_runtime(
    monkeypatch, malformed
):
    from io import StringIO

    receipt = to_jsonable(plan_fixture())
    if malformed:
        receipt["axis_count"] = True
    peer = ControlledWireSession((receipt,))

    def forbidden_raw_failure_scan(value):
        raise AssertionError("Production execute must query typed diagnostics")

    monkeypatch.setattr(dev_client, "_command_failed", forbidden_raw_failure_scan)
    client = dev_client.McpDevClient(server_stderr=StringIO())
    # Only the peer is controlled. No process/session is launched; execute,
    # run_session, framing, decoding, rendering and exit status are production.
    client._session = peer
    client._session_started = True
    try:
        execution = client.execute(
            [
                "artifact-plan",
                "source-only-plate",
                "--source-text",
                "pipeline_steps = []",
            ]
        )
    finally:
        client.close()
    assert execution.returncode == int(malformed)
    assert execution.payload["results"][0]["payloads"][0] == receipt
    assert (
        "mcp_payload_invalid" if malformed else "Owned step"
    ) in execution.rendered_output
    assert len(peer.calls) == 1
