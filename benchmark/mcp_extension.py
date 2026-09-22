"""Optional OpenHCS MCP declarations supplied by the benchmark package.

Importing this module is the explicit extension-loading boundary. The
declarations register through OpenHCS's existing AutoRegisterMeta owner; the
product package never imports this repository-only package.
"""

from __future__ import annotations

from benchmark.contracts.control import (
    BenchmarkRunInspection,
    BenchmarkRunInspectionRequest,
    MeasuredPipelineRunInspection,
    MeasuredPipelineRunInspectionRequest,
    MeasuredPipelineRunReport,
)
from benchmark.control_service import BenchmarkControlService
from openhcs.agent.capabilities import (
    AgentCapabilityDeclaration,
    AgentCapabilityExposition,
    AgentDataclassRequestServiceInvocation,
    CapabilityKind,
    CapabilityTargetContext,
    CapabilityVisibility,
    CapabilityWorkflowGroup,
    CapabilityWorkflowStage,
)


class BenchmarkCapability(AgentCapabilityDeclaration):
    """Expert capability for benchmark control and inspection."""

    service = "benchmark_control"
    data_exposure = ("local_benchmark_paths", "benchmark_result_artifacts")
    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.BENCHMARKING,
        workflow_stage=CapabilityWorkflowStage.INSPECTION,
        target_context=CapabilityTargetContext.BENCHMARK_RUN,
        visibility=CapabilityVisibility.EXPERT,
    )


class MeasuredPipelineCapability(BenchmarkCapability):
    """Shared request boundary for one completed ordinary-pipeline run."""

    input_contract = MeasuredPipelineRunInspectionRequest


class InspectBenchmarkRunCapability(BenchmarkCapability):
    name = "openhcs_inspect_benchmark_run"
    kind = CapabilityKind.TOOL
    title = "Inspect benchmark run"
    description = (
        "Returns the typed recorded rerun invocation and lifecycle status, "
        "append-only observation progress, and discovered structured result "
        "artifacts for one local output directory."
    )
    input_contract = BenchmarkRunInspectionRequest
    output_contract = BenchmarkRunInspection
    request_invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: BenchmarkControlService(context.path_policy),
        method=lambda service, request: service.inspect_run(request),
    )


class InspectMeasuredPipelineRunCapability(MeasuredPipelineCapability):
    name = "openhcs_inspect_measured_pipeline_run"
    kind = CapabilityKind.TOOL
    title = "Inspect measured pipeline run"
    description = (
        "Inspect a completed ordinary OpenHCS pipeline measurement from its typed "
        "receipt and bounded source/output evidence. This does not submit or poll "
        "an execution job; use the normal headless execution tools for that."
    )
    output_contract = MeasuredPipelineRunInspection
    request_invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: BenchmarkControlService(context.path_policy),
        method=lambda service, request: service.inspect_measured_run(request),
    )


class ReportMeasuredPipelineRunCapability(MeasuredPipelineCapability):
    name = "openhcs_report_measured_pipeline_run"
    kind = CapabilityKind.TOOL
    title = "Report measured pipeline run"
    description = (
        "Render a concise report from the same bounded completed-run receipt "
        "inspection; evidence warnings are retained in the result."
    )
    output_contract = MeasuredPipelineRunReport
    request_invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: BenchmarkControlService(context.path_policy),
        method=lambda service, request: service.report_measured_run(request),
    )


__all__ = (
    "BenchmarkCapability",
    "MeasuredPipelineCapability",
    "BenchmarkControlService",
    "InspectBenchmarkRunCapability",
    "InspectMeasuredPipelineRunCapability",
    "ReportMeasuredPipelineRunCapability",
)
