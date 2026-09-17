"""Optional OpenHCS MCP declarations supplied by the benchmark package.

Importing this module is the explicit extension-loading boundary. The
declarations register through OpenHCS's existing AutoRegisterMeta owner; the
product package never imports this repository-only package.
"""

from __future__ import annotations

from benchmark.contracts.control import (
    BenchmarkRunInspection,
    BenchmarkRunInspectionRequest,
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

    exposition = AgentCapabilityExposition(
        workflow_group=CapabilityWorkflowGroup.BENCHMARKING,
        workflow_stage=CapabilityWorkflowStage.INSPECTION,
        target_context=CapabilityTargetContext.BENCHMARK_RUN,
        visibility=CapabilityVisibility.EXPERT,
    )


class InspectBenchmarkRunCapability(BenchmarkCapability):
    name = "openhcs_inspect_benchmark_run"
    kind = CapabilityKind.TOOL
    title = "Inspect benchmark run"
    description = (
        "Returns the typed recorded rerun invocation and lifecycle status, "
        "append-only observation progress, and discovered structured result "
        "artifacts for one local output directory."
    )
    service = "benchmark_control"
    data_exposure = ("local_benchmark_paths", "benchmark_result_artifacts")
    input_contract = BenchmarkRunInspectionRequest
    output_contract = BenchmarkRunInspection
    request_invocation = AgentDataclassRequestServiceInvocation(
        service=lambda context: BenchmarkControlService(context.path_policy),
        method=lambda service, request: service.inspect_run(request),
    )


__all__ = (
    "BenchmarkCapability",
    "BenchmarkControlService",
    "InspectBenchmarkRunCapability",
)
