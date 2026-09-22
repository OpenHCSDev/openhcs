"""Agent-facing benchmark control service owned by the benchmark extension."""

from __future__ import annotations

from benchmark.contracts.control import (
    BenchmarkRunInspection,
    BenchmarkRunInspectionRequest,
    MeasuredPipelineRunInspection,
    MeasuredPipelineRunInspectionRequest,
    MeasuredPipelineRunReport,
)
from benchmark.control import (
    inspect_benchmark_run,
    inspect_measured_pipeline_run,
    report_measured_pipeline_run,
)
from openhcs.agent.path_policy import AgentPathPolicy


class BenchmarkControlService:
    """Apply agent path policy before projecting benchmark run state."""

    def __init__(self, path_policy: AgentPathPolicy) -> None:
        self._path_policy = path_policy

    def inspect_run(
        self,
        request: BenchmarkRunInspectionRequest,
    ) -> BenchmarkRunInspection:
        output_dir = self._path_policy.assert_readable(request.output_dir)
        if not output_dir.is_dir():
            raise ValueError(f"Benchmark output path must be a directory: {output_dir}")
        return inspect_benchmark_run(output_dir)

    def inspect_measured_run(
        self,
        request: MeasuredPipelineRunInspectionRequest,
    ) -> MeasuredPipelineRunInspection:
        output_dir = self._path_policy.assert_readable(request.output_dir)
        return inspect_measured_pipeline_run(output_dir)

    def report_measured_run(
        self,
        request: MeasuredPipelineRunInspectionRequest,
    ) -> MeasuredPipelineRunReport:
        return report_measured_pipeline_run(self.inspect_measured_run(request))
