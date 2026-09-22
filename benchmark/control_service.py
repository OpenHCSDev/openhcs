"""Agent-facing benchmark control service owned by the benchmark extension."""

from __future__ import annotations

from benchmark.contracts.control import (
    BenchmarkCaseCatalog,
    BenchmarkCaseDiscoveryRequest,
    BenchmarkRunInspection,
    BenchmarkRunInspectionRequest,
    MeasuredPipelineRunInspection,
    MeasuredPipelineRunInspectionRequest,
    MeasuredPipelineRunReport,
)
from benchmark.control import (
    discover_benchmark_cases,
    inspect_benchmark_run,
    inspect_measured_pipeline_run,
    report_measured_pipeline_run,
)
from openhcs.agent.path_policy import AgentPathPolicy


class BenchmarkControlService:
    """Apply agent path policy before projecting benchmark run state."""

    def __init__(self, path_policy: AgentPathPolicy) -> None:
        self._path_policy = path_policy

    def discover_cases(
        self,
        request: BenchmarkCaseDiscoveryRequest,
    ) -> BenchmarkCaseCatalog:
        manifest = self._path_policy.assert_readable(request.manifest_path)
        catalog = discover_benchmark_cases(
            manifest,
            requested_names=request.case_names,
        )
        for case in catalog.cases:
            self._path_policy.assert_readable_location(case.dataset_path)
            self._path_policy.assert_readable_location(case.cppipe_path)
        return catalog

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
