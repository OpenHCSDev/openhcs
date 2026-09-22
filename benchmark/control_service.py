"""Agent-facing benchmark control service owned by the benchmark extension."""

from __future__ import annotations

from typing import TYPE_CHECKING

from benchmark.contracts.control import (
    BenchmarkCaseCatalog,
    BenchmarkCaseDiscoveryRequest,
    BenchmarkRunInspection,
    BenchmarkRunInspectionRequest,
    MeasuredPipelineRunFinalizationRequest,
    MeasuredPipelineRunInspection,
    MeasuredPipelineRunInspectionRequest,
    MeasuredPipelineRunReport,
)
from benchmark.contracts.measured_run_receipt import MeasuredPipelineRunReceipt
from benchmark.control import (
    discover_benchmark_cases,
    inspect_benchmark_run,
    inspect_measured_pipeline_run,
    report_measured_pipeline_run,
)
from openhcs.agent.path_policy import AgentPathPolicy

if TYPE_CHECKING:
    from openhcs.agent.services.execution_session_service import ExecutionSessionService


class BenchmarkControlService:
    """Guard benchmark evidence while delegating job state to ordinary execution."""

    def __init__(
        self,
        path_policy: AgentPathPolicy,
        execution_service: ExecutionSessionService | None = None,
    ) -> None:
        self._path_policy = path_policy
        self._execution_service = execution_service

    def finalize_measured_run(
        self,
        request: MeasuredPipelineRunFinalizationRequest,
    ) -> MeasuredPipelineRunReceipt:
        """Write benchmark evidence from the ordinary job's exact completion."""

        if self._execution_service is None:
            raise RuntimeError("Measured run finalization requires execution service.")
        from benchmark.openhcs_measured_run import (
            measured_endpoint_provenance,
            retain_measured_openhcs_completion,
        )
        from benchmark.timing import BenchmarkPhase, PhaseTimingTrace
        from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams

        completed = self._execution_service.require_completed_pipeline_execution(
            request.job_id
        )
        observation_path = ZMQAuxiliaryExecutionParams.from_transport(
            completed.submission.config_params
        ).runtime_observation_export_path
        if observation_path is None:
            raise ValueError("Completed job has no runtime observation export.")
        observation_path = self._path_policy.assert_readable(observation_path)
        observation_path = self._path_policy.assert_writable(observation_path)
        record = completed.record
        if record.start_time is None or record.end_time is None:
            raise ValueError("Completed job has no server execution time bounds.")
        if record.end_time < record.start_time:
            raise ValueError("Completed job has reversed server execution time bounds.")
        if record.results_summary is None:
            raise ValueError("Completed job has no server results summary.")
        if completed.endpoint is None:
            raise ValueError("Completed job has no accepting endpoint handshake.")
        phase_timing = PhaseTimingTrace(
            run_id=request.run_id,
            pipeline_name=request.pipeline_name,
            tool="OpenHCS",
        )
        phase_timing.record(
            BenchmarkPhase.SERVER_PIPELINE_JOB,
            seconds=record.end_time - record.start_time,
        )
        return retain_measured_openhcs_completion(
            submission=completed.submission,
            execution_id=record.execution_id,
            results_summary=record.results_summary,
            endpoint_provenance=measured_endpoint_provenance(completed.endpoint),
            phase_timing=phase_timing,
            compile_artifact_id=completed.submission.compile_artifact_id,
        ).receipt

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
