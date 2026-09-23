"""Benchmark-only observation of an ordinary OpenHCS pipeline run."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import time
from collections.abc import Callable, Mapping
from dataclasses import (
    dataclass,
    field,
)
from pathlib import Path
from typing import Any

from zmqruntime import DataControlPortPairAuthority
from zmqruntime.messages import ExecutionStatusSnapshot, PongResponse

from benchmark.contracts.measured_run_receipt import (
    MEASURED_PIPELINE_RUN_RECEIPT_SCHEMA_VERSION,
    MeasuredEndpointProvenance,
    MeasuredPipelineRunReceipt,
)
from benchmark.contracts.run_artifacts import (
    MeasuredPipelineRunArtifact,
    retain_matching_measured_artifacts,
)
from benchmark.contracts.tool_adapter import ToolExecutionError
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.config_document import ConfigDocumentAuthority
from openhcs.core.execution_state import ExecutionOutputPlateSummary
from openhcs.core.runtime_execution_validation import (
    RuntimeArtifactExecutionObservation,
)
from openhcs.runtime.zmq_application import OPENHCS_ENDPOINT_APPLICATION
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
    ZMQPipelineRunPhase,
    run_compiled_pipeline,
)
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
    ZMQRuntimeExecutionOutcomeExport,
)
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQRuntimeObservationExportScope,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

from .timing import (
    BenchmarkPhase,
    PhaseTimingTrace,
    completed_server_execution_seconds,
)

ZMQ_RESULTS_SUMMARY_FILENAME = MeasuredPipelineRunArtifact.RESULTS_SUMMARY.value


def measured_endpoint_provenance(endpoint: PongResponse) -> MeasuredEndpointProvenance:
    """Project one admitted endpoint through the shared application authority."""

    compatibility = OPENHCS_ENDPOINT_APPLICATION.compatibility_with(
        endpoint.application
    )
    compatibility.require_match()
    return MeasuredEndpointProvenance(
        client_python_executable=sys.executable,
        client_openhcs_file=str(
            Path(importlib.util.find_spec("openhcs").origin).resolve()
        ),
        client_openhcs_version=compatibility.expected.version,
        endpoint_application_identifier=(
            endpoint.application.identifier
            if endpoint.application is not None
            else None
        ),
        endpoint_openhcs_version=compatibility.observed_version_label,
        endpoint_pid=(
            endpoint.process_identity.pid
            if endpoint.process_identity is not None
            else None
        ),
        endpoint_create_time_epoch_seconds=(
            endpoint.process_identity.create_time
            if endpoint.process_identity is not None
            else None
        ),
        endpoint_log_file_path=endpoint.log_file_path,
        endpoint_port=endpoint.port,
    )


@dataclass(frozen=True, slots=True)
class _ZMQOpenHCSExecution:
    """Server-side execution observation returned to the benchmark adapter."""

    execution_id: str
    observation_export: (
        ZMQRuntimeExecutionObservationExport | ZMQRuntimeExecutionOutcomeExport
    )
    observation: RuntimeArtifactExecutionObservation | None
    output_roots: tuple[Path, ...]
    results_summary: Mapping[str, Any]
    endpoint_provenance: MeasuredEndpointProvenance
    receipt: MeasuredPipelineRunReceipt

    @property
    def output_plate(self) -> ExecutionOutputPlateSummary:
        return ExecutionOutputPlateSummary.from_results_summary(self.results_summary)

    @property
    def execution_output_root(self) -> Path:
        if len(self.output_roots) == 1:
            return self.output_roots[0]
        summary_root = self.output_plate.output_plate_root
        if summary_root is not None:
            return Path(str(summary_root))
        return self.output_roots[0] if self.output_roots else Path(".")

    @property
    def axis_count(self) -> int:
        return self.observation_export.axis_count


@dataclass(slots=True)
class _ZMQProgressTimingObserver:
    """Capture server progress timestamps for benchmark phase accounting."""

    compile_started_at: float | None = None
    compile_completed_at: float | None = None
    execution_started_at: float | None = None
    execution_completed_at: float | None = None
    last_progress_monotonic: float = field(default_factory=time.monotonic)
    last_progress_phase: str = ""
    last_progress_status: str = ""
    on_event: Callable[[Mapping[str, Any]], None] | None = None

    def begin_run(self) -> None:
        """Discard prior phase bounds when one client observes repeated runs."""

        self.compile_started_at = None
        self.compile_completed_at = None
        self.execution_started_at = None
        self.execution_completed_at = None
        self.last_progress_monotonic = time.monotonic()
        self.last_progress_phase = ""
        self.last_progress_status = ""

    def __call__(self, event: Mapping[str, Any]) -> None:
        if self.on_event is not None:
            self.on_event(event)
        phase = str(event.get("phase", ""))
        status = str(event.get("status", ""))
        self.last_progress_monotonic = time.monotonic()
        self.last_progress_phase = phase
        self.last_progress_status = status
        timestamp = self._timestamp(event)
        if phase == "compile" and status == "started":
            self.compile_started_at = self.compile_started_at or timestamp
            return
        if phase == "compile" and status == "success":
            self.compile_completed_at = timestamp
            return
        if phase == "axis_started":
            self.execution_started_at = self.execution_started_at or timestamp
            return
        if phase == "axis_completed":
            self.execution_completed_at = timestamp

    @staticmethod
    def _timestamp(event: Mapping[str, Any]) -> float:
        value = event.get("timestamp")
        if isinstance(value, (int, float)):
            return float(value)
        return time.time()

    def record_phase_timings(
        self,
        phase_timing: PhaseTimingTrace,
    ) -> None:
        compile_seconds = self._duration(
            self.compile_started_at,
            self.compile_completed_at,
        )
        if compile_seconds is not None:
            phase_timing.record(
                BenchmarkPhase.COMPILE_OPENHCS,
                seconds=compile_seconds,
            )
        execute_seconds = self._duration(
            self.execution_started_at,
            self.execution_completed_at,
        )
        if execute_seconds is not None:
            phase_timing.record(
                BenchmarkPhase.EXECUTE_OPENHCS,
                seconds=execute_seconds,
            )

    @staticmethod
    def _duration(started_at: float | None, ended_at: float | None) -> float | None:
        if started_at is None or ended_at is None:
            return None
        return max(0.0, ended_at - started_at)

    def inactivity_seconds(self, *, observed_at: float | None = None) -> float:
        """Return elapsed monotonic time since the latest server progress event."""
        current = time.monotonic() if observed_at is None else observed_at
        return max(0.0, current - self.last_progress_monotonic)

    def progress_description(self) -> str:
        """Describe the most recently observed server progress event."""
        if not self.last_progress_phase:
            return "none observed"
        if not self.last_progress_status:
            return self.last_progress_phase
        return f"{self.last_progress_phase}/{self.last_progress_status}"


def _completed_server_job_seconds(
    client: ZMQExecutionClient, execution_id: str
) -> float:
    """Read an ordinary completed job's authoritative server time bounds."""

    snapshot = ExecutionStatusSnapshot.from_dict(client.poll_status(execution_id))
    record = snapshot.execution
    if record is None:
        raise ToolExecutionError(
            f"Completed OpenHCS job {execution_id!r} has no valid server time bounds."
        )
    try:
        return completed_server_execution_seconds(
            record, expected_execution_id=execution_id
        )
    except ValueError as exc:
        raise ToolExecutionError(str(exc)) from exc


def _require_measured_submission(
    submission: OpenHCSExecutionSubmission,
    expected_axis_count: int | None,
) -> None:
    """Fail before connecting when a measured request lacks its evidence target."""

    if expected_axis_count is not None and expected_axis_count < 1:
        raise ValueError("Expected axis count must be positive when declared.")
    auxiliary_params = ZMQAuxiliaryExecutionParams.from_transport(
        submission.config_params
    )
    observation_export_path = auxiliary_params.runtime_observation_export_path
    if observation_export_path is None:
        raise ValueError("Measured OpenHCS runs require runtime observation export.")
    if not observation_export_path.is_absolute():
        raise ValueError("Measured OpenHCS observation export path must be absolute.")


def execute_measured_openhcs_pipeline(
    *,
    submission: OpenHCSExecutionSubmission,
    phase_timing: PhaseTimingTrace,
    timing_observer: _ZMQProgressTimingObserver,
    execution_port: int | None = None,
    expected_axis_count: int | None = None,
    require_owned_server: bool = False,
) -> tuple[_ZMQOpenHCSExecution, str]:
    """Measure an ordinary pipeline submission with its requested observation."""

    _require_measured_submission(submission, expected_axis_count)
    client_port = execution_port
    if client_port is None and require_owned_server:
        client_port = DataControlPortPairAuthority.acquire(
            OPENHCS_ZMQ_CONFIG,
            transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode,
        ).data_port
    client = ZMQExecutionClient(
        port=client_port,
        persistent=False,
        progress_callback=timing_observer,
    )
    with client:
        return execute_measured_openhcs_pipeline_on_client(
            client=client,
            submission=submission,
            phase_timing=phase_timing,
            timing_observer=timing_observer,
            expected_axis_count=expected_axis_count,
            require_owned_server=require_owned_server,
        )


def execute_measured_openhcs_pipeline_on_client(
    *,
    client: ZMQExecutionClient,
    submission: OpenHCSExecutionSubmission,
    phase_timing: PhaseTimingTrace,
    timing_observer: _ZMQProgressTimingObserver,
    expected_axis_count: int | None = None,
    require_owned_server: bool = False,
) -> tuple[_ZMQOpenHCSExecution, str]:
    """Measure one ordinary run on a connected client observing ``timing_observer``."""

    _require_measured_submission(submission, expected_axis_count)
    endpoint = client.connected_endpoint
    if endpoint is None:
        raise ToolExecutionError(
            "OpenHCS ZMQ client entered without a connected endpoint."
        )
    try:
        endpoint_provenance = measured_endpoint_provenance(endpoint)
    except ValueError as exc:
        raise ToolExecutionError(str(exc)) from exc
    if require_owned_server and client.owned_server_process_is_alive() is not True:
        raise ToolExecutionError(
            "Measured run requires a client-owned execution server. "
            "The selected endpoint was already in use; choose an unused port."
        )
    timing_observer.begin_run()
    benchmark_phases = {
        ZMQPipelineRunPhase.SUBMIT_COMPILE: BenchmarkPhase.SUBMIT_OPENHCS,
        ZMQPipelineRunPhase.WAIT_COMPILE: BenchmarkPhase.WAIT_OPENHCS,
        ZMQPipelineRunPhase.SUBMIT_EXECUTION: BenchmarkPhase.SUBMIT_OPENHCS,
        ZMQPipelineRunPhase.WAIT_EXECUTION: BenchmarkPhase.WAIT_OPENHCS,
    }
    try:
        run = run_compiled_pipeline(
            client,
            submission,
            phase_context=lambda phase: phase_timing.phase(benchmark_phases[phase]),
        )
    except RuntimeError as exc:
        raise ToolExecutionError(str(exc)) from exc
    phase_timing.record(
        BenchmarkPhase.SERVER_COMPILATION_JOB,
        seconds=_completed_server_job_seconds(client, run.compile_artifact_id),
    )
    phase_timing.record(
        BenchmarkPhase.SERVER_PIPELINE_JOB,
        seconds=_completed_server_job_seconds(client, run.execution_id),
    )
    timing_observer.record_phase_timings(phase_timing)
    return (
        retain_measured_openhcs_completion(
            submission=submission,
            execution_id=run.execution_id,
            results_summary=run.results_summary,
            endpoint_provenance=endpoint_provenance,
            phase_timing=phase_timing,
            compile_artifact_id=run.compile_artifact_id,
            expected_axis_count=expected_axis_count,
        ),
        submission.pipeline_code(),
    )


def retain_measured_openhcs_completion(
    *,
    submission: OpenHCSExecutionSubmission,
    execution_id: str,
    results_summary: Mapping[str, Any],
    endpoint_provenance: MeasuredEndpointProvenance,
    phase_timing: PhaseTimingTrace,
    compile_artifact_id: str | None,
    expected_axis_count: int | None = None,
) -> _ZMQOpenHCSExecution:
    """Validate and retain evidence after an ordinary execution completes."""

    if expected_axis_count is not None and expected_axis_count < 1:
        raise ValueError("Expected axis count must be positive when declared.")
    auxiliary_params = ZMQAuxiliaryExecutionParams.from_transport(
        submission.config_params
    )
    observation_export_path = auxiliary_params.runtime_observation_export_path
    if observation_export_path is None:
        raise ValueError("Measured OpenHCS runs require runtime observation export.")
    if not observation_export_path.is_absolute():
        raise ValueError("Measured OpenHCS observation export path must be absolute.")
    if not observation_export_path.exists():
        raise ToolExecutionError(
            "OpenHCS ZMQ execution completed without writing runtime observation "
            f"export: {observation_export_path}"
        )
    if (
        auxiliary_params.runtime_observation_export_scope
        is ZMQRuntimeObservationExportScope.OUTCOMES
    ):
        observation_export = ZMQRuntimeExecutionOutcomeExport.read(
            observation_export_path
        )
    else:
        observation_export = ZMQRuntimeExecutionObservationExport.read(
            observation_export_path
        )
    if observation_export.execution_id != execution_id:
        raise ToolExecutionError(
            "Runtime observation export execution identity does not match the "
            f"completed job {execution_id!r}: {observation_export.execution_id!r}. "
            "No success receipt was written."
        )
    try:
        with phase_timing.phase(BenchmarkPhase.VALIDATE_RUNTIME):
            if isinstance(observation_export, ZMQRuntimeExecutionOutcomeExport):
                observation_export.require_successful_axes()
                observation = None
            else:
                observation = observation_export.require_valid_observation()
    except RuntimeError as exc:
        raise ToolExecutionError(str(exc)) from exc
    if (
        expected_axis_count is not None
        and observation_export.axis_count != expected_axis_count
    ):
        raise ToolExecutionError(
            f"Expected {expected_axis_count} execution axes, observed "
            f"{observation_export.axis_count}; no success receipt was written."
        )
    artifact_root = observation_export_path.parent
    output_roots = tuple(Path(root) for root in observation_export.output_roots)
    pipeline_source = submission.pipeline_code()
    global_config_source = ConfigDocumentAuthority.render(
        submission.global_pipeline_config,
        expected_config_type=GlobalPipelineConfig,
    )
    results_summary_path = MeasuredPipelineRunArtifact.RESULTS_SUMMARY.path_in(
        artifact_root
    )
    retain_matching_measured_artifacts(
        artifact_root,
        {
            MeasuredPipelineRunArtifact.RESULTS_SUMMARY: json.dumps(
                results_summary, indent=2, sort_keys=True
            ),
            MeasuredPipelineRunArtifact.PIPELINE_SOURCE: pipeline_source,
            MeasuredPipelineRunArtifact.GLOBAL_CONFIG_SOURCE: global_config_source,
        },
    )
    receipt = MeasuredPipelineRunReceipt(
        schema_version=MEASURED_PIPELINE_RUN_RECEIPT_SCHEMA_VERSION,
        run_id=phase_timing.run_id,
        pipeline_name=phase_timing.pipeline_name,
        plate_id=submission.plate_id,
        execution_plate_id=submission.execution_plate_id,
        selected_pipeline_path=submission.selected_pipeline_path,
        execution_id=execution_id,
        pipeline_source_sha256=hashlib.sha256(
            pipeline_source.encode("utf-8")
        ).hexdigest(),
        global_config_source_sha256=hashlib.sha256(
            global_config_source.encode("utf-8")
        ).hexdigest(),
        observation_export_path=observation_export_path,
        results_summary_path=results_summary_path,
        output_roots=output_roots,
        phase_timings=phase_timing.records,
        endpoint_provenance=endpoint_provenance,
        completed_at_epoch_seconds=time.time(),
        compile_artifact_id=compile_artifact_id,
        server_environment=observation_export.server_environment,
        observation_export_scope=auxiliary_params.runtime_observation_export_scope,
        expected_axis_count=expected_axis_count,
        observed_axis_count=observation_export.axis_count,
    )
    receipt.write(MeasuredPipelineRunArtifact.RECEIPT.path_in(artifact_root))
    return _ZMQOpenHCSExecution(
        execution_id=execution_id,
        observation_export=observation_export,
        observation=observation,
        output_roots=output_roots,
        results_summary=results_summary,
        endpoint_provenance=endpoint_provenance,
        receipt=receipt,
    )
