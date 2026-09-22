"""Benchmark-only observation of an ordinary OpenHCS pipeline run."""

from __future__ import annotations

import importlib.util
import json
import sys
import time
from collections.abc import Mapping
from dataclasses import (
    dataclass,
    field,
)
from pathlib import Path
from typing import Any

from zmqruntime.client import EndpointClientSession

from benchmark.contracts.tool_adapter import ToolExecutionError
from openhcs.core.runtime_execution_validation import (
    RuntimeArtifactExecutionObservation,
)
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
    ZMQPipelineRunPhase,
    run_compiled_pipeline,
)
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
)
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams

from .timing import (
    BenchmarkPhase,
    PhaseTimingTrace,
)

ZMQ_RESULTS_SUMMARY_FILENAME = "zmq_results_summary.json"


@dataclass(frozen=True, slots=True)
class _ZMQOpenHCSExecution:
    """Server-side execution observation returned to the benchmark adapter."""

    execution_id: str
    observation_export: ZMQRuntimeExecutionObservationExport
    observation: RuntimeArtifactExecutionObservation
    output_roots: tuple[Path, ...]
    results_summary: Mapping[str, Any]
    endpoint_provenance: Mapping[str, Any]

    @property
    def execution_output_root(self) -> Path:
        if len(self.output_roots) == 1:
            return self.output_roots[0]
        summary_root = self.results_summary.get("output_plate_root")
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

    def __call__(self, event: Mapping[str, Any]) -> None:
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
        *,
        completion_observed_at: float | None = None,
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
        if execute_seconds is None:
            execute_seconds = self._completion_bounded_execution_seconds(
                completion_observed_at,
                compile_seconds=compile_seconds,
                wait_seconds=_phase_seconds_total(
                    phase_timing,
                    BenchmarkPhase.WAIT_OPENHCS,
                ),
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

    def _completion_bounded_execution_seconds(
        self,
        completion_observed_at: float | None,
        *,
        compile_seconds: float | None,
        wait_seconds: float | None,
    ) -> float | None:
        start_at = self.execution_started_at or self.compile_completed_at
        if start_at is not None and completion_observed_at is not None:
            return max(0.0, completion_observed_at - start_at)
        if wait_seconds is None:
            return None
        return max(0.0, wait_seconds - (compile_seconds or 0.0))

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


def _phase_seconds_total(
    phase_timing: PhaseTimingTrace,
    phase: BenchmarkPhase,
) -> float | None:
    records = [
        record.seconds for record in phase_timing.records if record.phase is phase
    ]
    if not records:
        return None
    return sum(records)


def execute_measured_openhcs_pipeline(
    *,
    submission: OpenHCSExecutionSubmission,
    phase_timing: PhaseTimingTrace,
    timing_observer: _ZMQProgressTimingObserver,
    execution_port: int | None = None,
) -> tuple[_ZMQOpenHCSExecution, str]:
    """Measure an ordinary pipeline submission with its requested observation."""

    observation_export_path = ZMQAuxiliaryExecutionParams.from_transport(
        submission.config_params
    ).runtime_observation_export_path
    if observation_export_path is None:
        raise ValueError("Measured OpenHCS runs require runtime observation export.")
    pipeline_source = submission.pipeline_code()
    client = ZMQExecutionClient(
        port=execution_port,
        persistent=False,
        progress_callback=timing_observer,
    )
    with client:
        endpoint = client.connected_endpoint
        if endpoint is None:
            raise ToolExecutionError(
                "OpenHCS ZMQ client entered without a connected endpoint."
            )
        endpoint_session = EndpointClientSession(client)
        compatibility = endpoint_session.observe_compatibility()
        try:
            endpoint_session.require_admitted_client()
        except ValueError as exc:
            raise ToolExecutionError(str(exc)) from exc
        endpoint_provenance = {
            "client_python_executable": sys.executable,
            "client_openhcs_file": str(
                Path(importlib.util.find_spec("openhcs").origin).resolve()
            ),
            "client_openhcs_version": compatibility.expected.version,
            "endpoint_application_identifier": (
                endpoint.application.identifier
                if endpoint.application is not None
                else None
            ),
            "endpoint_openhcs_version": compatibility.observed_version_label,
            "endpoint_pid": (
                endpoint.process_identity.pid
                if endpoint.process_identity is not None
                else None
            ),
            "endpoint_create_time_epoch_seconds": (
                endpoint.process_identity.create_time
                if endpoint.process_identity is not None
                else None
            ),
            "endpoint_log_file_path": endpoint.log_file_path,
            "endpoint_port": endpoint.port,
        }
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
    timing_observer.record_phase_timings(
        phase_timing,
        completion_observed_at=run.completion_observed_at,
    )
    if not observation_export_path.exists():
        raise ToolExecutionError(
            "OpenHCS ZMQ execution completed without writing runtime observation "
            f"export: {observation_export_path}"
        )
    observation_export = ZMQRuntimeExecutionObservationExport.read(
        observation_export_path
    )
    try:
        with phase_timing.phase(BenchmarkPhase.VALIDATE_RUNTIME):
            observation = observation_export.require_valid_observation()
    except RuntimeError as exc:
        raise ToolExecutionError(str(exc)) from exc
    output_roots = tuple(Path(root) for root in observation_export.output_roots)
    results_summary_payload = run.completion_response.get(
        "results", {}
    ) or run.completion_response.get(
        "results_summary",
        {},
    )
    if not isinstance(results_summary_payload, Mapping):
        results_summary_payload = {}
    results_summary = dict(results_summary_payload)
    results_summary_path = observation_export_path.with_name(
        ZMQ_RESULTS_SUMMARY_FILENAME
    )
    results_summary_path.write_text(
        json.dumps(results_summary, indent=2, sort_keys=True),
        encoding="utf-8",
    )
    return (
        _ZMQOpenHCSExecution(
            execution_id=run.execution_id,
            observation_export=observation_export,
            observation=observation,
            output_roots=output_roots,
            results_summary=results_summary,
            endpoint_provenance=endpoint_provenance,
        ),
        pipeline_source,
    )
