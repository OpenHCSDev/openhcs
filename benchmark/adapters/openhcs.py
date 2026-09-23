"""OpenHCS tool adapter."""

from __future__ import annotations

import hashlib
import importlib.util
import logging
import os
import signal
import threading
from collections.abc import Mapping, Sequence
from contextlib import ExitStack, contextmanager
from dataclasses import (
    dataclass,
    replace,
)
from pathlib import Path
from typing import Any

from benchmark.adapters.cppipe_source import (
    CPPipeSourceRequest,
    CPPipeSourceResolution,
    materialize_cppipe_reference,
    resolve_cppipe_source,
)
from benchmark.cellprofiler_export_equivalence import (
    cellprofiler_database_export_equivalence,
)
from benchmark.cellprofiler_reference_exports import (
    CellProfilerReferenceArtifactComparison,
    CellProfilerReferenceExportPlan,
)
from benchmark.contracts.metric import MetricCollector
from benchmark.contracts.run_artifacts import MeasuredPipelineRunArtifact
from benchmark.contracts.tool_adapter import (
    BenchmarkResult,
    ToolAdapter,
    ToolExecutionError,
    ToolNotInstalledError,
)
from benchmark.timing import BenchmarkPhase, PhaseTimingTrace
from openhcs.core.config import (
    CompilationDebugConfig,
    GlobalPipelineConfig,
    LazyCompilationDebugConfig,
    PipelineConfig,
)
from openhcs.core.equivalence import RuntimeEquivalencePolicy, RuntimeEquivalenceReport
from openhcs.core.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.equivalence.report import (
    RuntimeEquivalenceDifference,
    RuntimeEquivalenceDifferenceKind,
)
from openhcs.core.function_step_transport import FunctionStepTransportAuthority
from openhcs.core.input_workspace import InputWorkspacePreparationRequest
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.runtime_equivalence import (
    runtime_reference_artifact_equivalence,
)
from openhcs.core.steps.abstract import AbstractStep
from openhcs.interop.cellprofiler.measurement_dialect import (
    cellprofiler_runtime_equivalence_policy,
)
from openhcs.interop.cellprofiler.plate_workspace import (
    prepare_cellprofiler_input_workspace,
)
from openhcs.runtime.zmq_execution_client import OpenHCSExecutionSubmission
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams

from ..openhcs_measured_run import (
    ZMQ_RESULTS_SUMMARY_FILENAME as ZMQ_RESULTS_SUMMARY_FILENAME,
)
from ..openhcs_measured_run import (
    _ZMQOpenHCSExecution,
    _ZMQProgressTimingObserver,
)
from ..openhcs_measured_run import (
    execute_measured_openhcs_pipeline as execute_measured_openhcs_pipeline,
)

logger = logging.getLogger(__name__)


_DUMP_COMPILED_PLANS_ENV = "OPENHCS_BENCHMARK_DUMP_COMPILED_PLANS"


def _strict_cellprofiler_runtime_equivalence_policy() -> RuntimeEquivalencePolicy:
    """Return the benchmark parity policy with broad dialect relaxations disabled."""
    return cellprofiler_runtime_equivalence_policy(
        numeric_abs_tolerance=1e-6,
        numeric_rel_tolerance=1e-6,
        feature_numeric_tolerances=(),
        allow_extra_candidate_measurements=False,
        allow_tie_sensitive_location_mismatches=False,
        allow_unstable_shape_descriptors=False,
        allow_sparse_object_boundary_jitter=False,
        allow_unstable_zernike_descriptors=False,
        threshold_entropy_abs_tolerance=1e-6,
        threshold_sensitive_pair_abs_tolerance=1e-6,
        threshold_sensitive_pair_rel_tolerance=1e-6,
        image_abs_tolerance=1e-6,
        image_rel_tolerance=1e-6,
        image_max_different_fraction=0.0,
    )


def _reference_export_plan(
    cppipe_path: Path,
) -> CellProfilerReferenceExportPlan | None:
    """Load and validate benchmark-only declared export semantics when present."""

    sidecar_path = Path(cppipe_path).with_suffix(".reference_exports.json")
    if not sidecar_path.is_file():
        return None
    plan = CellProfilerReferenceExportPlan.from_sidecar(sidecar_path)
    plan.validate_generated_pipeline(cppipe_path)
    return plan


def _reference_export_equivalence(
    plan: CellProfilerReferenceExportPlan,
    *,
    reference_root: Path,
    candidate_paths: Sequence[Path],
) -> tuple[
    RuntimeEquivalenceReport,
    tuple[CellProfilerReferenceArtifactComparison, ...],
]:
    """Apply declaration-owned numeric-image and categorical-label contracts."""

    try:
        comparisons = plan.compare_observed_outputs(reference_root, candidate_paths)
    except ValueError as exc:
        return (
            RuntimeEquivalenceReport(
                (
                    RuntimeEquivalenceDifference(
                        RuntimeEquivalenceDifferenceKind.IMAGE_CONTENT,
                        str(exc),
                    ),
                )
            ),
            (),
        )
    differences = tuple(
        RuntimeEquivalenceDifference(
            RuntimeEquivalenceDifferenceKind.IMAGE_CONTENT,
            f"declared reference export {comparison.artifact.artifact_name!r} "
            f"differs under {comparison.artifact.comparison}",
        )
        for comparison in comparisons
        if not comparison.equivalent
    )
    return RuntimeEquivalenceReport(differences), comparisons


def _execute_pipeline_via_zmq_server(
    *,
    plate_id: str | Path,
    execution_plate_id: str | Path,
    selected_pipeline_path: str | Path,
    pipeline_steps: Sequence[AbstractStep],
    global_config: GlobalPipelineConfig,
    pipeline_config: PipelineConfig,
    observation_export_path: Path,
    phase_timing: PhaseTimingTrace,
    timing_observer: _ZMQProgressTimingObserver,
    execution_port: int | None = None,
) -> tuple[_ZMQOpenHCSExecution, str]:
    """Submit pipeline through the ZMQ compiler/executor and load observation."""

    transport_pipeline = FunctionStepTransportAuthority.normalize_pipeline(
        pipeline_steps
    )
    submission = OpenHCSExecutionSubmission(
        plate_id=plate_id,
        execution_plate_id=execution_plate_id,
        selected_pipeline_path=selected_pipeline_path,
        pipeline_document=PipelineDocumentAuthority.from_values(
            pipeline_config=pipeline_config, pipeline_steps=transport_pipeline
        ),
        global_config=global_config,
    ).with_auxiliary_params(
        ZMQAuxiliaryExecutionParams(
            runtime_observation_export_path=observation_export_path
        )
    )
    return execute_measured_openhcs_pipeline(
        submission=submission,
        phase_timing=phase_timing,
        timing_observer=timing_observer,
        execution_port=execution_port,
    )


@dataclass(frozen=True, slots=True)
class OpenHCSRunRequest:
    """Decoded benchmark policy for one OpenHCS execution."""

    dataset_path: Path
    pipeline_name: str
    microscope_type: str | None
    cppipe_source: CPPipeSourceRequest
    equivalence_reference_output_dir: Path | None
    compare_image_outputs: bool
    materialize_runtime_artifacts: bool
    raise_on_equivalence_failure: bool
    openhcs_timeout_seconds: float
    dump_compiled_plans: bool
    metrics: tuple[MetricCollector, ...]

    def __post_init__(self) -> None:
        if self.openhcs_timeout_seconds <= 0:
            raise ValueError("openhcs_timeout_seconds must be positive.")

    @property
    def dataset_id(self) -> str:
        return self.cppipe_source.dataset_id

    @property
    def output_dir(self) -> Path:
        return self.cppipe_source.output_dir

    @classmethod
    def from_pipeline_params(
        cls,
        *,
        dataset_path: Path,
        pipeline_name: str,
        pipeline_params: Mapping[str, Any],
        metrics: tuple[MetricCollector, ...],
        output_dir: Path,
    ) -> "OpenHCSRunRequest":
        """Decode the legacy parameter map once at the adapter boundary."""

        resolved_dataset_path = Path(dataset_path)
        resolved_output_dir = Path(output_dir).resolve()
        dataset_id = str(pipeline_params.get("dataset_id", resolved_dataset_path.name))
        microscope_type = pipeline_params.get("microscope_type")
        reference_dir = pipeline_params.get("equivalence_reference_output_dir")
        timeout = pipeline_params.get("openhcs_timeout_seconds")
        if timeout is None:
            timeout = os.environ.get("OPENHCS_BENCHMARK_OPENHCS_TIMEOUT_SECONDS", "120")
        dump_compiled_plans = pipeline_params.get("dump_compiled_plans")
        if dump_compiled_plans is None:
            dump_compiled_plans = os.environ.get(_DUMP_COMPILED_PLANS_ENV)
        return cls(
            dataset_path=resolved_dataset_path,
            pipeline_name=pipeline_name,
            microscope_type=(
                str(microscope_type) if microscope_type is not None else None
            ),
            cppipe_source=CPPipeSourceRequest.from_pipeline_params(
                dataset_id=dataset_id,
                output_dir=resolved_output_dir,
                pipeline_params=pipeline_params,
            ),
            equivalence_reference_output_dir=(
                Path(reference_dir) if reference_dir is not None else None
            ),
            compare_image_outputs=bool(
                pipeline_params.get("compare_image_outputs", True)
            ),
            materialize_runtime_artifacts=bool(
                pipeline_params.get("materialize_runtime_artifacts", True)
            ),
            raise_on_equivalence_failure=bool(
                pipeline_params.get("raise_on_equivalence_failure", True)
            ),
            openhcs_timeout_seconds=float(timeout),
            dump_compiled_plans=_truthy_debug_flag(dump_compiled_plans),
            metrics=metrics,
        )


class OpenHCSAdapter(ToolAdapter):
    """OpenHCS tool adapter."""

    name = "OpenHCS"

    def __init__(
        self,
        *,
        global_config: GlobalPipelineConfig | None = None,
        execution_port: int | None = None,
    ) -> None:
        import openhcs

        self.version = openhcs.__version__
        self.global_config = global_config or GlobalPipelineConfig()
        self.execution_port = execution_port

    def validate_installation(self) -> None:
        """Check OpenHCS is importable."""
        if importlib.util.find_spec("openhcs") is None:
            raise ToolNotInstalledError("OpenHCS not installed")
        import openhcs  # noqa: F401

    def _run_converted_cppipe_pipeline(
        self,
        request: OpenHCSRunRequest,
    ) -> BenchmarkResult:
        """Execute a converted CellProfiler pipeline through the OpenHCS orchestrator."""
        from objectstate.lazy_factory import (
            ensure_global_config_context,
            rebuild_lazy_config_with_new_global_reference,
        )

        from openhcs.core.config import (
            AnalysisConsolidationConfig,
            MaterializationBackend,
            PathPlanningConfig,
            VFSConfig,
        )

        phase_timing = PhaseTimingTrace(
            run_id=f"{request.dataset_id}:{request.pipeline_name}:openhcs",
            pipeline_name=request.pipeline_name,
            tool=self.name,
        )
        with phase_timing.phase(BenchmarkPhase.RESOLVE_SOURCE):
            cppipe_source = self._resolve_cppipe_source(request)
        cppipe_path = cppipe_source.path
        reference_url = cppipe_source.reference_url
        try:
            reference_export_plan = _reference_export_plan(cppipe_path)
        except ValueError as exc:
            raise ToolExecutionError(
                f"Invalid CellProfiler reference-export sidecar for {cppipe_path}: "
                f"{exc}"
            ) from exc

        output_suffix = f"_{request.pipeline_name}_converted_cppipe"
        output_plate_root = (
            request.output_dir / f"{request.dataset_path.name}{output_suffix}"
        )
        generated_source_path = request.output_dir / f"{cppipe_path.stem}_openhcs.py"
        source_workspace_path = (
            request.output_dir
            / f"{request.dataset_path.name}_{cppipe_path.stem}_source_workspace"
        )
        compilation_debug_config = _benchmark_compilation_debug_config(
            self.global_config.compilation_debug_config,
            request=request,
            cppipe_path=cppipe_path,
        )
        compiled_bundle_dump_path = (
            compilation_debug_config.compiled_execution_bundle_path
        )

        equivalence_report = None
        reference_export_comparisons: tuple[
            CellProfilerReferenceArtifactComparison, ...
        ] = ()
        equivalence_failure_message = None
        try:
            with phase_timing.phase(BenchmarkPhase.COMPILE_DIALECT):
                ingestion = prepare_cellprofiler_input_workspace(
                    InputWorkspacePreparationRequest(
                        selected_path=request.dataset_path,
                        selected_pipeline_path=cppipe_path,
                        workspace_root=source_workspace_path,
                        generated_source_path=generated_source_path,
                    )
                )
        except ValueError as exc:
            raise ToolExecutionError(
                "Failed to prepare CellProfiler source workspace for "
                f"{cppipe_path.name}: {exc}"
            ) from exc
        if ingestion.pipeline_import_error is not None:
            raise ToolExecutionError(ingestion.pipeline_import_error.message)
        pipeline_steps = ingestion.pipeline_steps
        pipeline_config = ingestion.pipeline_config
        if pipeline_steps is None or pipeline_config is None:
            raise ToolExecutionError(
                f"CellProfiler pipeline preparation produced no pipeline: {cppipe_path}"
            )
        execution_plate_path = ingestion.execution_plate_path
        generated_pipeline_source = generated_source_path.read_text(encoding="utf-8")
        canonical_pipeline_source = FunctionStepTransportAuthority.source_from_pipeline(
            pipeline_steps
        )
        if generated_pipeline_source != canonical_pipeline_source:
            raise ToolExecutionError(
                "CellProfiler benchmark pipeline source differs from the canonical "
                "UI/ZMQ FunctionStep source before execution."
            )
        if compilation_debug_config.enabled:
            pipeline_config = replace(
                pipeline_config,
                compilation_debug_config=LazyCompilationDebugConfig(
                    enabled=compilation_debug_config.enabled,
                    compiled_execution_bundle_path=(
                        compilation_debug_config.compiled_execution_bundle_path
                    ),
                ),
            )

        global_config = replace(
            self.global_config,
            analysis_consolidation_config=AnalysisConsolidationConfig(
                enabled=False,
            ),
            path_planning_config=PathPlanningConfig(
                global_output_folder=request.output_dir,
                output_dir_suffix=output_suffix,
            ),
            vfs_config=VFSConfig(
                materialization_backend=MaterializationBackend.DISK,
            ),
            compilation_debug_config=compilation_debug_config,
            materialize_runtime_artifacts=request.materialize_runtime_artifacts,
            materialization_results_path=output_plate_root / "results",
        )
        ensure_global_config_context(GlobalPipelineConfig, global_config)
        pipeline_config = rebuild_lazy_config_with_new_global_reference(
            pipeline_config,
            global_config,
            GlobalPipelineConfig,
        )
        observation_export_path = (
            MeasuredPipelineRunArtifact.RUNTIME_OBSERVATION.path_in(request.output_dir)
        )
        with ExitStack() as stack:
            for metric in request.metrics:
                stack.enter_context(metric)
            timing_observer = _ZMQProgressTimingObserver()
            with _openhcs_execution_watchdog(
                request.openhcs_timeout_seconds,
                timing_observer,
            ):
                server_execution, pipeline_source = _execute_pipeline_via_zmq_server(
                    plate_id=request.dataset_path,
                    execution_plate_id=execution_plate_path,
                    selected_pipeline_path=cppipe_path,
                    pipeline_steps=pipeline_steps,
                    global_config=global_config,
                    pipeline_config=pipeline_config,
                    observation_export_path=observation_export_path,
                    phase_timing=phase_timing,
                    timing_observer=timing_observer,
                    execution_port=self.execution_port,
                )
        submitted_pipeline_source_sha = hashlib.sha256(
            pipeline_source.encode("utf-8")
        ).hexdigest()[:12]
        output_roots = server_execution.output_roots
        execution_output_root = (
            server_execution.execution_output_root
            if server_execution.output_roots
            else request.output_dir
        )
        observation = server_execution.observation
        if observation is None:
            raise ToolExecutionError(
                "CellProfiler equivalence requires a value observation export."
            )
        axis_count = server_execution.axis_count
        executed_axes = tuple(observation.records_by_axis)
        csv_output_count = len(observation.exports.table_outputs)
        execution_output_snapshot = (
            RuntimeOutputSnapshot.from_artifact_execution_observation(observation)
        )
        image_output_count = len(execution_output_snapshot.images)
        equivalence_reference = request.equivalence_reference_output_dir
        if equivalence_reference is not None:
            if not equivalence_reference.exists():
                raise ToolExecutionError(
                    f"Equivalence reference output directory does not exist: "
                    f"{equivalence_reference}"
                )
            equivalence_policy = _strict_cellprofiler_runtime_equivalence_policy()
            with phase_timing.phase(BenchmarkPhase.COMPARE_EQUIVALENCE):
                if reference_export_plan is not None:
                    (
                        equivalence_report,
                        reference_export_comparisons,
                    ) = _reference_export_equivalence(
                        reference_export_plan,
                        reference_root=equivalence_reference,
                        candidate_paths=observation.exports.image_outputs,
                    )
                else:
                    reference_snapshot = RuntimeOutputSnapshot.from_output_root(
                        equivalence_reference
                    )
                    if not request.compare_image_outputs:
                        reference_snapshot = RuntimeOutputSnapshot(
                            tables=reference_snapshot.tables,
                        )
                    equivalence_report = runtime_reference_artifact_equivalence(
                        reference_snapshot,
                        observation,
                        policy=equivalence_policy,
                    )
                database_export_report = cellprofiler_database_export_equivalence(
                    equivalence_reference,
                    observation.exports,
                    policy=equivalence_policy,
                )
                equivalence_report = RuntimeEquivalenceReport(
                    (
                        *equivalence_report.differences,
                        *database_export_report.differences,
                    )
                )
            if not equivalence_report.is_equivalent:
                equivalence_failure_message = (
                    "Converted CellProfiler output did not match semantic "
                    f"reference output {equivalence_reference}:\n"
                    + "\n".join(
                        f"- {message}"
                        for message in equivalence_report.failure_messages()
                    )
                )
                if request.raise_on_equivalence_failure:
                    raise ToolExecutionError(equivalence_failure_message)

        metric_results = self._metric_results(request.metrics)
        output_plate_root.mkdir(parents=True, exist_ok=True)
        execution_output_root.mkdir(parents=True, exist_ok=True)

        provenance = {
            "openhcs_version": self.version,
            **server_execution.endpoint_provenance.as_payload(),
            "microscope_type": request.microscope_type,
            "pipeline_source": "converted_cppipe",
            "cppipe_path": str(cppipe_path),
            "generated_source_path": str(generated_source_path),
            "submitted_pipeline_source_sha": submitted_pipeline_source_sha,
            "axis_count": axis_count,
            "csv_output_count": csv_output_count,
            "image_output_count": image_output_count,
            "compiled_output_roots": tuple(str(root) for root in output_roots),
            "phase_timing_records": phase_timing.payloads(),
            "executed_axes": executed_axes,
            "zmq_results_summary_path": str(
                observation_export_path.with_name(ZMQ_RESULTS_SUMMARY_FILENAME)
            ),
        }
        if compiled_bundle_dump_path is not None:
            provenance["compiled_execution_bundle_path"] = str(
                compiled_bundle_dump_path
            )
        if equivalence_reference is not None:
            provenance["equivalence_reference_output_dir"] = str(equivalence_reference)
            provenance["equivalence_difference_count"] = len(
                equivalence_report.differences if equivalence_report else ()
            )
        if reference_export_plan is not None:
            provenance["reference_export_comparisons"] = tuple(
                {
                    "artifact_name": comparison.artifact.artifact_name,
                    "semantic_kind": comparison.artifact.semantic_kind.value,
                    "comparison_contract": comparison.artifact.comparison,
                    "reference_shape": comparison.reference_shape,
                    "candidate_shape": comparison.candidate_shape,
                    "compared_pixel_count": comparison.compared_pixel_count,
                    "different_pixel_count": comparison.different_pixel_count,
                    "out_of_tolerance_pixel_count": (
                        comparison.out_of_tolerance_pixel_count
                    ),
                    "max_abs_difference": comparison.max_abs_difference,
                    "equivalent": comparison.equivalent,
                }
                for comparison in reference_export_comparisons
            )
        if reference_url is not None:
            provenance["cppipe_reference_url"] = reference_url

        return BenchmarkResult(
            tool_name=self.name,
            dataset_id=request.dataset_id,
            pipeline_name=request.pipeline_name,
            metrics=metric_results,
            output_path=execution_output_root,
            success=equivalence_failure_message is None,
            error_message=equivalence_failure_message,
            provenance=provenance,
        )

    def _metric_results(
        self,
        metrics: tuple[MetricCollector, ...],
    ) -> dict[str, Any]:
        """Return metric results, skipping metrics unused by cached execution."""
        results: dict[str, Any] = {}
        for metric in metrics:
            try:
                results[metric.name] = metric.get_result()
            except RuntimeError:
                continue
        return results

    def _resolve_cppipe_source(
        self,
        request: OpenHCSRunRequest,
    ) -> CPPipeSourceResolution:
        """Resolve .cppipe source metadata through the shared adapter helper."""
        return resolve_cppipe_source(
            request.cppipe_source,
            materialize_reference=self._materialize_cppipe_reference,
        )

    def _materialize_cppipe_reference(
        self,
        reference_url: str,
        target_dir: Path,
    ) -> Path:
        """Download one canonical .cppipe file into a stable local path."""
        return materialize_cppipe_reference(reference_url, target_dir)

    def run(
        self,
        dataset_path: Path,
        pipeline_name: str,
        pipeline_params: dict[str, Any],
        metrics: list[Any],
        output_dir: Path,
    ) -> BenchmarkResult:
        """Execute OpenHCS pipeline with metrics."""
        output_dir.mkdir(parents=True, exist_ok=True)

        request = OpenHCSRunRequest.from_pipeline_params(
            dataset_path=dataset_path,
            pipeline_name=pipeline_name,
            pipeline_params=pipeline_params,
            metrics=self._validated_metric_collectors(metrics),
            output_dir=output_dir,
        )
        return self._run_converted_cppipe_pipeline(request)

    def _validated_metric_collectors(
        self,
        metrics: list[Any],
    ) -> tuple[MetricCollector, ...]:
        """Validate metric collectors once and return a typed immutable bundle."""
        validated_metrics: list[MetricCollector] = []
        for metric in metrics:
            if not isinstance(metric, MetricCollector):
                raise ToolExecutionError(
                    f"Metric {metric} does not extend MetricCollector"
                )
            validated_metrics.append(metric)
        return tuple(validated_metrics)


@contextmanager
def _openhcs_execution_watchdog(
    timeout_seconds: float,
    timing_observer: _ZMQProgressTimingObserver,
):
    """Interrupt execution only after server progress has remained silent."""
    alarm_signal = getattr(signal, "SIGALRM", None)
    interval_timer = getattr(signal, "ITIMER_REAL", None)
    set_interval_timer = getattr(signal, "setitimer", None)
    if (
        threading.current_thread() is not threading.main_thread()
        or alarm_signal is None
        or interval_timer is None
        or set_interval_timer is None
    ):
        yield
        return

    previous_handler = signal.getsignal(alarm_signal)

    def _renew_or_raise_timeout(_signum: int, _frame: object) -> None:
        inactivity_seconds = timing_observer.inactivity_seconds()
        remaining_seconds = timeout_seconds - inactivity_seconds
        if remaining_seconds > 0.0:
            set_interval_timer(interval_timer, remaining_seconds)
            return
        raise TimeoutError(
            "OpenHCS execution made no server progress for "
            f"{inactivity_seconds:.1f}s (watchdog threshold "
            f"{timeout_seconds:.1f}s; last progress: "
            f"{timing_observer.progress_description()})."
        )

    signal.signal(alarm_signal, _renew_or_raise_timeout)
    set_interval_timer(interval_timer, timeout_seconds)
    try:
        yield
    except TimeoutError as exc:
        raise ToolExecutionError(str(exc)) from exc
    finally:
        set_interval_timer(interval_timer, 0.0)
        signal.signal(alarm_signal, previous_handler)


def _truthy_debug_flag(value: object) -> bool:
    """Return whether a benchmark debug flag is enabled."""
    if value is None:
        return False
    if isinstance(value, bool):
        return value
    return str(value).strip().lower() in {"1", "true", "yes", "on"}


def _benchmark_compilation_debug_config(
    base_config: CompilationDebugConfig,
    *,
    request: OpenHCSRunRequest,
    cppipe_path: Path,
) -> CompilationDebugConfig:
    if not request.dump_compiled_plans:
        return base_config
    return replace(
        base_config,
        enabled=True,
        compiled_execution_bundle_path=(
            request.output_dir / f"{cppipe_path.stem}_compiled_execution_bundle.pkl"
        ),
    )
