"""Reproduce the bounded genuine-well CellProfiler/OpenHCS batch pilot.

This is an experiment driver over the ordinary measured OpenHCS execution
boundary, not an alternative pipeline engine or a paper speedup generator.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
from collections.abc import Mapping
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
from pathlib import Path
from typing import Any

from objectstate.lazy_factory import (
    ensure_global_config_context,
    rebuild_lazy_config_with_new_global_reference,
)
from zmqruntime import DataControlPortPairAuthority
from zmqruntime.messages import ExecutionStatusSnapshot

from benchmark.adapters.cellprofiler import (
    CellProfilerRunRequest,
    HeadlessCellProfilerPipelinePolicy,
    NativeCellProfilerInputDomainStrategy,
)
from benchmark.adapters.cppipe_source import CPPipeSourceRequest, resolve_cppipe_source
from benchmark.adapters.openhcs import _strict_cellprofiler_runtime_equivalence_policy
from benchmark.cellprofiler_comparison import load_comparison_cases
from benchmark.cellprofiler_export_equivalence import (
    cellprofiler_database_export_equivalence,
    cellprofiler_native_shard_equivalence,
)
from benchmark.openhcs_measured_run import (
    _ZMQProgressTimingObserver,
    execute_measured_openhcs_pipeline_on_client,
)
from benchmark.timing import PhaseTimingTrace, completed_server_execution_seconds
from benchmark.well_throughput_scaling import (
    _write_progress_diagnostics,
    well_throughput_start_method_from_manifest,
)
from openhcs.constants.constants import AllComponents
from openhcs.core.config import (
    AnalysisConsolidationConfig,
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyWellFilterConfig,
    MaterializationBackend,
    MultiprocessingStartMethod,
    PathPlanningConfig,
    PipelineConfig,
    VFSConfig,
    WellFilterConfig,
)
from openhcs.core.equivalence.comparison import runtime_image_differences
from openhcs.core.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.input_workspace import InputWorkspacePreparationRequest
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.progress.types import ProgressEvent, ProgressPhase
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.interop.cellprofiler.plate_workspace import (
    prepare_cellprofiler_input_workspace,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
)
from openhcs.runtime.zmq_execution_observation import (
    ZMQRuntimeExecutionObservationExport,
)
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQRuntimeObservationExportScope,
)
from openhcs.serialization.json import to_jsonable

CASE_NAME = "cp_tutorial_translocation_final"
WELL_COUNT = 8


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--openhcs-workers", type=int, default=1)
    parser.add_argument("--native-jobs", type=int, default=1)
    parser.add_argument("--native-python", type=Path, required=True)
    return parser


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _output_inventory(root: Path, files: frozenset[Path]) -> tuple[dict[str, str], ...]:
    return tuple(
        {"path": str(path.relative_to(root)), "sha256": _sha256(path)}
        for path in sorted(files)
    )


def _source_input_inventory(input_dir: Path) -> tuple[dict[str, object], ...]:
    """Hash the staged native image and metadata inputs, following symlinks."""

    files = tuple(sorted(path for path in input_dir.rglob("*") if path.is_file()))
    if not files:
        raise ValueError("Native selected-source workspace contains no input files.")
    return tuple(
        {
            "path": str(path.relative_to(input_dir)),
            "source_path": str(path.resolve()),
            "size_bytes": path.stat().st_size,
            "sha256": _sha256(path),
        }
        for path in files
    )


def _native_python_executable(path: Path, project_root: Path) -> Path:
    """Keep the virtual-environment entrypoint, not its base-interpreter target."""

    executable = path.expanduser()
    if not executable.is_absolute():
        executable = project_root / executable
    if not executable.is_file():
        raise FileNotFoundError(
            f"Native CellProfiler Python does not exist: {executable}"
        )
    return executable


def _invoke_native_worker(
    *,
    native_python: Path,
    worker_script: Path,
    request_path: Path,
    evidence_prefix: Path,
    project_root: Path,
    repetitions: int,
) -> dict[str, object]:
    process = subprocess.run(
        (str(native_python), str(worker_script), str(request_path)),
        cwd=project_root,
        env=os.environ.copy(),
        capture_output=True,
        text=True,
        timeout=900 * (repetitions + 1),
        check=False,
    )
    evidence_prefix.with_name(evidence_prefix.name + "_stdout.log").write_text(
        process.stdout
    )
    evidence_prefix.with_name(evidence_prefix.name + "_stderr.log").write_text(
        process.stderr
    )
    process.check_returncode()
    return json.loads(process.stdout.splitlines()[-1])


def _worker_axis_evidence(
    events: tuple[ProgressEvent, ...],
    *,
    execution_id: str,
    expected_axes: int,
    expected_workers: int,
) -> dict[str, object]:
    selected = tuple(event for event in events if event.execution_id == execution_id)
    starts = tuple(
        event for event in selected if event.phase is ProgressPhase.AXIS_STARTED
    )
    completions = tuple(
        event for event in selected if event.phase is ProgressPhase.AXIS_COMPLETED
    )
    started_axes = tuple(event.axis_id for event in starts)
    completed_axes = tuple(event.axis_id for event in completions)
    if (
        len(starts) != expected_axes
        or len(completions) != expected_axes
        or len(set(started_axes)) != expected_axes
        or set(started_axes) != set(completed_axes)
    ):
        raise RuntimeError(
            "OpenHCS worker progress does not cover each expected axis exactly once."
        )
    worker_pids = tuple(sorted({event.pid for event in starts}))
    if len(worker_pids) != expected_workers:
        raise RuntimeError(
            f"OpenHCS used {len(worker_pids)} worker processes, "
            f"expected {expected_workers}."
        )
    worker_intervals = tuple(
        (
            min(event.timestamp for event in starts if event.pid == pid),
            max(event.timestamp for event in completions if event.pid == pid),
        )
        for pid in worker_pids
    )
    overlap = min(end for _, end in worker_intervals) - max(
        start for start, _ in worker_intervals
    )
    if overlap <= 0:
        raise RuntimeError("OpenHCS worker intervals did not overlap.")
    return {
        "worker_process_ids": worker_pids,
        "worker_interval_overlap_seconds": overlap,
        "axis_events": tuple(
            {
                "axis_id": event.axis_id,
                "phase": event.phase.value,
                "timestamp": event.timestamp,
                "pid": event.pid,
                "worker_slot": event.worker_slot,
                "owned_wells": event.owned_wells,
            }
            for event in selected
        ),
    }


def _global_config(
    output_dir: Path,
    wells: tuple[str, ...],
    *,
    worker_count: int = 1,
    start_method: MultiprocessingStartMethod,
) -> GlobalPipelineConfig:
    return GlobalPipelineConfig(
        num_workers=worker_count,
        use_threading=False,
        multiprocessing_start_method=start_method,
        well_filter_config=WellFilterConfig(well_filter=list(wells)),
        path_planning_config=PathPlanningConfig(
            well_filter=0,
            global_output_folder=output_dir,
            output_dir_suffix="_matched_pilot",
        ),
        vfs_config=VFSConfig(materialization_backend=MaterializationBackend.DISK),
        analysis_consolidation_config=AnalysisConsolidationConfig(enabled=False),
        materialize_runtime_artifacts=False,
    )


def _candidate_pipeline_config(
    imported: PipelineConfig,
    global_config: GlobalPipelineConfig,
    output_dir: Path,
    wells: tuple[str, ...],
) -> PipelineConfig:
    """Inherit the benchmark worker count from the one global authority."""

    pipeline_config = replace(
        imported,
        num_workers=None,
        use_threading=None,
        multiprocessing_start_method=None,
        materialize_runtime_artifacts=False,
        well_filter_config=LazyWellFilterConfig(well_filter=list(wells)),
        path_planning_config=LazyPathPlanningConfig(
            well_filter=0,
            global_output_folder=output_dir,
            output_dir_suffix="_matched_pilot",
        ),
    )
    return rebuild_lazy_config_with_new_global_reference(
        pipeline_config, global_config, GlobalPipelineConfig
    )


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.repetitions < 1 or args.openhcs_workers < 1 or args.native_jobs < 1:
        raise ValueError("Repetitions and worker counts must be positive.")
    if WELL_COUNT % args.native_jobs or (
        args.native_jobs > 1 and args.native_jobs != args.openhcs_workers
    ):
        raise ValueError(
            "Native jobs must partition eight wells evenly and match the "
            "OpenHCS worker count in a concurrency pilot."
        )
    root = args.output_dir.expanduser().resolve()
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"Matched pilot output directory must be empty: {root}")
    root.mkdir(parents=True, exist_ok=True)
    project_root = Path(__file__).resolve().parent.parent
    manifest = args.manifest.expanduser().resolve()
    start_method = well_throughput_start_method_from_manifest(manifest)
    (case,) = (
        case for case in load_comparison_cases(manifest) if case.name == CASE_NAME
    )
    prepared = prepare_cellprofiler_input_workspace(
        InputWorkspacePreparationRequest(
            selected_path=case.dataset_path,
            selected_pipeline_path=case.cppipe_path,
            workspace_root=root / "source_workspace",
            generated_source_path=root / "imported_pipeline.py",
        )
    )
    if prepared.pipeline_import_error is not None:
        raise RuntimeError(prepared.pipeline_import_error)
    if (
        prepared.materialization is None
        or prepared.pipeline_steps is None
        or prepared.pipeline_config is None
    ):
        raise RuntimeError("CellProfiler import did not prepare a complete document.")
    source_wells = {
        source_component_metadata_value(metadata, AllComponents.WELL)
        for metadata in prepared.materialization.source_metadata.values()
    }
    if None in source_wells:
        raise ValueError("Imported source metadata lacks a declared well identity.")
    wells = tuple(sorted(source_wells)[:WELL_COUNT])
    if len(wells) != WELL_COUNT:
        raise ValueError(f"Expected eight genuine source wells, found {wells!r}.")
    provenance = {
        "case": CASE_NAME,
        "wells": wells,
        "manifest_sha256": _sha256(manifest),
        "cppipe_sha256": _sha256(case.cppipe_path),
        "driver_sha256": _sha256(Path(__file__)),
        "native_worker_sha256": _sha256(
            project_root / "benchmark/native_cellprofiler_batch_worker.py"
        ),
        "source_commit": subprocess.check_output(
            ("git", "rev-parse", "HEAD"), cwd=project_root, text=True
        ).strip(),
        "source_dirty": bool(
            subprocess.check_output(
                ("git", "status", "--porcelain"), cwd=project_root, text=True
            ).strip()
        ),
        "native_job_count": args.native_jobs,
        "candidate_worker_count": args.openhcs_workers,
        "candidate_worker_start_method": start_method.value,
        "thread_environment": {
            key: os.environ.get(key)
            for key in (
                "OMP_NUM_THREADS",
                "OPENBLAS_NUM_THREADS",
                "MKL_NUM_THREADS",
                "NUMEXPR_NUM_THREADS",
                "VECLIB_MAXIMUM_THREADS",
                "NPY_DISABLE_CPU_FEATURES",
                "PYTHONHASHSEED",
            )
        },
    }
    (root / "pilot_provenance.json").write_text(json.dumps(provenance, indent=2))

    native_preparation = root / "native_preparation"
    native_global_config = _global_config(
        root / "native", wells, start_method=start_method
    )
    native_request = CellProfilerRunRequest(
        dataset_path=case.dataset_path,
        pipeline_name=case.name,
        cppipe_source=CPPipeSourceRequest(
            dataset_id=case.resolved_dataset_id,
            output_dir=native_preparation,
            cppipe_path=case.cppipe_path,
        ),
        first_image_set=None,
        last_image_set=None,
        timeout_seconds=None,
        metrics=(),
        global_config=native_global_config,
    )
    source = resolve_cppipe_source(native_request.cppipe_source)
    execution_cppipe = HeadlessCellProfilerPipelinePolicy.execution_path(
        source.path, native_preparation
    )
    native_domain = NativeCellProfilerInputDomainStrategy.select_for(
        native_request, source
    ).prepare(native_request, source, execution_cppipe)
    provenance["native_input_inventory"] = _source_input_inventory(
        native_domain.input_dir
    )
    (root / "pilot_provenance.json").write_text(json.dumps(provenance, indent=2))
    native_payload = {
        "pipeline_path": str(native_domain.cppipe_path),
        "input_dir": str(native_domain.input_dir),
        "file_list_path": (
            str(native_domain.file_list_path)
            if native_domain.file_list_path is not None
            else None
        ),
        "output_root": str(root / "native"),
        "expected_image_sets": WELL_COUNT,
        "repetitions": args.repetitions,
    }
    native_request_path = root / "native_request.json"
    native_request_path.write_text(json.dumps(native_payload, indent=2))
    native_python = _native_python_executable(args.native_python, project_root)
    native_worker = project_root / "benchmark/native_cellprofiler_batch_worker.py"
    native_report = _invoke_native_worker(
        native_python=native_python,
        worker_script=native_worker,
        request_path=native_request_path,
        evidence_prefix=root / "native",
        project_root=project_root,
        repetitions=args.repetitions,
    )
    (root / "native_report.json").write_text(json.dumps(native_report, indent=2))
    print("Native warm-up and observed batches complete.", flush=True)

    policy = _strict_cellprofiler_runtime_equivalence_policy()
    (root / "equivalence_policy.json").write_text(
        json.dumps(to_jsonable(policy), indent=2, sort_keys=True)
    )
    shard_reports: tuple[dict[str, object], ...] = ()
    shard_equivalence: list[dict[str, object]] = []
    if args.native_jobs > 1:
        partition_size = WELL_COUNT // args.native_jobs
        request_paths = []
        for index in range(args.native_jobs):
            shard_request = {
                **native_payload,
                "output_root": str(root / "native_shards" / str(index)),
                "expected_image_sets": partition_size,
                "first_image_set": index * partition_size + 1,
                "last_image_set": (index + 1) * partition_size,
            }
            request_path = root / "native_shards" / f"request_{index}.json"
            request_path.parent.mkdir(parents=True, exist_ok=True)
            request_path.write_text(json.dumps(shard_request, indent=2))
            request_paths.append(request_path)
        with ThreadPoolExecutor(max_workers=args.native_jobs) as executor:
            reports = tuple(
                executor.map(
                    lambda item: _invoke_native_worker(
                        native_python=native_python,
                        worker_script=native_worker,
                        request_path=item[1],
                        evidence_prefix=root / "native_shards" / str(item[0]),
                        project_root=project_root,
                        repetitions=args.repetitions,
                    ),
                    enumerate(request_paths),
                )
            )
        shard_reports = reports
        (root / "native_shards" / "reports.json").write_text(
            json.dumps(shard_reports, indent=2)
        )
        for repetition in range(-1, args.repetitions):
            shard_roots = tuple(
                root / "native_shards" / str(index) / str(repetition)
                for index in range(args.native_jobs)
            )
            comparison = cellprofiler_native_shard_equivalence(
                root / "native" / str(repetition),
                shard_roots,
                policy=policy,
            )
            observations_for_repetition = tuple(
                report["observations"][repetition + 1] for report in shard_reports
            )
            invocations = tuple(
                observation["invocation_started_monotonic_seconds"]
                for observation in observations_for_repetition
            )
            starts = tuple(
                observation["first_module_started_monotonic_seconds"]
                for observation in observations_for_repetition
            )
            completions = tuple(
                observation["completed_monotonic_seconds"]
                for observation in observations_for_repetition
            )
            if any(
                invocation > first_module or first_module > completed
                for invocation, first_module, completed in zip(
                    invocations, starts, completions, strict=True
                )
            ):
                raise RuntimeError(
                    "Native batch invocation, first-module and completion "
                    "timestamps are not ordered."
                )
            result = {
                "repetition": repetition,
                "invocation_start_skew_seconds": max(invocations) - min(invocations),
                "invocation_overlap_seconds": min(completions) - max(invocations),
                "invocation_through_completion_makespan_seconds": (
                    max(completions) - min(invocations)
                ),
                "first_module_start_skew_seconds": max(starts) - min(starts),
                "first_module_overlap_seconds": min(completions) - max(starts),
                "first_module_through_completion_makespan_seconds": (
                    max(completions) - min(starts)
                ),
                "differences": tuple(str(value) for value in comparison.differences),
            }
            shard_equivalence.append(result)
            (root / "native_shards" / "equivalence.json").write_text(
                json.dumps(shard_equivalence, indent=2)
            )
            if result["first_module_overlap_seconds"] <= 0 or result["differences"]:
                raise RuntimeError(
                    f"Native shard batch {repetition} did not prove concurrent, "
                    f"equivalent work: {result}"
                )
        print(
            "Native sharded batches overlap and match whole-batch outputs.", flush=True
        )
    axis_events: list[ProgressEvent] = []
    progress_events: list[dict[str, Any]] = []

    def capture_progress_event(event: Mapping[str, Any]) -> None:
        progress_events.append(dict(event))
        if event["phase"] in (
            ProgressPhase.AXIS_STARTED.value,
            ProgressPhase.AXIS_COMPLETED.value,
        ):
            axis_events.append(ProgressEvent.from_dict(dict(event)))

    timing_observer = _ZMQProgressTimingObserver(on_event=capture_progress_event)
    port = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
        transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode,
    ).data_port
    observations = []
    with ZMQExecutionClient(
        port=port, persistent=False, progress_callback=timing_observer
    ) as client:
        for repetition in range(-1, args.repetitions):
            axis_events.clear()
            progress_events.clear()
            print(f"OpenHCS batch {repetition} starting.", flush=True)
            export_scope = (
                ZMQRuntimeObservationExportScope.VALUES
                if repetition < 0
                else ZMQRuntimeObservationExportScope.OUTCOMES
            )
            evidence_dir = root / "candidate_evidence" / str(repetition)
            output_dir = root / "candidate" / str(repetition)
            global_config = _global_config(
                output_dir,
                wells,
                worker_count=args.openhcs_workers,
                start_method=start_method,
            )
            ensure_global_config_context(GlobalPipelineConfig, global_config)
            pipeline_config = _candidate_pipeline_config(
                prepared.pipeline_config, global_config, output_dir, wells
            )
            submission = OpenHCSExecutionSubmission(
                plate_id=case.dataset_path,
                execution_plate_id=prepared.execution_plate_path,
                selected_pipeline_path=case.cppipe_path,
                pipeline_document=PipelineDocumentAuthority.from_values(
                    pipeline_config=pipeline_config,
                    pipeline_steps=prepared.pipeline_steps,
                ),
                global_config=global_config,
            ).with_auxiliary_params(
                ZMQAuxiliaryExecutionParams(
                    runtime_observation_export_path=(evidence_dir / "observation.pkl"),
                    runtime_observation_export_scope=export_scope,
                )
            )
            completed, _ = execute_measured_openhcs_pipeline_on_client(
                client=client,
                submission=submission,
                phase_timing=PhaseTimingTrace(
                    run_id=f"{CASE_NAME}-{repetition}",
                    pipeline_name=CASE_NAME,
                    tool="OpenHCS",
                ),
                timing_observer=timing_observer,
                expected_axis_count=WELL_COUNT,
                require_owned_server=True,
            )
            status = ExecutionStatusSnapshot.from_dict(
                client.poll_status(completed.execution_id)
            )
            record = status.execution
            first_axis_started_at = timing_observer.execution_started_at
            if record is None or first_axis_started_at is None:
                raise RuntimeError(
                    "Completed OpenHCS batch lacks its server job or first-axis "
                    "timing boundary."
                )
            server_job_seconds = completed_server_execution_seconds(
                record, expected_execution_id=completed.execution_id
            )
            worker_evidence = _worker_axis_evidence(
                tuple(axis_events),
                execution_id=completed.execution_id,
                expected_axes=WELL_COUNT,
                expected_workers=args.openhcs_workers,
            )
            _write_progress_diagnostics(
                evidence_dir,
                case_name=CASE_NAME,
                worker_count=args.openhcs_workers,
                well_count=WELL_COUNT,
                events=progress_events,
            )
            if (
                record.start_time is None
                or record.end_time is None
                or first_axis_started_at < record.start_time
                or first_axis_started_at > record.end_time
            ):
                raise RuntimeError(
                    "OpenHCS first-axis event lies outside the completed server job."
                )
            observation = completed.observation_export
            if isinstance(observation, ZMQRuntimeExecutionObservationExport):
                candidate_exports = observation.exports
            else:
                candidate_exports = RuntimeExportObservation.from_output_roots(
                    completed.output_roots
                )
            native_root = root / "native" / str(repetition)
            database_report = cellprofiler_database_export_equivalence(
                native_root, candidate_exports, policy=policy
            )
            native_images = RuntimeOutputSnapshot.from_output_root(native_root).images
            candidate_images = RuntimeOutputSnapshot.from_export_observation(
                candidate_exports
            ).images
            image_differences = runtime_image_differences(
                native_images, candidate_images, policy
            )
            declared_output_files = (
                frozenset(Path(path) for path in observation.exports.output_files)
                if isinstance(observation, ZMQRuntimeExecutionObservationExport)
                else None
            )
            actual_output_files = frozenset(
                path
                for output_root in completed.output_roots
                for path in output_root.rglob("*")
                if path.is_file()
            )
            native_output_files = frozenset(
                path for path in native_root.rglob("*") if path.is_file()
            )
            result = {
                "repetition": repetition,
                "execution_id": completed.execution_id,
                "compile_artifact_id": completed.receipt.compile_artifact_id,
                "endpoint_pid": completed.endpoint_provenance.endpoint_pid,
                "axis_count": completed.axis_count,
                "observation_scope": export_scope.value,
                **worker_evidence,
                "server_job_started_at_epoch_seconds": record.start_time,
                "first_axis_started_at_epoch_seconds": first_axis_started_at,
                "server_job_completed_at_epoch_seconds": record.end_time,
                "server_job_seconds": server_job_seconds,
                "first_axis_through_server_completion_seconds": (
                    record.end_time - first_axis_started_at
                ),
                "native_image_count": len(native_images),
                "candidate_image_count": len(candidate_images),
                "native_output_file_count": len(native_output_files),
                "candidate_output_file_count": len(actual_output_files),
                "declared_output_file_count": (
                    len(declared_output_files)
                    if declared_output_files is not None
                    else None
                ),
                "native_output_inventory": _output_inventory(
                    native_root, native_output_files
                ),
                "candidate_output_inventory": _output_inventory(
                    output_dir, actual_output_files
                ),
                "unexpected_output_files": (
                    tuple(
                        str(path)
                        for path in sorted(actual_output_files - declared_output_files)
                    )
                    if declared_output_files is not None
                    else None
                ),
                "missing_declared_output_files": (
                    tuple(
                        str(path)
                        for path in sorted(declared_output_files - actual_output_files)
                    )
                    if declared_output_files is not None
                    else None
                ),
                "database_differences": tuple(
                    str(difference) for difference in database_report.differences
                ),
                "image_differences": tuple(
                    str(difference) for difference in image_differences
                ),
                "receipt_path": str(evidence_dir / "measured_pipeline_receipt.json"),
            }
            observations.append(result)
            (root / "candidate_report.json").write_text(
                json.dumps(observations, indent=2)
            )
            print(
                f"OpenHCS batch {repetition}: {completed.axis_count} axes, "
                f"{len(result['database_differences'])} database and "
                f"{len(result['image_differences'])} image differences.",
                flush=True,
            )
            if (
                len(native_images) != WELL_COUNT
                or len(candidate_images) != WELL_COUNT
                or len(native_output_files) != len(actual_output_files)
                or (
                    declared_output_files is not None
                    and len(declared_output_files) != len(actual_output_files)
                )
                or result["unexpected_output_files"]
                or result["missing_declared_output_files"]
                or result["database_differences"]
                or result["image_differences"]
            ):
                raise RuntimeError(
                    f"Matched output equivalence failed in repetition {repetition}: "
                    f"{result}"
                )

    final_input_inventory = _source_input_inventory(native_domain.input_dir)
    if final_input_inventory != provenance["native_input_inventory"]:
        raise RuntimeError("Native source images or metadata changed during pilot.")
    provenance["native_input_inventory_after"] = final_input_inventory
    (root / "pilot_provenance.json").write_text(json.dumps(provenance, indent=2))

    report = {
        **provenance,
        "native": native_report,
        "native_shards": shard_reports,
        "native_shard_equivalence": shard_equivalence,
        "candidate": observations,
        "timing_claim": (
            "none: process counts, overlap, and source-owned intervals are "
            "retained, but first-module/first-axis boundary equivalence and "
            "repeated throughput remain under review"
        ),
    }
    (root / "report.json").write_text(json.dumps(report, indent=2))
    print(json.dumps({"output_dir": str(root), "candidate": observations}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
