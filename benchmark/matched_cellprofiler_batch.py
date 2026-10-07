"""Reproduce the bounded genuine-well CellProfiler/OpenHCS batch pilot.

This is an experiment driver over the ordinary measured OpenHCS execution
boundary, not an alternative pipeline engine or a paper speedup generator.
"""

from __future__ import annotations

import argparse
import json
import operator
import os
import subprocess
from collections import Counter
from collections.abc import Mapping
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
from dataclasses import asdict, replace
from functools import partial
from multiprocessing import get_context
from pathlib import Path
from typing import Any

import openhcs
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
    NativeCellProfilerSelectedSourceUniverse,
    NativeCellProfilerSourcePlacement,
)
from benchmark.adapters.cppipe_source import CPPipeSourceRequest, resolve_cppipe_source
from benchmark.adapters.openhcs import _strict_cellprofiler_runtime_equivalence_policy
from benchmark.cellprofiler_comparison import load_comparison_cases
from benchmark.cellprofiler_export_equivalence import (
    cellprofiler_database_export_equivalence,
    cellprofiler_native_shard_equivalence,
)
from benchmark.control import inspect_measured_pipeline_run
from benchmark.file_digest import sha256_file
from benchmark.native_batch_contracts import (
    NativeBatchEnvironment,
    NativeBatchReport,
    NativeBatchRequest,
)
from benchmark.native_execution_projection import RepeatedSourceNativeBatchReport
from benchmark.native_measurement_facts import retained_native_measurement_snapshot
from benchmark.openhcs_measured_run import (
    _ZMQProgressTimingObserver,
    execute_measured_openhcs_pipeline_on_client,
)
from benchmark.timing import (
    BenchmarkPhase,
    PhaseTimingRecord,
    PhaseTimingTrace,
    additive_phase_total_seconds,
    completed_server_execution_seconds,
)
from benchmark.well_throughput_scaling import (
    _replicate_source_binding_workspace_wells,
    _synthetic_well_ids,
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
from openhcs.core.equivalence.report import (
    RuntimeEquivalenceDifference,
    RuntimeEquivalenceReport,
)
from openhcs.core.source_matching import SourceImageSetIdentityPolicy
from openhcs.core.equivalence.policy import (
    RuntimeEquivalencePolicy,
    normalize_runtime_identifier,
)
from openhcs.core.input_workspace import InputWorkspacePreparationRequest
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.progress.types import ProgressEvent, ProgressPhase
from openhcs.core.runtime_exports import RuntimeExportObservation
from openhcs.core.runtime_equivalence import (
    RuntimeMeasurementSnapshot,
    runtime_measurement_equivalence,
)
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG
from openhcs.core.source_projection import OpenHCSPlaneAddress
from openhcs.interop.cellprofiler.plate_workspace import (
    prepare_cellprofiler_input_workspace,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
)
from openhcs.runtime.zmq_execution_signature import (
    ZMQAuxiliaryExecutionParams,
    ZMQRuntimeObservationExportScope,
)
from openhcs.serialization.json import to_jsonable


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    cases = parser.add_mutually_exclusive_group(required=True)
    cases.add_argument("--case", help="Run one case from the manifest.")
    cases.add_argument(
        "--all-cases", action="store_true", help="Run the manifest on one owned server."
    )
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument(
        "--well-count", type=int, help="Select the first N declared source wells."
    )
    selection.add_argument(
        "--well",
        dest="requested_wells",
        action="append",
        help="Select one declared source well; repeat for an explicit sample.",
    )
    parser.add_argument(
        "--repeat-assignments",
        type=int,
        help="Repeat one selected source well as independent matched assignments.",
    )
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--openhcs-workers", type=int, default=1)
    parser.add_argument("--native-jobs", type=int, default=1)
    parser.add_argument("--comparison-workers", type=int, default=1)
    parser.add_argument(
        "--comparison-cpus", type=int, nargs="+",
        help="Explicit CPU affinity for saved-output qualification workers.",
    )
    parser.add_argument("--native-python", type=Path, required=True)
    parser.add_argument(
        "--native-reference-root",
        type=Path,
        help="Existing cases root with genuine native reports; missing cases run fresh.",
    )
    parser.add_argument(
        "--candidate-only",
        action="store_true",
        help=(
            "Measure only OpenHCS against a genuine retained repeated-source native "
            "batch; retain actual native clocks and declare projection inputs separately."
        ),
    )
    parser.add_argument(
        "--native-execution-model",
        choices=("retained-first-batch-plus-warm-assignments-v1",),
        help="Explicitly project a fresh native batch; no new native observations.",
    )
    parser.add_argument(
        "--native-measurement-cache-root",
        type=Path,
        help="Reuse retained native semantic snapshots; candidate SCI remains fresh.",
    )
    parser.add_argument(
        "--production-source-root",
        type=Path,
        help="Frozen production checkout, separate from the benchmark harness source.",
    )
    return parser


def _select_genuine_wells(
    available_wells: set[str | None],
    *,
    well_count: int | None,
    requested_wells: tuple[str, ...],
) -> tuple[str, ...]:
    """Resolve one declared sampling choice against imported source metadata."""

    if None in available_wells or "" in available_wells:
        raise ValueError("Imported source metadata lacks a declared well identity.")
    if requested_wells and well_count is not None:
        raise ValueError("Select wells by count or by identity, not both.")
    available = {well for well in available_wells if well is not None}
    if requested_wells:
        if len(set(requested_wells)) != len(requested_wells):
            raise ValueError("Requested pilot wells must be unique.")
        missing = set(requested_wells) - available
        if missing:
            raise ValueError(f"Requested pilot wells are absent: {sorted(missing)!r}.")
        return requested_wells
    if well_count is None or well_count < 1:
        raise ValueError("Well count must be positive when selecting by count.")
    wells = tuple(sorted(available)[:well_count])
    if len(wells) != well_count:
        raise ValueError(
            f"Expected {well_count} genuine source wells, found {wells!r}."
        )
    return wells


def _output_inventory(root: Path, files: frozenset[Path]) -> tuple[dict[str, str], ...]:
    return tuple(
        {
            "path": str(path.relative_to(root)),
            "sha256": sha256_file(path),
        }
        for path in sorted(files)
    )


def _source_input_inventory(
    source_universe: NativeCellProfilerSelectedSourceUniverse,
) -> tuple[dict[str, object], ...]:
    """Hash the selected native source universe, following symlinks."""

    placements = tuple(
        sorted(source_universe.placements, key=lambda placement: placement.relative_path)
    )
    if not placements:
        raise ValueError("Native selected-source universe contains no input files.")
    return tuple(
        {
            "path": str(placement.relative_path),
            "source_path": str(placement.source_path.resolve()),
            "size_bytes": placement.source_path.stat().st_size,
            "sha256": sha256_file(placement.source_path),
        }
        for placement in placements
    )


def _require_compared_output_inventory(
    *,
    reference_files: frozenset[Path],
    candidate_files: frozenset[Path],
    reference_exports: RuntimeExportObservation,
    candidate_exports: RuntimeExportObservation,
    reference_snapshot: RuntimeOutputSnapshot,
    candidate_snapshot: RuntimeOutputSnapshot,
    candidate_managed_files: frozenset[Path] = frozenset(),
    compared_file_report: RuntimeEquivalenceReport = RuntimeEquivalenceReport(()),
) -> None:
    """Reject unqualified output formats and missing scientific output files."""
    # Validate all explicit edges against their object rows, then compare the
    # cross-output correlations before using redundant scalar table inventory.
    from openhcs.core.equivalence.relationships import (
        ExportedRelationshipMeasurementSemantics,
    )
    # The inventory's default dialect is deliberately separate from the CSV
    # comparison policy. Retain its edge admission without rebuilding scalar
    # measurement counters already consumed by the value comparison.
    correlations = tuple(
        ExportedRelationshipMeasurementSemantics.correlated_object_relationships(
            *ExportedRelationshipMeasurementSemantics.validated_output_tables(
                snapshot.tables, RuntimeEquivalencePolicy()
            )
        )
        for snapshot in (reference_snapshot, candidate_snapshot)
    )
    if correlations[0] != correlations[1]:
        raise RuntimeError("Matched saved output relationship correlations differ.")
    comparable_tables = tuple(
        tuple(
            table
            for table in snapshot.tables
            if table.participates_in_comparison
            and not ExportedRelationshipMeasurementSemantics.supports_table(table)
        )
        for snapshot in (reference_snapshot, candidate_snapshot)
    )
    counts = []
    for files, exports, snapshot, managed_files, tables in (
        (
            reference_files,
            reference_exports,
            reference_snapshot,
            frozenset(),
            comparable_tables[0],
        ),
        (
            candidate_files,
            candidate_exports,
            candidate_snapshot,
            candidate_managed_files,
            comparable_tables[1],
        ),
    ):
        files = files - managed_files
        compared_files = (
            frozenset(exports.table_outputs)
            | frozenset(exports.image_outputs)
            | (files & compared_file_report.compared_output_files)
        )
        if files != compared_files:
            raise RuntimeError(
                "Matched output inventory contains files without a value comparison: "
                f"{tuple(sorted(files - compared_files))!r}."
            )
        snapshot.require_image_file_coverage(frozenset(exports.image_outputs))
        count = (
            len(files)
            - len(snapshot.tables)
            - len(exports.image_outputs)
            + len(snapshot.images)
            + len(tables)
        )
        if count < 1:
            raise RuntimeError("Matched batch has no compared scientific output files.")
        counts.append(count)
    if counts[0] != counts[1]:
        raise RuntimeError(
            "Matched scientific output file counts differ: "
            f"reference={counts[0]}, candidate={counts[1]}."
        )
    table_shapes = tuple(
        Counter(
            (
                tuple(
                    (
                        measurement.subject.scope.value,
                        normalize_runtime_identifier(measurement.subject.name),
                    )
                    for measurement in table.measurement_tables()
                ),
                len(table.rows),
            )
            for table in tables
        )
        for tables in comparable_tables
    )
    if table_shapes[0] != table_shapes[1]:
        raise RuntimeError(
            "Matched CSV table row counts differ: "
            f"reference={table_shapes[0]}, candidate={table_shapes[1]}."
        )


def _saved_output_equivalence(
    native_root: Path,
    candidate_exports: RuntimeExportObservation,
    *,
    policy: RuntimeEquivalencePolicy,
    source_workspaces: tuple[Path, ...] = (),
    image_set_policy: SourceImageSetIdentityPolicy = SourceImageSetIdentityPolicy(),
    execution_axis_id: str | None = None,
    actual_candidate_files: frozenset[Path] | None = None,
    candidate_managed_files: frozenset[Path] = frozenset(),
    native_measurement_cache_root: Path | None = None,
    native_reference_report_sha256: str | None = None,
    production_source_commit: str | None = None,
) -> tuple[
    RuntimeEquivalenceReport,
    RuntimeEquivalenceReport,
    tuple[RuntimeEquivalenceDifference, ...],
    RuntimeExportObservation,
    int,
    int,
]:
    """Compare full saved outputs; retain reports and counts, not decoded pixels."""
    database_report = cellprofiler_database_export_equivalence(
        native_root,
        candidate_exports,
        policy=policy,
        execution_axis_id=execution_axis_id,
    )
    native_exports = RuntimeExportObservation.from_output_roots((native_root,))
    native_snapshot = RuntimeOutputSnapshot.from_export_observation(native_exports)
    candidate_snapshot = RuntimeOutputSnapshot.from_export_observation(
        candidate_exports,
        source_workspaces=source_workspaces,
        image_set_policy=image_set_policy,
        execution_axis_id=execution_axis_id,
        measurement_dialect=policy.measurement_dialect,
    )
    csv_report = runtime_measurement_equivalence(
        retained_native_measurement_snapshot(
            native_snapshot,
            policy=policy,
            source_table_paths=native_exports.table_outputs,
            cache_root=native_measurement_cache_root,
            reference_report_sha256=native_reference_report_sha256,
            source_commit=production_source_commit,
        ),
        RuntimeMeasurementSnapshot.from_output_snapshot(
            candidate_snapshot, policy=policy
        ),
        policy=policy,
    )
    image_differences = runtime_image_differences(
        native_snapshot.images,
        candidate_snapshot.images,
        policy,
    )
    _require_compared_output_inventory(
        reference_files=frozenset(
            path for path in native_root.rglob("*") if path.is_file()
        ),
        candidate_files=(
            frozenset(candidate_exports.output_files)
            if actual_candidate_files is None
            else actual_candidate_files
        ),
        reference_exports=native_exports,
        candidate_exports=candidate_exports,
        reference_snapshot=native_snapshot,
        candidate_snapshot=candidate_snapshot,
        candidate_managed_files=candidate_managed_files,
        compared_file_report=database_report,
    )
    return (
        database_report,
        csv_report,
        image_differences,
        native_exports,
        len(native_snapshot.images),
        len(candidate_snapshot.images),
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
    timeout_seconds: float | None,
) -> dict[str, object]:
    request = json.loads(request_path.read_text())
    batch_request = NativeBatchRequest(**request)
    batch_request.temporary_root.mkdir(parents=True, exist_ok=False)
    native_environment = batch_request.worker_environment()
    report_path = evidence_prefix.with_name(
        evidence_prefix.name + "_report.json"
    ).resolve()
    request["report_path"] = str(report_path)
    request_path.write_text(json.dumps(request, indent=2) + "\n")
    with (
        evidence_prefix.with_name(evidence_prefix.name + "_stdout.log").open(
            "w"
        ) as stdout,
        evidence_prefix.with_name(evidence_prefix.name + "_stderr.log").open(
            "w"
        ) as stderr,
    ):
        process = subprocess.run(
            (str(native_python), str(worker_script), str(request_path)),
            cwd=project_root,
            env=native_environment,
            stdout=stdout,
            stderr=stderr,
            text=True,
            timeout=(
                None
                if timeout_seconds is None
                else timeout_seconds
                * (repetitions + 1)
                * max(1, len(request.get("assignment_output_subdirectories", ())))
            ),
            check=False,
        )
    process.check_returncode()
    return json.loads(report_path.read_text())


def _probe_native_environment(
    native_python: Path,
    native_worker: Path,
    request: NativeBatchRequest,
) -> NativeBatchEnvironment:
    """Consume the native report owner's capture without Java or pipeline execution."""
    request.temporary_root.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        (str(native_python), str(native_worker), "--environment"),
        env=request.worker_environment(),
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    return NativeBatchEnvironment(**json.loads(result.stdout))


def _native_reference_inventory(paths: frozenset[Path]) -> tuple[dict[str, str], ...]:
    return tuple(
        {"path": str(path), "sha256": sha256_file(path)} for path in sorted(paths)
    )


def _native_shard_requests(
    report: NativeBatchReport, job_count: int
) -> tuple[NativeBatchRequest, ...]:
    """Derive each exact partition from the original whole-batch request."""
    report.require_complete(report.request.repetitions)
    image_counts = {row.image_set_count for row in report.observations}
    if len(image_counts) != 1:
        raise RuntimeError("Native whole-batch image-set domain changed.")
    (image_count,) = image_counts
    if job_count < 2 or image_count < job_count or image_count % job_count:
        raise RuntimeError("Native image sets do not partition across requested jobs.")
    directories = report.request.assignment_output_subdirectories
    if directories and len(directories) % job_count:
        raise RuntimeError("Native assignments do not partition across requested jobs.")
    if directories:
        domains = tuple(
            tuple(tuple(item) for item in row.assignment_image_set_counts)
            for row in report.observations
        )
        if len(set(domains)) != 1 or len({count for _, count in domains[0]}) != 1:
            raise RuntimeError(
                "Native repeated assignments have unequal input domains."
            )
    shard_root = Path(report.request.output_root).parent / "native_shards"
    partition = image_count // job_count
    assignment_partition = len(directories) // job_count
    return tuple(
        replace(
            report.request,
            output_root=str(shard_root / str(index)),
            expected_image_sets=partition,
            first_image_set=1 if directories else index * partition + 1,
            last_image_set=None if directories else (index + 1) * partition,
            assignment_output_subdirectories=directories[
                index * assignment_partition : (index + 1) * assignment_partition
            ],
            start_barrier_root=str(shard_root / "start_barrier"),
            start_barrier_job_count=job_count,
            start_barrier_job_index=index,
            report_path=str(shard_root / f"{index}_report.json"),
        )
        for index in range(job_count)
    )


def _validate_native_shard_reports(
    whole: NativeBatchReport,
    reports: tuple[dict[str, object], ...],
    job_count: int,
) -> frozenset[Path]:
    """Admit complete original reports and their exact partition/barrier custody."""
    requests = _native_shard_requests(whole, job_count)
    if len(reports) != job_count:
        raise RuntimeError("Retained native shard reports are incomplete.")
    files = set()
    for request, payload in zip(requests, reports, strict=True):
        report = NativeBatchReport.from_payload(payload)
        report.require_complete(whole.request.repetitions)
        report_path = Path(request.report_path)
        request_path = report_path.with_name(
            f"request_{request.start_barrier_job_index}.json"
        )
        if (
            report.request != request
            or NativeBatchRequest(**json.loads(request_path.read_text())) != request
            or json.loads(report_path.read_text()) != payload
        ):
            raise RuntimeError(
                "Native shard differs from its original partition/request/report."
            )
        whole.environment.require_equivalent(report.environment)
        for whole_row, row in zip(whole.observations, report.observations, strict=True):
            expected_domains = (
                tuple(
                    item
                    for item in whole_row.assignment_image_set_counts
                    if item[0] in request.assignment_output_subdirectories
                )
                if request.assignment_output_subdirectories
                else (("", request.expected_image_sets),)
            )
            if row.image_set_count != request.expected_image_sets or tuple(
                tuple(item) for item in row.assignment_image_set_counts
            ) != tuple(tuple(item) for item in expected_domains):
                raise RuntimeError(
                    "Native shard assignment coverage differs from its partition."
                )
        files.update((request_path, report_path))
    barrier_root = Path(requests[0].start_barrier_root)
    expected_markers = frozenset(
        barrier_root / f"repetition_{repetition}_job_{index}.ready"
        for repetition in range(whole.request.repetitions)
        for index in range(job_count)
    )
    if frozenset(barrier_root.iterdir()) != expected_markers or any(
        not path.is_file() for path in expected_markers
    ):
        raise RuntimeError("Native shard barrier membership is incomplete or changed.")
    return frozenset(files) | expected_markers


def _concurrent_timing(
    reports: tuple[dict[str, Any], ...], repetition: int
) -> dict[str, float | int]:
    """Derive simultaneous makespans from the original additive report clocks."""
    observations = tuple(
        next(row for row in report["observations"] if row["repetition"] == repetition)
        for report in reports
    )
    invocations = tuple(
        row["invocation_started_monotonic_seconds"] for row in observations
    )
    starts = tuple(row["pipeline_started_monotonic_seconds"] for row in observations)
    completions = tuple(row["completed_monotonic_seconds"] for row in observations)
    if any(
        invocation > start or start > completed
        for invocation, start, completed in zip(
            invocations, starts, completions, strict=True
        )
    ):
        raise RuntimeError("Native batch timing boundaries are out of order.")
    if len(reports) > 1 and min(completions) <= max(starts):
        raise RuntimeError("Native batch jobs did not overlap during analysis.")
    return {
        "repetition": repetition,
        "invocation_start_skew_seconds": max(invocations) - min(invocations),
        "invocation_overlap_seconds": min(completions) - max(invocations),
        "invocation_through_completion_makespan_seconds": max(completions)
        - min(invocations),
        "pipeline_start_skew_seconds": max(starts) - min(starts),
        "pipeline_overlap_seconds": min(completions) - max(starts),
        "pipeline_execution_makespan_seconds": max(completions) - min(starts),
    }


def _native_shard_equivalence(
    whole: NativeBatchReport,
    reports: tuple[dict[str, object], ...],
    *,
    policy: RuntimeEquivalencePolicy,
) -> list[dict[str, object]]:
    """Recompare all original physical shard outputs to the whole native run."""
    results = []
    for repetition in range(-1, whole.request.repetitions):
        native_root = Path(whole.observations[repetition + 1].output_root)
        shard_roots = tuple(
            Path(report["observations"][repetition + 1]["output_root"])
            for report in reports
        )
        directories = whole.request.assignment_output_subdirectories
        if not directories:
            comparison = cellprofiler_native_shard_equivalence(
                native_root, shard_roots, policy=policy
            )
        else:
            comparisons = []
            covered_files = set()
            for directory in directories:
                roots = tuple(
                    root / directory
                    for root in shard_roots
                    if (root / directory).is_dir()
                )
                if len(roots) != 1:
                    raise RuntimeError(
                        "Native workers must own each repeated assignment exactly once."
                    )
                exports = RuntimeExportObservation.from_output_root(roots[0])
                db, csv, images, _, _, _ = _saved_output_equivalence(
                    native_root / directory, exports, policy=policy
                )
                comparisons.extend((db, csv, RuntimeEquivalenceReport(images)))
                covered_files.update(exports.output_files)
            actual_files = frozenset(
                path
                for root in shard_roots
                for path in root.rglob("*")
                if path.is_file()
            )
            if covered_files != actual_files:
                raise RuntimeError(
                    "Native assignment comparison leaves unowned output files."
                )
            comparison = RuntimeEquivalenceReport(
                tuple(
                    difference
                    for report in comparisons
                    for difference in report.differences
                ),
                frozenset(
                    path
                    for report in comparisons
                    for path in report.compared_output_files
                ),
            )
        result = {
            **_concurrent_timing(reports, repetition),
            "differences": tuple(str(value) for value in comparison.differences),
        }
        results.append(result)
        if result["differences"]:
            raise RuntimeError(
                f"Native shard batch {repetition} differs from whole work: {result}"
            )
    return results


def _reuse_native_report(
    reference_case: Path,
    *,
    native_payload: Mapping[str, object],
    native_python: Path,
    native_worker: Path,
    provenance: dict[str, object],
) -> dict[str, object]:
    """Qualify native measurements independently of the candidate's source revision."""
    if sha256_file(native_worker) != provenance["native_worker_sha256"]:
        raise RuntimeError("Current native worker differs from its declared source.")
    if (
        sha256_file(native_worker.with_name("native_batch_contracts.py"))
        != provenance["native_contract_sha256"]
    ):
        raise RuntimeError(
            "Current native report contract differs from its declared source."
        )
    report_path = reference_case / "native_report.json"
    origin_path = reference_case / "pilot_provenance.json"
    request_path = reference_case / "native_request.json"
    report = json.loads(report_path.read_text())
    typed_report = NativeBatchReport.from_payload(report)
    origin = json.loads(origin_path.read_text())
    request = typed_report.request
    original_request = NativeBatchRequest(**json.loads(request_path.read_text()))
    if request != original_request:
        raise RuntimeError("Retained native report differs from its original request.")
    planned_request = NativeBatchRequest(**native_payload)
    request.require_same_workload(planned_request)
    for key in (
        "case",
        "wells",
        "selected_source_wells",
        "assignment_scope",
        "cppipe_sha256",
        "native_worker_sha256",
        "native_contract_sha256",
        "native_job_count",
        "thread_environment",
    ):
        if origin[key] != json.loads(json.dumps(provenance[key])):
            raise RuntimeError(f"Retained native reference differs in {key}.")
    # Exact prepared bytes reject unsupported path-dependent differences rather
    # than normalizing arbitrary CPPipe fields or accepting a changed input role.
    original_pipeline = Path(request.pipeline_path)
    current_pipeline = Path(native_payload["pipeline_path"])
    if sha256_file(original_pipeline) != sha256_file(current_pipeline):
        raise RuntimeError("Retained native effective CPPipe bytes differ.")
    original_file_list = request.file_list_path
    current_file_list = native_payload["file_list_path"]
    if (original_file_list is None) != (current_file_list is None) or (
        original_file_list is not None
        and Path(original_file_list).read_bytes()
        != Path(current_file_list).read_bytes()
    ):
        raise RuntimeError("Retained native ordered source file list differs.")
    current_inventory = json.loads(json.dumps(provenance["native_input_inventory"]))
    original_source_universe = NativeCellProfilerSelectedSourceUniverse(
        tuple(Path(row["source_path"]) for row in origin["native_input_inventory"]),
        placements=tuple(
            NativeCellProfilerSourcePlacement(Path(row["source_path"]), Path(row["path"]))
            for row in origin["native_input_inventory"]
        ),
    )
    original_inventory = json.loads(json.dumps(_source_input_inventory(original_source_universe)))
    if (
        original_inventory != origin["native_input_inventory"]
        or original_inventory != current_inventory
    ):
        raise RuntimeError("Retained native source images or metadata differ.")
    typed_report.environment.require_equivalent(
        _probe_native_environment(native_python, native_worker, planned_request)
    )
    typed_report.require_complete(int(native_payload["repetitions"]))
    if any(
        row["image_set_count"] != origin["native_image_set_count"]
        for row in report["observations"]
    ):
        raise RuntimeError(
            "Retained native image-set domain changed between observations."
        )
    outputs = frozenset(
        path
        for row in report["observations"]
        for path in Path(row["output_root"]).rglob("*")
        if path.is_file()
    )
    candidate_path = reference_case / "candidate_report.json"
    if candidate_path.is_file():
        for row in json.loads(candidate_path.read_text()):
            run_root = Path(request.output_root) / str(row["repetition"])
            files = frozenset(path for path in run_root.rglob("*") if path.is_file())
            if (
                json.loads(json.dumps(_output_inventory(run_root, files)))
                != row["native_output_inventory"]
            ):
                raise RuntimeError("Previously inventoried native outputs changed.")
    source_files = {report_path, origin_path, request_path, original_pipeline}
    if original_file_list is not None:
        source_files.add(Path(original_file_list))
    provenance.update(
        native_reference_report_path=str(report_path),
        native_reference_report_sha256=sha256_file(report_path),
        native_reference_source_commit=origin.get(
            "native_reference_source_commit", origin["source_commit"]
        ),
        native_reference_file_inventory=_native_reference_inventory(
            outputs | frozenset(source_files)
        ),
    )
    return report


def _reuse_native_projection_source(
    reference_case: Path,
    *,
    native_payload: Mapping[str, object],
    native_python: Path,
    native_worker: Path,
    provenance: dict[str, object],
) -> dict[str, object]:
    """Validate an observed repeated-source batch at its actual cardinality."""
    if (
        len(provenance["selected_source_wells"]) != 1
        or provenance["assignment_scope"] != "independent repeated source assignments"
        or provenance["native_job_count"] != 1
    ):
        raise RuntimeError(
            "Candidate-only capture requires one repeated source and serial native."
        )
    source = RepeatedSourceNativeBatchReport.from_payload(
        json.loads((reference_case / "native_report.json").read_text())
    )
    planned = source.validation_request(
        NativeBatchRequest(**native_payload), len(provenance["wells"])
    )
    reference_provenance = dict(provenance)
    reference_provenance["wells"] = _synthetic_well_ids(
        len(source.assignment_directories)
    )
    report = _reuse_native_report(
        reference_case,
        native_payload=asdict(planned),
        native_python=native_python,
        native_worker=native_worker,
        provenance=reference_provenance,
    )
    provenance.update(
        (key, value)
        for key, value in reference_provenance.items()
        if key.startswith("native_reference_")
    )
    return report


def _reuse_native_shard_reports(
    reference_case: Path,
    *,
    native_report: Mapping[str, object],
    provenance: dict[str, object],
    policy: RuntimeEquivalencePolicy,
) -> tuple[tuple[dict[str, object], ...], list[dict[str, object]]]:
    """Qualify original parallel runs without invoking native analysis again."""
    reports_path = reference_case / "native_shards" / "reports.json"
    equivalence_path = reference_case / "native_shards" / "equivalence.json"
    reports = tuple(json.loads(reports_path.read_text()))
    whole = NativeBatchReport.from_payload(native_report)
    files = _validate_native_shard_reports(
        whole, reports, provenance["native_job_count"]
    )
    original_equivalence = json.loads(equivalence_path.read_text())
    if tuple(row["repetition"] for row in original_equivalence) != tuple(
        range(-1, whole.request.repetitions)
    ):
        raise RuntimeError(
            "Original native shard equivalence is incomplete or reordered."
        )
    files |= frozenset((reports_path, equivalence_path)) | frozenset(
        path
        for report in reports
        for observation in report["observations"]
        for path in Path(observation["output_root"]).rglob("*")
        if path.is_file()
    )
    candidate_path = reference_case / "candidate_report.json"
    if candidate_path.is_file():
        files |= frozenset((candidate_path,))
    files |= frozenset(
        Path(row["path"]) for row in provenance["native_reference_file_inventory"]
    )
    provenance["native_reference_file_inventory"] = _native_reference_inventory(files)
    equivalence = _native_shard_equivalence(whole, reports, policy=policy)
    if json.loads(json.dumps(equivalence)) != original_equivalence:
        raise RuntimeError(
            "Retained native shard science or simultaneous clocks changed."
        )
    _require_native_reference_unchanged(provenance)
    return reports, equivalence


def _require_native_reference_unchanged(provenance: Mapping[str, object]) -> None:
    """Retained inputs and outputs stay untouched throughout fresh scientific checks."""
    if "native_reference_file_inventory" not in provenance:
        return
    before = provenance["native_reference_file_inventory"]
    paths = frozenset(Path(row["path"]) for row in before)
    report = NativeBatchReport.from_payload(
        json.loads(Path(provenance["native_reference_report_path"]).read_text())
    )
    reports = (report,)
    if provenance["native_job_count"] > 1:
        reports += tuple(
            NativeBatchReport.from_payload(payload)
            for payload in json.loads(
                Path(provenance["native_reference_report_path"])
                .with_name("native_shards")
                .joinpath("reports.json")
                .read_text()
            )
        )
    paths |= frozenset(
        path
        for retained in reports
        for observation in retained.observations
        for path in Path(observation.output_root).rglob("*")
        if path.is_file()
    )
    if len(reports) > 1:
        paths |= frozenset(Path(reports[1].request.start_barrier_root).iterdir())
    if json.loads(json.dumps(_native_reference_inventory(paths))) != json.loads(
        json.dumps(before)
    ):
        raise RuntimeError(
            "Retained native reference files changed during qualification."
        )


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
    if args.comparison_workers < 1:
        raise ValueError("Comparison worker count must be positive.")
    if args.comparison_workers > 1 and (
        args.repeat_assignments is None
        or not args.comparison_cpus
        or len(set(args.comparison_cpus)) < args.comparison_workers
        or any(cpu < 0 or cpu >= os.cpu_count() for cpu in args.comparison_cpus)
    ):
        raise ValueError(
            "Parallel saved comparisons require repeated assignments and "
            "explicit CPU affinity with at least one CPU per worker."
        )
    if args.native_jobs > 1 and args.native_jobs != args.openhcs_workers:
        raise ValueError(
            "Native and OpenHCS worker counts must match in a concurrency pilot."
        )
    if args.native_reference_root is not None:
        if not args.native_reference_root.expanduser().is_dir():
            raise FileNotFoundError("Native reference cases root does not exist.")
    if args.repeat_assignments is not None and args.repeat_assignments < 1:
        raise ValueError("Repeated assignment count must be positive.")
    if args.native_measurement_cache_root is not None and args.native_reference_root is None:
        raise ValueError("Native semantic cache requires retained native source custody.")
    if args.native_execution_model is not None and not args.candidate_only:
        raise ValueError("A native execution model requires candidate-only capture.")
    if args.candidate_only and (
        args.native_reference_root is None
        or args.repeat_assignments is None
        or args.native_jobs != 1
        or args.production_source_root is None
    ):
        raise ValueError(
            "Candidate-only capture requires retained native outputs, repeated "
            "assignments, serial native reference, and a production source root."
        )
    cases = load_comparison_cases(args.manifest.expanduser().resolve())
    selected_cases = tuple(
        case for case in cases if args.all_cases or case.name == args.case
    )
    if not selected_cases:
        raise ValueError(f"No manifest case matches {args.case!r}.")
    output_root = args.output_dir.expanduser().resolve()
    if output_root.exists() and any(output_root.iterdir()):
        raise FileExistsError(
            f"Matched pilot output directory must be empty: {output_root}"
        )
    port = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
        transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode,
    ).data_port
    with ZMQExecutionClient(port=port, persistent=False) as client:
        for case in selected_cases:
            case_args = argparse.Namespace(**vars(args))
            case_args.case = case.name
            case_args.output_dir = (
                output_root / case.name if args.all_cases else output_root
            )
            _run_case(case_args, client)
    return 0


def _run_case(args: argparse.Namespace, client: ZMQExecutionClient) -> int:
    """Qualify one case while retaining the suite's prepared execution server."""

    project_root = Path(__file__).resolve().parent.parent
    production_root = (
        args.production_source_root.expanduser().resolve()
        if args.production_source_root is not None
        else project_root
    )
    if args.production_source_root is not None and (
        Path(openhcs.__file__).resolve().parent.parent != production_root
    ):
        raise RuntimeError(
            "Loaded OpenHCS does not belong to the declared production root."
        )
    source_commit = subprocess.check_output(
        ("git", "rev-parse", "HEAD"), cwd=production_root, text=True
    ).strip()
    source_dirty = bool(
        subprocess.check_output(
            ("git", "status", "--porcelain"), cwd=production_root, text=True
        ).strip()
    )
    if args.production_source_root is not None and source_dirty:
        raise RuntimeError("Declared production checkout must be clean.")
    harness_inventory = {
        str(path.relative_to(project_root)): sha256_file(path)
        for path in sorted((project_root / "benchmark").rglob("*.py"))
    }
    root = args.output_dir.expanduser().resolve()
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"Matched pilot output directory must be empty: {root}")
    root.mkdir(parents=True, exist_ok=True)
    manifest = args.manifest.expanduser().resolve()
    start_method = well_throughput_start_method_from_manifest(manifest)
    (case,) = (
        case for case in load_comparison_cases(manifest) if case.name == args.case
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
    wells = _select_genuine_wells(
        source_wells,
        well_count=args.well_count,
        requested_wells=tuple(args.requested_wells or ()),
    )
    source_wells = wells
    if args.repeat_assignments is not None:
        if len(source_wells) != 1:
            raise ValueError(
                "Repeated assignments require exactly one selected source well."
            )
        wells = _synthetic_well_ids(args.repeat_assignments)
    assignment_directories = (
        tuple(OpenHCSPlaneAddress.component_token(well) for well in wells)
        if args.repeat_assignments is not None and len(wells) > 1
        else ()
    )
    well_count = len(wells)
    if args.openhcs_workers > well_count:
        raise ValueError("OpenHCS workers cannot exceed the selected assignment count.")
    if well_count % args.native_jobs:
        raise ValueError(
            "Native jobs must partition the selected wells evenly in a "
            "concurrency pilot."
        )
    provenance = {
        "case": case.name,
        "wells": wells,
        "selected_source_wells": source_wells,
        "assignment_scope": (
            "independent repeated source assignments"
            if args.repeat_assignments is not None
            else "genuine source wells"
        ),
        "manifest_sha256": sha256_file(manifest),
        "cppipe_sha256": sha256_file(case.cppipe_path),
        "driver_sha256": sha256_file(Path(__file__)),
        "native_worker_sha256": sha256_file(
            project_root / "benchmark/native_cellprofiler_batch_worker.py"
        ),
        "native_contract_sha256": sha256_file(
            project_root / "benchmark/native_batch_contracts.py"
        ),
        "source_commit": source_commit,
        "source_dirty": source_dirty,
        "comparison_workers": args.comparison_workers,
        "comparison_cpus": args.comparison_cpus,
        "native_measurement_cache_root": (
            str(args.native_measurement_cache_root.expanduser().resolve())
            if args.native_measurement_cache_root is not None else None
        ),
        "production_source_root": str(production_root),
        "benchmark_harness": {
            "source_root": str(project_root),
            "source_commit": subprocess.check_output(
                ("git", "rev-parse", "HEAD"), cwd=project_root, text=True
            ).strip(),
            "source_dirty": bool(
                subprocess.check_output(
                    ("git", "status", "--porcelain"), cwd=project_root, text=True
                ).strip()
            ),
            "file_sha256": harness_inventory,
        },
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
        root / "native", source_wells, start_method=start_method
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
        timeout_seconds=case.cellprofiler_timeout_seconds,
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
    if args.repeat_assignments is not None:
        _replicate_source_binding_workspace_wells(
            prepared.materialization.metadata_path,
            wells,
            source_well_filter=native_global_config.well_filter_config,
        )
    provenance["native_input_inventory"] = _source_input_inventory(
        native_domain.source_universe
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
        "expected_image_sets": None,
        "repetitions": args.repetitions,
        "assignment_output_subdirectories": assignment_directories,
    }
    native_request_path = root / "native_request.json"
    native_request_path.write_text(json.dumps(native_payload, indent=2))
    native_python = _native_python_executable(args.native_python, project_root)
    native_worker = project_root / "benchmark/native_cellprofiler_batch_worker.py"
    reference_case = (
        args.native_reference_root.expanduser().resolve() / case.name
        if args.native_reference_root is not None
        else None
    )
    if reference_case is not None and reference_case.exists():
        native_report = (
            _reuse_native_projection_source
            if args.candidate_only
            else _reuse_native_report
        )(
            reference_case,
            native_payload=native_payload,
            native_python=native_python,
            native_worker=native_worker,
            provenance=provenance,
        )
        native_request_path.write_text(
            json.dumps(
                asdict(NativeBatchReport.from_payload(native_report).request), indent=2
            )
        )
    else:
        if args.candidate_only:
            raise FileNotFoundError(
                "Candidate-only native reference must already exist."
            )
        native_report = _invoke_native_worker(
            native_python=native_python,
            worker_script=native_worker,
            request_path=native_request_path,
            evidence_prefix=root / "native",
            project_root=project_root,
            repetitions=args.repetitions,
            timeout_seconds=native_request.timeout_seconds,
        )
    (root / "native_report.json").write_text(json.dumps(native_report, indent=2))
    projection_inputs = None
    native_comparison_directories = assignment_directories or ("",)
    provenance["native_capture_status"] = (
        "retained_projection_source"
        if args.candidate_only
        else "retained" if "native_reference_report_path" in provenance else "measured"
    )
    if args.candidate_only:
        projection_source = RepeatedSourceNativeBatchReport.from_payload(native_report)
        native_comparison_directories = projection_source.comparison_directories(
            well_count
        )
        projection_method = (
            projection_source.projected_fresh_batch
            if args.native_execution_model is not None
            else projection_source.projection_inputs
        )
        projection_inputs = projection_method(
            well_count,
            source_report_path=Path(provenance["native_reference_report_path"]),
            source_report_sha256=provenance["native_reference_report_sha256"],
        )
    native_image_set_counts = {
        observation["image_set_count"] for observation in native_report["observations"]
    }
    if len(native_image_set_counts) != 1:
        raise RuntimeError("Native whole-batch image-set count changed between runs.")
    (native_image_set_count,) = native_image_set_counts
    if args.repeat_assignments is not None:
        expected_directories = (
            projection_source.assignment_directories
            if args.candidate_only
            else assignment_directories or ("",)
        )
        observed_domains = tuple(
            tuple(
                (str(directory), int(count))
                for directory, count in observation["assignment_image_set_counts"]
            )
            for observation in native_report["observations"]
        )
        if (
            any(
                tuple(directory for directory, _ in domain) != expected_directories
                for domain in observed_domains
            )
            or len(set(observed_domains)) != 1
            or any(count < 1 for _, count in observed_domains[0])
            or len({count for _, count in observed_domains[0]}) != 1
            or sum(count for _, count in observed_domains[0]) != native_image_set_count
        ):
            raise RuntimeError(
                "Native repeated assignments must retain complete identical input domains."
            )
    if native_image_set_count < args.native_jobs or (
        native_image_set_count % args.native_jobs
    ):
        raise RuntimeError(
            "Native image sets cannot be partitioned evenly across requested jobs."
        )
    provenance["native_image_set_count"] = native_image_set_count
    (root / "pilot_provenance.json").write_text(json.dumps(provenance, indent=2))
    print(
        (
            "Validated retained genuine native batches."
            if "native_reference_report_path" in provenance
            else "Native warm-up and observed batches complete."
        ),
        flush=True,
    )

    policy = _strict_cellprofiler_runtime_equivalence_policy()
    (root / "equivalence_policy.json").write_text(
        json.dumps(to_jsonable(policy), indent=2, sort_keys=True)
    )
    shard_reports: tuple[dict[str, object], ...] = ()
    shard_equivalence: list[dict[str, object]] = []
    if args.native_jobs > 1:
        whole = NativeBatchReport.from_payload(native_report)
        if "native_reference_report_path" in provenance:
            shard_reports, shard_equivalence = _reuse_native_shard_reports(
                reference_case,
                native_report=native_report,
                provenance=provenance,
                policy=policy,
            )
        else:
            requests = _native_shard_requests(whole, args.native_jobs)
            request_paths = []
            for request in requests:
                request_path = Path(request.report_path).with_name(
                    f"request_{request.start_barrier_job_index}.json"
                )
                request_path.parent.mkdir(parents=True, exist_ok=True)
                request_path.write_text(json.dumps(asdict(request), indent=2))
                request_paths.append(request_path)
            with ThreadPoolExecutor(max_workers=args.native_jobs) as executor:
                shard_reports = tuple(
                    executor.map(
                        lambda item: _invoke_native_worker(
                            native_python=native_python,
                            worker_script=native_worker,
                            request_path=item[1],
                            evidence_prefix=root / "native_shards" / str(item[0]),
                            project_root=project_root,
                            repetitions=args.repetitions,
                            timeout_seconds=native_request.timeout_seconds,
                        ),
                        enumerate(request_paths),
                    )
                )
            _validate_native_shard_reports(whole, shard_reports, args.native_jobs)
            shard_equivalence = _native_shard_equivalence(
                whole, shard_reports, policy=policy
            )
        (root / "native_shards").mkdir(parents=True, exist_ok=True)
        (root / "native_shards" / "reports.json").write_text(
            json.dumps(shard_reports, indent=2)
        )
        (root / "native_shards" / "equivalence.json").write_text(
            json.dumps(shard_equivalence, indent=2)
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
    client.progress_callback = timing_observer
    observations = []
    for repetition in range(-1, args.repetitions):
        axis_events.clear()
        progress_events.clear()
        print(f"OpenHCS batch {repetition} starting.", flush=True)
        export_scope = ZMQRuntimeObservationExportScope.OUTCOMES
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
                run_id=f"{case.name}-{repetition}",
                pipeline_name=case.name,
                tool="OpenHCS",
            ),
            timing_observer=timing_observer,
            expected_axis_count=well_count,
            require_owned_server=True,
        )
        if args.production_source_root is not None and (
            Path(completed.endpoint_provenance.client_openhcs_file)
            .resolve()
            .parent.parent
            != production_root
        ):
            raise RuntimeError(
                "Execution receipt OpenHCS source differs from production root."
            )
        retained_evidence = inspect_measured_pipeline_run(evidence_dir)
        if not retained_evidence.retained_evidence_valid:
            raise RuntimeError(
                "Measured OpenHCS evidence failed retained-file inspection: "
                f"{retained_evidence.warnings!r}"
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
            expected_axes=well_count,
            expected_workers=args.openhcs_workers,
        )
        _write_progress_diagnostics(
            evidence_dir,
            case_name=case.name,
            worker_count=args.openhcs_workers,
            well_count=well_count,
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
        owned_exports = observation.exports
        candidate_exports = (
            owned_exports
            if owned_exports is not None
            else RuntimeExportObservation.from_output_roots(completed.output_roots)
        )
        native_root = Path(native_report["observations"][repetition + 1]["output_root"])
        declared_output_files = (
            frozenset(Path(path) for path in owned_exports.output_files)
            if owned_exports is not None
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
        managed_output_files = frozenset(
            path
            for output_root in completed.output_roots
            for path in METADATA_CONFIG.managed_paths(output_root)
        )
        image_set_policy = SourceImageSetIdentityPolicy.from_pipeline_config(
            pipeline_config
        )
        if args.repeat_assignments is None:
            comparisons = (
                _saved_output_equivalence(
                    native_root,
                    candidate_exports,
                    policy=policy,
                    native_measurement_cache_root=args.native_measurement_cache_root,
                    native_reference_report_sha256=provenance.get("native_reference_report_sha256"),
                    production_source_commit=source_commit,
                    source_workspaces=completed.output_roots,
                    image_set_policy=image_set_policy,
                    actual_candidate_files=actual_output_files,
                    candidate_managed_files=managed_output_files,
                ),
            )
        else:
            assignment_exports = tuple(
                candidate_exports.for_execution_axis(well) for well in wells
            )
            if frozenset(
                path for exports in assignment_exports for path in exports.output_files
            ) != frozenset(candidate_exports.output_files):
                raise RuntimeError(
                    "Assignment comparison does not cover every declared output file."
                )
            comparison_tasks = tuple(
                partial(
                    _saved_output_equivalence,
                    native_root / directory,
                    exports,
                    policy=policy,
                    native_measurement_cache_root=args.native_measurement_cache_root,
                    native_reference_report_sha256=provenance.get("native_reference_report_sha256"),
                    production_source_commit=source_commit,
                    source_workspaces=completed.output_roots,
                    image_set_policy=image_set_policy,
                    execution_axis_id=well,
                )
                for well, directory, exports in zip(
                    wells,
                    native_comparison_directories,
                    assignment_exports,
                    strict=True,
                )
            )
            if args.comparison_workers == 1:
                comparisons = tuple(task() for task in comparison_tasks)
            else:
                with ProcessPoolExecutor(
                    max_workers=args.comparison_workers,
                    mp_context=get_context("fork"),
                    initializer=os.sched_setaffinity,
                    initargs=(0, set(args.comparison_cpus)),
                ) as executor:
                    comparisons = tuple(executor.map(operator.call, comparison_tasks))

        database_report = RuntimeEquivalenceReport(
            tuple(
                difference
                for comparison in comparisons
                for difference in comparison[0].differences
            ),
            frozenset(
                path
                for comparison in comparisons
                for path in comparison[0].compared_output_files
            ),
        )
        csv_report = RuntimeEquivalenceReport(
            tuple(
                difference
                for comparison in comparisons
                for difference in comparison[1].differences
            ),
        )
        image_differences = tuple(
            difference for comparison in comparisons for difference in comparison[2]
        )
        native_image_count = sum(comparison[4] for comparison in comparisons)
        candidate_image_count = sum(comparison[5] for comparison in comparisons)
        native_exports = RuntimeExportObservation.from_output_roots((native_root,))
        phase_seconds = PhaseTimingRecord.seconds_by_phase(
            completed.receipt.phase_timings
        )
        result = {
            "repetition": repetition,
            "execution_id": completed.execution_id,
            "compile_artifact_id": completed.receipt.compile_artifact_id,
            "endpoint_pid": completed.endpoint_provenance.endpoint_pid,
            "axis_count": completed.axis_count,
            "observation_scope": export_scope.value,
            "assignment_scope": provenance["assignment_scope"],
            "compared_assignments": (
                wells if args.repeat_assignments is not None else ()
            ),
            "native_assignment_correspondence": (
                tuple(
                    {
                        "candidate_assignment": well,
                        "observed_reference_directory": directory,
                    }
                    for well, directory in zip(
                        wells, native_comparison_directories, strict=True
                    )
                )
                if args.repeat_assignments is not None
                else ()
            ),
            **worker_evidence,
            "server_job_started_at_epoch_seconds": record.start_time,
            "first_axis_started_at_epoch_seconds": first_axis_started_at,
            "server_job_completed_at_epoch_seconds": record.end_time,
            "server_job_seconds": server_job_seconds,
            "execution_seconds": phase_seconds[BenchmarkPhase.EXECUTE_OPENHCS.name],
            "compile_seconds": phase_seconds[BenchmarkPhase.COMPILE_OPENHCS.name],
            "total_seconds": additive_phase_total_seconds(phase_seconds),
            "first_axis_through_server_completion_seconds": (
                record.end_time - first_axis_started_at
            ),
            "native_image_count": native_image_count,
            "candidate_image_count": candidate_image_count,
            "native_physical_image_count": len(native_exports.image_outputs),
            "candidate_physical_image_count": len(candidate_exports.image_outputs),
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
                    for path in sorted(
                        actual_output_files
                        - declared_output_files
                        - managed_output_files
                    )
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
            "csv_differences": tuple(
                str(difference) for difference in csv_report.differences
            ),
            "image_differences": tuple(
                str(difference) for difference in image_differences
            ),
            "receipt_path": str(evidence_dir / "measured_pipeline_receipt.json"),
        }
        observations.append(result)
        (root / "candidate_report.json").write_text(json.dumps(observations, indent=2))
        print(
            f"OpenHCS batch {repetition}: {completed.axis_count} axes, "
            f"{len(result['database_differences'])} database and "
            f"{len(csv_report.differences)} CSV and "
            f"{len(result['image_differences'])} image differences.",
            flush=True,
        )
        if (
            not native_output_files
            or not actual_output_files
            or (
                declared_output_files is not None
                and len(declared_output_files - managed_output_files)
                != len(actual_output_files - managed_output_files)
            )
            or result["unexpected_output_files"]
            or result["missing_declared_output_files"]
            or result["database_differences"]
            or csv_report.differences
            or result["image_differences"]
        ):
            raise RuntimeError(
                f"Matched output equivalence failed in repetition {repetition}: "
                f"{result}"
            )

    final_input_inventory = _source_input_inventory(native_domain.source_universe)
    if final_input_inventory != provenance["native_input_inventory"]:
        raise RuntimeError("Native source images or metadata changed during pilot.")
    _require_native_reference_unchanged(provenance)
    if args.production_source_root is not None and (
        subprocess.check_output(
            ("git", "rev-parse", "HEAD"), cwd=production_root, text=True
        ).strip()
        != source_commit
        or subprocess.check_output(
            ("git", "status", "--porcelain"), cwd=production_root, text=True
        ).strip()
    ):
        raise RuntimeError("Production source changed during candidate capture.")
    if harness_inventory != {
        str(path.relative_to(project_root)): sha256_file(path)
        for path in sorted((project_root / "benchmark").rglob("*.py"))
    }:
        raise RuntimeError("Benchmark harness changed during candidate capture.")
    provenance["native_input_inventory_after"] = final_input_inventory
    (root / "pilot_provenance.json").write_text(json.dumps(provenance, indent=2))

    report = {
        **provenance,
        "native": native_report,
        "native_shards": shard_reports,
        "native_shard_equivalence": shard_equivalence,
        "candidate": observations,
        "native_execution_projection": projection_inputs,
        "timing_claim": (
            "Observed complete selected batches: native pipeline-start through post-run "
            "and full invocation are separate; OpenHCS worker execution and complete "
            "client operation are separate. Repeated assignments are independently "
            "executed source copies, not additional genuine wells."
            + (
                " Candidate-only execution uses observed repeated-source native outputs "
                "at their original cardinality; separate projection inputs do not "
                "claim newly observed native executions. Any declared timing model "
                "is separate from the unchanged native observations."
                if args.candidate_only
                else " Native execution timings are observed."
            )
            + (
                " Native timings and output roots were reused from genuine retained "
                "observations; their original source and report SHA are recorded separately."
                if "native_reference_report_path" in provenance
                else ""
            )
        ),
    }
    (root / "report.json").write_text(json.dumps(report, indent=2))
    print(json.dumps({"output_dir": str(root), "candidate": observations}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
