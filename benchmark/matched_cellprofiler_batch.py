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
from dataclasses import replace
from pathlib import Path

from objectstate.lazy_factory import (
    ensure_global_config_context,
    rebuild_lazy_config_with_new_global_reference,
)
from zmqruntime import DataControlPortPairAuthority

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
)
from benchmark.openhcs_measured_run import (
    _ZMQProgressTimingObserver,
    execute_measured_openhcs_pipeline_on_client,
)
from benchmark.timing import PhaseTimingTrace
from openhcs.constants.constants import AllComponents
from openhcs.core.config import (
    AnalysisConsolidationConfig,
    GlobalPipelineConfig,
    LazyPathPlanningConfig,
    LazyWellFilterConfig,
    MaterializationBackend,
    PathPlanningConfig,
    VFSConfig,
    WellFilterConfig,
)
from openhcs.core.equivalence.comparison import runtime_image_differences
from openhcs.core.equivalence.outputs import RuntimeOutputSnapshot
from openhcs.core.input_workspace import InputWorkspacePreparationRequest
from openhcs.core.pipeline_document import PipelineDocumentAuthority
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.interop.cellprofiler.plate_workspace import (
    prepare_cellprofiler_input_workspace,
)
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG
from openhcs.runtime.zmq_execution_client import (
    OpenHCSExecutionSubmission,
    ZMQExecutionClient,
)
from openhcs.runtime.zmq_execution_signature import ZMQAuxiliaryExecutionParams
from openhcs.serialization.json import to_jsonable

CASE_NAME = "cp_tutorial_translocation_final"
WELL_COUNT = 8


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--repetitions", type=int, default=1)
    parser.add_argument("--native-python", type=Path, required=True)
    return parser


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _output_inventory(root: Path, files: frozenset[Path]) -> tuple[dict[str, str], ...]:
    return tuple(
        {"path": str(path.relative_to(root)), "sha256": _sha256(path)}
        for path in sorted(files)
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


def _global_config(output_dir: Path, wells: tuple[str, ...]) -> GlobalPipelineConfig:
    return GlobalPipelineConfig(
        num_workers=1,
        use_threading=False,
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


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.repetitions < 1:
        raise ValueError("At least one observed repetition is required.")
    root = args.output_dir.expanduser().resolve()
    if root.exists() and any(root.iterdir()):
        raise FileExistsError(f"Matched pilot output directory must be empty: {root}")
    root.mkdir(parents=True, exist_ok=True)
    project_root = Path(__file__).resolve().parent.parent
    manifest = args.manifest.expanduser().resolve()
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
    native_global_config = _global_config(root / "native", wells)
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
    native_process = subprocess.run(
        (
            str(_native_python_executable(args.native_python, project_root)),
            str(project_root / "benchmark/native_cellprofiler_batch_worker.py"),
            str(native_request_path),
        ),
        cwd=project_root,
        env=os.environ.copy(),
        capture_output=True,
        text=True,
        timeout=900 * (args.repetitions + 1),
        check=False,
    )
    (root / "native_stdout.log").write_text(native_process.stdout)
    (root / "native_stderr.log").write_text(native_process.stderr)
    native_process.check_returncode()
    native_report = json.loads(native_process.stdout.splitlines()[-1])
    (root / "native_report.json").write_text(json.dumps(native_report, indent=2))
    print("Native warm-up and observed batches complete.", flush=True)

    policy = _strict_cellprofiler_runtime_equivalence_policy()
    (root / "equivalence_policy.json").write_text(
        json.dumps(to_jsonable(policy), indent=2, sort_keys=True)
    )
    timing_observer = _ZMQProgressTimingObserver()
    port = DataControlPortPairAuthority.acquire(
        OPENHCS_ZMQ_CONFIG,
        transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode,
    ).data_port
    observations = []
    with ZMQExecutionClient(
        port=port, persistent=False, progress_callback=timing_observer
    ) as client:
        for repetition in range(-1, args.repetitions):
            print(f"OpenHCS batch {repetition} starting.", flush=True)
            evidence_dir = root / "candidate_evidence" / str(repetition)
            output_dir = root / "candidate" / str(repetition)
            global_config = _global_config(output_dir, wells)
            ensure_global_config_context(GlobalPipelineConfig, global_config)
            pipeline_config = replace(
                prepared.pipeline_config,
                materialize_runtime_artifacts=False,
                well_filter_config=LazyWellFilterConfig(well_filter=list(wells)),
                path_planning_config=LazyPathPlanningConfig(
                    well_filter=0,
                    global_output_folder=output_dir,
                    output_dir_suffix="_matched_pilot",
                ),
            )
            pipeline_config = rebuild_lazy_config_with_new_global_reference(
                pipeline_config, global_config, GlobalPipelineConfig
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
                    runtime_observation_export_path=(evidence_dir / "observation.pkl")
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
            observation = completed.observation_export
            native_root = root / "native" / str(repetition)
            database_report = cellprofiler_database_export_equivalence(
                native_root, observation.exports, policy=policy
            )
            native_images = RuntimeOutputSnapshot.from_output_root(native_root).images
            candidate_images = RuntimeOutputSnapshot.from_export_observation(
                observation.exports
            ).images
            image_differences = runtime_image_differences(
                native_images, candidate_images, policy
            )
            declared_output_files = frozenset(
                Path(path) for path in observation.exports.output_files
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
                "native_image_count": len(native_images),
                "candidate_image_count": len(candidate_images),
                "native_output_file_count": len(native_output_files),
                "candidate_output_file_count": len(actual_output_files),
                "declared_output_file_count": len(declared_output_files),
                "native_output_inventory": _output_inventory(
                    native_root, native_output_files
                ),
                "candidate_output_inventory": _output_inventory(
                    output_dir, actual_output_files
                ),
                "unexpected_output_files": tuple(
                    str(path)
                    for path in sorted(actual_output_files - declared_output_files)
                ),
                "missing_declared_output_files": tuple(
                    str(path)
                    for path in sorted(declared_output_files - actual_output_files)
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
                or result["unexpected_output_files"]
                or result["missing_declared_output_files"]
                or result["database_differences"]
                or result["image_differences"]
            ):
                raise RuntimeError(
                    f"Matched output equivalence failed in repetition {repetition}: "
                    f"{result}"
                )

    report = {
        **provenance,
        "native": native_report,
        "candidate": observations,
        "timing_claim": "none: boundary and concurrency matching remain under review",
    }
    (root / "report.json").write_text(json.dumps(report, indent=2))
    print(json.dumps({"output_dir": str(root), "candidate": observations}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
