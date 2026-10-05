"""Measure native CellProfiler throughput on replicated, byte-identical wells.

The source-binding workspace declares the input universe. Each synthetic well
contains symlinks to that universe; the native batch worker owns execution and
timing. This measures concurrent native jobs rather than projecting one well.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

from benchmark.adapters.cellprofiler import (
    EmbeddedImagePlaneNativeCellProfilerInputDomainStrategy,
    HeadlessCellProfilerPipelinePolicy,
)
from benchmark.cellprofiler_comparison import load_comparison_cases
from benchmark.file_digest import sha256_file
from benchmark.matched_cellprofiler_batch import (
    _invoke_native_worker,
    _native_python_executable,
)
from benchmark.well_throughput_scaling import _synthetic_well_ids
from openhcs.constants.constants import AllComponents
from openhcs.core.input_workspace import InputWorkspacePreparationRequest
from openhcs.core.source_matching import source_component_metadata_value
from openhcs.interop.cellprofiler.plate_workspace import (
    prepare_cellprofiler_input_workspace,
)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--case", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--native-python", type=Path, required=True)
    parser.add_argument("--wells", type=int, default=16)
    parser.add_argument("--native-jobs", type=int, default=4)
    parser.add_argument("--image-sets-per-well", type=int, required=True)
    parser.add_argument("--repetitions", type=int, default=1)
    return parser


def _source_paths(plane_mappings: dict[str, Any]) -> tuple[Path, ...]:
    """Resolve the declared disk planes without scanning unrelated files."""

    paths = []
    for mapping in plane_mappings.values():
        if mapping.get("backend") != "disk":
            raise ValueError("Native synthetic wells require disk source planes.")
        path = Path(str(mapping["backend_address"])).resolve(strict=True)
        if not path.is_file():
            raise ValueError(f"Declared source plane is not a file: {path}")
        paths.append(path)
    unique_paths = tuple(sorted(set(paths)))
    if not unique_paths:
        raise ValueError("Source bindings declare no disk image planes.")
    basenames = tuple(path.name for path in unique_paths)
    if len(set(basenames)) != len(unique_paths):
        raise ValueError("Native synthetic staging needs unique source basenames.")
    return unique_paths


def _stage_wells(
    source_paths: tuple[Path, ...], input_dir: Path, well_ids: tuple[str, ...]
) -> tuple[dict[str, object], ...]:
    """Create deterministic image identities while retaining the source bytes."""

    input_dir.mkdir(parents=True, exist_ok=False)
    inventory = []
    for well in well_ids:
        well_dir = input_dir / well
        well_dir.mkdir()
        for source in source_paths:
            staged = well_dir / source.name
            staged.symlink_to(source)
            inventory.append(
                {
                    "well": well,
                    "path": str(staged.relative_to(input_dir)),
                    "source_path": str(source),
                    "size_bytes": source.stat().st_size,
                    "sha256": sha256_file(source),
                }
            )
    return tuple(inventory)


def _concurrent_timing(
    reports: tuple[dict[str, Any], ...], repetition: int
) -> dict[str, float | int]:
    observations = tuple(
        next(
            observation
            for observation in report["observations"]
            if observation["repetition"] == repetition
        )
        for report in reports
    )
    invocations = tuple(
        observation["invocation_started_monotonic_seconds"]
        for observation in observations
    )
    starts = tuple(
        observation["pipeline_started_monotonic_seconds"]
        for observation in observations
    )
    completions = tuple(
        observation["completed_monotonic_seconds"] for observation in observations
    )
    if any(
        invocation > pipeline_start or pipeline_start > completed
        for invocation, pipeline_start, completed in zip(
            invocations, starts, completions, strict=True
        )
    ):
        raise RuntimeError("Native batch timing boundaries are out of order.")
    if len(reports) > 1 and min(completions) <= max(starts):
        raise RuntimeError("Native batch jobs did not overlap during analysis.")
    return {
        "repetition": repetition,
        "invocation_start_skew_seconds": max(invocations) - min(invocations),
        "invocation_through_completion_makespan_seconds": max(completions)
        - min(invocations),
        "pipeline_start_skew_seconds": max(starts) - min(starts),
        "pipeline_execution_makespan_seconds": max(completions)
        - min(starts),
        "pipeline_overlap_seconds": min(completions) - max(starts),
    }


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if (
        args.wells < 1
        or args.native_jobs < 1
        or args.repetitions < 1
        or args.image_sets_per_well < 1
        or args.wells % args.native_jobs
    ):
        raise ValueError("Positive counts must partition wells evenly among jobs.")
    project_root = Path(__file__).resolve().parent.parent
    root = args.output_dir.expanduser().resolve()
    root.mkdir(parents=True, exist_ok=False)
    manifest = args.manifest.expanduser().resolve(strict=True)
    matches = tuple(
        case for case in load_comparison_cases(manifest) if case.name == args.case
    )
    if len(matches) != 1:
        raise ValueError(f"Expected one manifest case named {args.case!r}.")
    (case,) = matches
    prepared = prepare_cellprofiler_input_workspace(
        InputWorkspacePreparationRequest(
            selected_path=case.dataset_path,
            selected_pipeline_path=case.cppipe_path,
            workspace_root=root / "source_workspace",
            generated_source_path=root / "imported_pipeline.py",
        )
    )
    if prepared.pipeline_import_error is not None:
        raise RuntimeError(str(prepared.pipeline_import_error))
    if prepared.materialization is None:
        raise RuntimeError("Pipeline import has no declared source-binding planes.")
    source_wells = {
        source_component_metadata_value(metadata, AllComponents.WELL)
        for metadata in prepared.materialization.source_metadata.values()
    }
    if len(source_wells) != 1 or None in source_wells or "" in source_wells:
        raise ValueError(
            "Synthetic native scaling requires exactly one declared source well; "
            f"found {source_wells!r}."
        )
    source_paths = _source_paths(prepared.materialization.plane_mappings)
    well_ids = _synthetic_well_ids(args.wells)
    input_dir = root / "inputs"
    inventory = _stage_wells(source_paths, input_dir, well_ids)
    staged_paths = tuple(input_dir / row["path"] for row in inventory)
    file_list_path = root / "file_list.txt"
    file_list_path.write_text(
        "\n".join(
            EmbeddedImagePlaneNativeCellProfilerInputDomainStrategy.file_uri(path)
            for path in staged_paths
        )
        + "\n"
    )
    pipeline_path = HeadlessCellProfilerPipelinePolicy.execution_path(
        case.cppipe_path, root / "pipeline_preparation"
    )
    source_commit = subprocess.check_output(
        ("git", "rev-parse", "HEAD"), cwd=project_root, text=True
    ).strip()
    provenance = {
        "case": case.name,
        "source_well": next(iter(source_wells)),
        "synthetic_wells": well_ids,
        "source_inventory": inventory,
        "manifest_sha256": sha256_file(manifest),
        "cppipe_sha256": sha256_file(case.cppipe_path),
        "driver_sha256": sha256_file(Path(__file__)),
        "native_worker_sha256": sha256_file(
            project_root / "benchmark/native_cellprofiler_batch_worker.py"
        ),
        "source_commit": source_commit,
        "source_dirty": bool(
            subprocess.check_output(
                ("git", "status", "--porcelain"), cwd=project_root, text=True
            ).strip()
        ),
        "native_jobs": args.native_jobs,
        "image_sets_per_well": args.image_sets_per_well,
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
                "JAVA_HOME",
            )
        },
    }
    (root / "provenance.json").write_text(json.dumps(provenance, indent=2))
    native_python = _native_python_executable(args.native_python, project_root)
    worker_script = project_root / "benchmark/native_cellprofiler_batch_worker.py"
    image_sets_per_job = args.image_sets_per_well * args.wells // args.native_jobs
    request_paths = []
    for index in range(args.native_jobs):
        request = {
            "pipeline_path": str(pipeline_path),
            "input_dir": str(input_dir),
            "file_list_path": str(file_list_path),
            "output_root": str(root / "native_jobs" / str(index)),
            "expected_image_sets": image_sets_per_job,
            "first_image_set": index * image_sets_per_job + 1,
            "last_image_set": (index + 1) * image_sets_per_job,
            "repetitions": args.repetitions,
        }
        if args.native_jobs > 1:
            request.update(
                {
                    "start_barrier_root": str(root / "native_jobs" / "start_barrier"),
                    "start_barrier_job_count": args.native_jobs,
                    "start_barrier_job_index": index,
                }
            )
        request_path = root / "native_jobs" / f"request_{index}.json"
        request_path.parent.mkdir(parents=True, exist_ok=True)
        request_path.write_text(json.dumps(request, indent=2))
        request_paths.append(request_path)
    print(
        f"Staged {args.wells} wells, {len(inventory)} source links; "
        f"running {args.native_jobs} native jobs.",
        flush=True,
    )
    with ThreadPoolExecutor(max_workers=args.native_jobs) as executor:
        reports = tuple(
            executor.map(
                lambda item: _invoke_native_worker(
                    native_python=native_python,
                    worker_script=worker_script,
                    request_path=item[1],
                    evidence_prefix=root / "native_jobs" / str(item[0]),
                    project_root=project_root,
                    repetitions=args.repetitions,
                ),
                enumerate(request_paths),
            )
        )
    for report in reports:
        if any(
            observation["image_set_count"] != image_sets_per_job
            for observation in report["observations"]
        ):
            raise RuntimeError("Native worker observed the wrong image-set count.")
    timing = tuple(
        _concurrent_timing(reports, repetition)
        for repetition in range(-1, args.repetitions)
    )
    summary = {
        "case": case.name,
        "wells": args.wells,
        "native_jobs": args.native_jobs,
        "image_sets_per_well": args.image_sets_per_well,
        "total_image_sets": args.wells * args.image_sets_per_well,
        "timing": timing,
        "reports": reports,
    }
    (root / "summary.json").write_text(json.dumps(summary, indent=2))
    print(
        json.dumps({key: value for key, value in summary.items() if key != "reports"})
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
