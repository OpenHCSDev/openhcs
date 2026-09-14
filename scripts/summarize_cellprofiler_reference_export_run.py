#!/usr/bin/env python3
"""Write file-level receipts for a dated CellProfiler reference-export run."""

from __future__ import annotations

import argparse
import csv
import json
from pathlib import Path

from benchmark.cellprofiler_reference_exports import (
    CellProfilerReferenceExportPlan,
)

FIELDNAMES = (
    "suite_id",
    "case_name",
    "suite_case_equivalent",
    "suite_difference_count",
    "artifact_name",
    "output_filename",
    "semantic_kind",
    "comparison_contract",
    "reference_shape",
    "candidate_shape",
    "reference_dtype",
    "candidate_dtype",
    "reference_pixel_digest",
    "candidate_pixel_digest",
    "compared_pixel_count",
    "different_pixel_count",
    "out_of_tolerance_pixel_count",
    "max_abs_difference",
    "artifact_equivalent",
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-root", type=Path, required=True)
    parser.add_argument("--pipeline-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    rows = comparison_rows(args.run_root, args.pipeline_root)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=FIELDNAMES)
        writer.writeheader()
        writer.writerows(rows)
    print(f"artifact_comparisons={len(rows)}")
    print(f"equivalent_artifacts={sum(row['artifact_equivalent'] for row in rows)}")
    print(f"output={args.output}")
    return 0


def comparison_rows(
    run_root: Path, pipeline_root: Path
) -> tuple[dict[str, object], ...]:
    """Return declared file-level receipts for every observation in one suite."""

    observations_path = Path(run_root) / "observations.jsonl"
    observations = tuple(
        json.loads(line)
        for line in observations_path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    )
    rows: list[dict[str, object]] = []
    for observation in observations:
        case_name = str(observation["case_name"])
        native_summary = observation.get("native_cellprofiler") or {}
        candidate_summary = observation.get("openhcs") or {}
        native_output_path = native_summary.get("output_path")
        candidate_output_path = candidate_summary.get("output_path")
        if not native_output_path or not candidate_output_path:
            raise ValueError(
                f"{case_name}: comparison receipts require non-empty native and "
                f"candidate output paths; native_error="
                f"{native_summary.get('error_message')!r}, candidate_error="
                f"{candidate_summary.get('error_message')!r}."
            )
        plan = CellProfilerReferenceExportPlan.from_sidecar(
            Path(pipeline_root) / f"{case_name}.reference_exports.json"
        )
        plan.validate_generated_pipeline(Path(pipeline_root) / f"{case_name}.cppipe")
        native_root = Path(native_output_path)
        candidate_root = Path(candidate_output_path) / "images_results"
        marker = json.loads(
            (native_root / ".cellprofiler_benchmark_reference.json").read_text(
                encoding="utf-8"
            )
        )
        marker_image_count = int(marker["provenance"]["image_output_count"])
        if marker_image_count != len(plan.artifacts):
            raise ValueError(
                f"{case_name}: native marker image count {marker_image_count} "
                f"does not match declared artifacts {len(plan.artifacts)}."
            )

        for comparison in plan.compare_output_roots(native_root, candidate_root):
            artifact = comparison.artifact
            rows.append(
                {
                    "suite_id": observation["suite_id"],
                    "case_name": case_name,
                    "suite_case_equivalent": observation["equivalent"],
                    "suite_difference_count": observation["difference_count"],
                    "artifact_name": artifact.artifact_name,
                    "output_filename": artifact.output_filename,
                    "semantic_kind": artifact.semantic_kind.value,
                    "comparison_contract": artifact.comparison,
                    "reference_shape": json.dumps(comparison.reference_shape),
                    "candidate_shape": json.dumps(comparison.candidate_shape),
                    "reference_dtype": comparison.reference_dtype,
                    "candidate_dtype": comparison.candidate_dtype,
                    "reference_pixel_digest": comparison.reference_pixel_digest,
                    "candidate_pixel_digest": comparison.candidate_pixel_digest,
                    "compared_pixel_count": comparison.compared_pixel_count,
                    "different_pixel_count": comparison.different_pixel_count,
                    "out_of_tolerance_pixel_count": (
                        comparison.out_of_tolerance_pixel_count
                    ),
                    "max_abs_difference": comparison.max_abs_difference,
                    "artifact_equivalent": comparison.equivalent,
                }
            )
    return tuple(rows)


if __name__ == "__main__":
    raise SystemExit(main())
