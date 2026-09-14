"""Generate benchmark-only CellProfiler terminal-artifact export pipelines."""

from __future__ import annotations

import argparse
from pathlib import Path

from benchmark.cellprofiler_comparison import load_comparison_cases
from benchmark.cellprofiler_reference_exports import CellProfilerReferenceExportPlan


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    parser.add_argument(
        "--case",
        action="append",
        required=True,
        dest="case_names",
        help="Exact source-manifest case to derive. Repeat for multiple cases.",
    )
    args = parser.parse_args()

    requested_names = tuple(dict.fromkeys(args.case_names))
    cases_by_name = {case.name: case for case in load_comparison_cases(args.manifest)}
    missing = tuple(name for name in requested_names if name not in cases_by_name)
    if missing:
        raise ValueError(f"Manifest has no requested cases: {missing!r}.")

    for case_name in requested_names:
        case = cases_by_name[case_name]
        plan = CellProfilerReferenceExportPlan.from_pipeline(
            case.cppipe_path,
            source_root=case.dataset_path,
        )
        output_path = args.output_dir / f"{case.name}.cppipe"
        plan.materialize(
            case.cppipe_path,
            output_path,
            provenance={
                "source_manifest": str(args.manifest),
                "source_case_name": case.name,
                "dataset_id": case.resolved_dataset_id,
            },
        )
        print(f"{case.name}\t{output_path}\t{len(plan.artifacts)} exports")


if __name__ == "__main__":
    main()
