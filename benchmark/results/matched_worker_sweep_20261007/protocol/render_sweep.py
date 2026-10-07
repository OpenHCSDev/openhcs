"""Render qualified issue 1100 records through existing measured/May owners.

Run the archived script only after every declared mode qualifies. No timings are
projected and no production plotting implementation is introduced.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import sys
from dataclasses import asdict, replace
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--protocol-manifest", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    record = args.record.resolve()
    root = record.parents[2]
    sys.path.insert(0, str(root))
    sys.path.insert(0, str(root / "paper/figures"))
    import build_slas_agent
    import build_slas_benchmark
    from benchmark.reports import cppipe_figures
    from benchmark.reports.cppipe_figures import FIGURE_STYLE, MeasuredBatchSummarySource

    declaration = json.loads(args.protocol_manifest.read_text())
    modes = declaration["modes"]
    may = sorted((mode for mode in modes if
                  (mode["assignments"] == mode["openhcs_workers"] == 1)
                  or (mode["openhcs_workers"] > 1
                      and mode["assignments"] == 4 * mode["openhcs_workers"])),
                 key=lambda mode: mode["openhcs_workers"])
    fixed_assignments = math.lcm(*(mode["openhcs_workers"] for mode in may))
    fixed_name = f"fixed{fixed_assignments}"
    fixed = sorted((mode for mode in modes if mode["assignments"] == fixed_assignments),
                   key=lambda mode: mode["openhcs_workers"])
    if ([mode["openhcs_workers"] for mode in may] != [1, 2, 3, 4]
            or [mode["openhcs_workers"] for mode in fixed] != [1, 2, 3, 4]
            or len(modes) != 7):
        raise ValueError("Prepared protocol must own the complete May and evenly balanced fixed-workload schedule")
    if any(mode["native_processes"] != 1 for mode in modes):
        raise ValueError("Primary sweep requires actual one-process stock CellProfiler")

    code_inputs = (Path(__file__).resolve(), args.protocol_manifest.resolve(),
                   Path(cppipe_figures.__file__), Path(build_slas_benchmark.__file__),
                   Path(build_slas_agent.__file__))
    if any(not path.resolve().is_relative_to(root) for path in code_inputs):
        raise ValueError("Archive the protocol script/manifest in the record before rendering")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for scope in ("execution", "total"):
        sources, tables, inputs = {}, {}, list(code_inputs)
        cohort = None
        for mode in modes:
            label = (f"{mode['openhcs_workers']} worker"
                     f"{'s' if mode['openhcs_workers'] != 1 else ''} / "
                     f"{mode['assignments']} assignment"
                     f"{'s' if mode['assignments'] != 1 else ''}")
            source = MeasuredBatchSummarySource(label,
                       record / "data" / mode["archive_mode"] / f"{scope}_summary.csv")
            custody = source.qualified_custody()
            if custody["source_head"] != declaration["source_revision"] or source.clock_scope != scope:
                raise ValueError("Summary source or qualified clock differs from prepared protocol")
            for case in custody["cases"]:
                actual = case["mode"]
                if (actual["candidate_worker_count"] != mode["openhcs_workers"]
                        or actual["native_job_count"] != 1
                        or len(actual["wells"]) != mode["assignments"]):
                    raise ValueError("Qualified case mode differs from declared schedule")
            with source.path.open(newline="", encoding="utf-8") as stream:
                rows = tuple(csv.DictReader(stream))
            table = {row["case_name"]: row for row in rows}
            declared_cases = {case["case"] for case in custody["cases"]}
            if len(rows) != len(table) or len(table) != 30 or set(table) != declared_cases:
                raise ValueError("Every mode must retain exactly thirty real workflow rows")
            if cohort is None:
                cohort = set(table)
            if set(table) != cohort:
                raise ValueError("Modes cannot pool different workflow cohorts")
            sources[mode["archive_mode"]], tables[mode["archive_mode"]] = source, table
            inputs.extend((source.path, source.custody_path, source.retained_manifest_path()))

        # Fixed-workload ratios require identical assignment roles, not merely
        # the same cardinality or pipeline name.
        fixed_reference = {
            case["case"]: case["mode"]
            for case in sources[fixed[0]["archive_mode"]].qualified_custody()["cases"]
        }
        for mode in fixed:
            if fixed_assignments % mode["openhcs_workers"]:
                raise ValueError("Fixed workload must divide evenly across each worker count")
            for case in sources[mode["archive_mode"]].qualified_custody()["cases"]:
                for field in ("wells", "selected_source_wells", "assignment_scope"):
                    if case["mode"][field] != fixed_reference[case["case"]][field]:
                        raise ValueError(f"{fixed_name} assignment role differs: {field}")

        for schedule_name, schedule in (("may", may), (fixed_name, fixed)):
            destination = args.output_dir / schedule_name / scope
            selected = tuple(sources[mode["archive_mode"]] for mode in schedule)
            build_slas_benchmark.build_measured(
                tuple(f"{source.label}={source.path}" for source in selected),
                scope, destination)
            rows = tuple(source.metric_rows(name, row, category_row=row)[1]
                         for source in selected
                         for name, row in tables[source.path.parent.name].items())
            outputs = FIGURE_STYLE.generate_average_point_figures(
                rows, methods=tuple(source.candidate_method for source in selected),
                output_dir=destination, output_formats=("png", "svg"),
                filename_stem=f"{schedule_name}_{scope}_mean_workflow_points",
                title=f"Matched thirty-workflow {schedule_name} {scope} speedups",
                ylabel="Stock CellProfiler / OpenHCS speedup", value_key="speedup",
                target_line=1, log_variant=True)
            build_slas_benchmark.write_provenance(
                destination, tuple(dict.fromkeys(inputs)),
                tuple(dict.fromkeys((*outputs, *destination.glob("measured_*"),
                                    *destination.glob("qualified_*")))),
                {"interpretation": "Actual serial stock CellProfiler denominator; independent engine medians; thirty workflow dots, arithmetic mean bars and median lines. Changing May workloads are not fixed-workload parallel efficiency.",
                 "scope": scope, "source_revision": declaration["source_revision"],
                 "memory": "Unavailable; no historical substitution"})

        reference_source = sources[fixed[0]["archive_mode"]]
        reference = {name: reference_source.metric_rows(name, row, category_row=row)[1]
                     for name, row in tables[fixed[0]["archive_mode"]].items()}
        for metric in ("scaling", "efficiency"):
            destination = args.output_dir / fixed_name / scope / metric
            destination.mkdir(parents=True, exist_ok=True)
            rows, methods = [], []
            for mode in fixed:
                source = sources[mode["archive_mode"]]
                methods.append(source.candidate_method)
                for name, row in tables[mode["archive_mode"]].items():
                    candidate = source.metric_rows(name, row, category_row=row)[1]
                    baseline_seconds, candidate_seconds = reference[name].raw_seconds, candidate.raw_seconds
                    if any(value is None or not math.isfinite(value) or value <= 0
                           for value in (baseline_seconds, candidate_seconds)):
                        raise ValueError("Fixed-workload scaling needs positive qualified durations")
                    value = baseline_seconds / candidate_seconds
                    if metric == "efficiency":
                        value /= mode["openhcs_workers"]
                    rows.append(replace(candidate, speedup=value))
            table_path = destination / "derived_workflow_metrics.csv"
            with table_path.open("w", newline="", encoding="utf-8") as stream:
                dictionaries = [asdict(row) for row in rows]
                if metric == "efficiency":
                    for values in dictionaries:
                        values["efficiency_unit_fraction"] = values.pop("speedup")
                writer = csv.DictWriter(stream, fieldnames=tuple(dictionaries[0]))
                writer.writeheader()
                writer.writerows(dictionaries)
            # Existing painter annotates ratios with x; efficiency stays an
            # explicitly named fraction CSV rather than a misleading x plot.
            outputs = () if metric == "efficiency" else FIGURE_STYLE.generate_average_point_figures(
                rows, methods=methods, output_dir=destination,
                output_formats=("png", "svg"), filename_stem=f"{fixed_name}_{scope}_{metric}",
                title=f"{fixed_assignments} assignments: OpenHCS {scope} {metric}",
                ylabel="OpenHCS one-worker / n-worker speedup",
                value_key="speedup", target_line=1, log_variant=True)
            build_slas_benchmark.write_provenance(
                destination, tuple(dict.fromkeys(inputs)), (table_path, *outputs),
                {"interpretation": "OpenHCS one-worker duration / n-worker duration on the identical evenly balanced assignments; efficiency divides this ratio by worker count. This is not CellProfiler-relative speedup.",
                 "scope": scope, "source_revision": declaration["source_revision"]})


if __name__ == "__main__":
    main()
