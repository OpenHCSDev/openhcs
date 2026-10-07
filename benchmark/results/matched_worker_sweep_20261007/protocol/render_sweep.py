"""Render admitted first-use CP references and actual OpenHCS through May owners.

Measured CP1/CP8 and explicitly projected CP12/CP16 remain distinct. No native
observations, timing models, or plotting algorithms are implemented here.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import statistics
import sys
from dataclasses import asdict, replace
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--protocol-manifest", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--calibration-only", action="store_true")
    args = parser.parse_args()
    record = args.record.resolve()
    root = record.parents[2]
    sys.path.insert(0, str(root))
    sys.path.insert(0, str(root / "paper/figures"))
    import build_slas_agent
    import build_slas_benchmark
    from benchmark import native_batch_contracts, native_execution_projection
    from benchmark.native_batch_contracts import NativeBatchReport
    from benchmark.native_execution_projection import RepeatedSourceNativeBatchReport
    from benchmark.reports import cppipe_figures as figures

    declaration = json.loads(args.protocol_manifest.read_text())
    modes = declaration["modes"]
    may = sorted((mode for mode in modes if
                  mode["assignments"] == mode["openhcs_workers"] == 1
                  or mode["openhcs_workers"] > 1
                  and mode["assignments"] == 4 * mode["openhcs_workers"]),
                 key=lambda mode: mode["openhcs_workers"])
    fixed_count = math.lcm(*(mode["openhcs_workers"] for mode in may))
    fixed = sorted((mode for mode in modes if mode["assignments"] == fixed_count),
                   key=lambda mode: mode["openhcs_workers"])
    if (len(modes) != 7 or [m["openhcs_workers"] for m in may] != [1, 2, 3, 4]
            or [m["openhcs_workers"] for m in fixed] != [1, 2, 3, 4]):
        raise ValueError("Protocol must declare the complete May and balanced fixed workload")
    inputs = [Path(__file__).resolve(), args.protocol_manifest.resolve(),
              Path(figures.__file__), Path(build_slas_benchmark.__file__),
              Path(build_slas_agent.__file__), Path(native_execution_projection.__file__),
              Path(native_batch_contracts.__file__),
              record / "protocol/v2/convert_matched_reports.py",
              record / "calibration/cold_first/cold-first-model-validation.json",
              record / "calibration/cold_first/archive_custody.json"]
    modes_to_read = [mode for mode in modes if mode["assignments"] in (1, 8)] if args.calibration_only else modes
    sources, tables, cases, kinds, native_affinities = {}, {}, {}, {}, {}
    cohort, manifest_digest = None, None
    for mode in modes_to_read:
        name = mode["archive_mode"]
        custody_path = record / "data/first_use" / name / "summary_custody.json"
        custody = json.loads(custody_path.read_text())
        if custody["status"] != "PASS" or custody["source_head"] != declaration["source_revision"]:
            raise ValueError("First-use view must pass the converter on the declared source")
        manifest_path = record / "protocol" / name / Path(custody["manifest"]["path"]).name
        if hashlib.sha256(manifest_path.read_bytes()).hexdigest() != custody["manifest"]["sha256"]:
            raise ValueError("Retained manifest differs from qualified declaration")
        if manifest_digest is None:
            manifest_digest = custody["manifest"]["sha256"]
        if custody["manifest"]["sha256"] != manifest_digest:
            raise ValueError("Modes cannot mix pipeline declarations")
        cases[name] = {case["case"]: case for case in custody["cases"]}
        if len(cases[name]) != len(custody["cases"]) or len(cases[name]) != 30:
            raise ValueError("Each mode must contain thirty distinct workflow cases")
        mode_kinds, mode_affinities = set(), set()
        for case in cases[name].values():
            actual = case["mode"]
            if (actual["candidate_worker_count"] != mode["openhcs_workers"]
                    or len(actual["wells"]) != mode["assignments"]):
                raise ValueError("Qualified OpenHCS worker/assignment domain differs")
            reference = case["native_headline_reference"]
            kind = reference["kind"]
            if (kind not in ("measured_first_batch", "projected_first_batch")
                    or reference["source_fresh_repetition"] != -1
                    or reference["source_fresh_observation_count"] != 1
                    or reference["target_native_observation_count"] != (1 if kind == "measured_first_batch" else 0)):
                raise ValueError("Native headline must distinguish genuine first observation from projection")
            native_path = record / "reports" / name / case["case"] / "native_report.json"
            if hashlib.sha256(native_path.read_bytes()).hexdigest() != reference["source_report_sha256"]:
                raise ValueError("Archived native anchor differs from headline source")
            payload = json.loads(native_path.read_text())
            mode_affinities.add(tuple(payload["environment"]["cpu_affinity"]))
            native = NativeBatchReport.from_payload(payload)
            native.require_complete(3)
            fresh = native.observations[0]
            if fresh.repetition != -1 or tuple(row.repetition for row in native.observations[1:]) != (0, 1, 2):
                raise ValueError("Native source must retain one fresh and three genuine warm observations")
            if kind == "projected_first_batch":
                projection = case["native_execution_projection"]
                expected = RepeatedSourceNativeBatchReport.from_payload(payload).projected_fresh_batch(
                    mode["assignments"], source_report_path=Path(reference["source_report_path"]),
                    source_report_sha256=reference["source_report_sha256"])
                if json.dumps(projection, sort_keys=True) != json.dumps(expected, sort_keys=True):
                    raise ValueError("Projected reference differs from existing producer authority")
                execution = projection["projected_fresh_batch_execution_seconds"]
                invocation = projection["projected_fresh_batch_prepared_invocation_seconds"]
            else:
                if actual["native_job_count"] != 1 or case["native_execution_projection"] is not None:
                    raise ValueError("Measured headline must be one genuine stock CP batch")
                execution, invocation = fresh.pipeline_execution_seconds, fresh.invocation_seconds
            if (not math.isclose(reference["execution_seconds"], execution, rel_tol=1e-12)
                    or not math.isclose(reference["prepared_invocation_seconds"], invocation, rel_tol=1e-12)):
                raise ValueError("Headline durations differ from genuine/derived source authority")
            mode_kinds.add(kind)
            inputs.append(native_path)
        if len(mode_kinds) != 1:
            raise ValueError("Each mode must declare one measured/projected headline kind")
        kinds[name] = mode_kinds.pop()
        if len(mode_affinities) != 1:
            raise ValueError("Each mode must retain one native source CPU affinity")
        native_affinities[name] = mode_affinities.pop()
        label = (f"{mode['openhcs_workers']} worker{'s' if mode['openhcs_workers'] != 1 else ''} / "
                 f"{mode['assignments']} assignments\nCP {'projected' if kinds[name] == 'projected_first_batch' else 'measured'}")
        for scope in ("execution", "total"):
            path = record / "data/first_use" / name / f"first_use_{scope}_summary.csv"
            source = figures.SummarySource(label, path)
            with path.open(newline="", encoding="utf-8") as stream:
                records = tuple(csv.DictReader(stream))
            table = {row["case_name"]: row for row in records}
            if len(records) != len(table) or set(table) != set(cases[name]):
                raise ValueError("First-use summary must contain the exact thirty qualified cases")
            if cohort is None:
                cohort = set(table)
            if set(table) != cohort:
                raise ValueError("Modes cannot mix workflow cohorts")
            for case_name, row in table.items():
                case = cases[name][case_name]
                reference = case["native_headline_reference"]
                native_seconds = reference["execution_seconds" if scope == "execution" else "prepared_invocation_seconds"]
                oh_seconds = statistics.median(observation[f"openhcs_{scope}_seconds"] for observation in case["rows"])
                if (len(case["rows"]) != 3 or int(row["n"]) != 3
                        or row["native_reference_kind"] != reference["kind"]
                        or int(row["native_observation_count"]) != reference["target_native_observation_count"]
                        or not math.isclose(float(row[figures.NATIVE_SECONDS_FIELD]), native_seconds, rel_tol=1e-12)
                        or not math.isclose(float(row[figures.OPENHCS_SECONDS_FIELD]), oh_seconds, rel_tol=1e-12)
                        or not math.isclose(float(row["median_speedup"]), native_seconds / oh_seconds, rel_tol=1e-12)):
                    raise ValueError("First-use CSV must match explicit native reference and genuine OH median")
            sources[name, scope], tables[name, scope] = source, table
            inputs.extend((path, custody_path, manifest_path))
    if any(not path.resolve().is_relative_to(root) for path in inputs):
        raise ValueError("Archive all consumed sources before rendering")
    inputs = tuple(dict.fromkeys(inputs))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    interpretation = {"source_revision": declaration["source_revision"],
                      "native_reference_kinds": kinds,
                      "native_source_cpu_affinities": native_affinities,
                      "calibration_scope": "CP1 versus CP8 uses different CPU affinity (one versus four slots), so not a batching-only effect. Matched-affinity cold-first validation covers three workflows, not the full thirty; cross-campaign anchor variation remains visible.",
                      "native_policy": "Measured CP first batch n=1 at 1/8 assignments; explicitly projected first-use CP reference at 12/16; OH median n=3. No target native observations fabricated.",
                      "memory": "Unavailable; no historical substitution"}

    def save(destination, outputs, meaning):
        build_slas_benchmark.write_provenance(destination, inputs, tuple(outputs),
                                             {**interpretation, "interpretation": meaning})

    # One diagnostic calibration, not a parallel cold/warm headline figure set.
    anchor_modes = {mode["assignments"]: mode["archive_mode"] for mode in modes_to_read
                    if mode["assignments"] in (1, 8)}
    data, calibration_rows = [], []
    for case_name in tables[anchor_modes[1], "execution"]:
        values = {"case_name": case_name}
        for count, name in anchor_modes.items():
            case = cases[name][case_name]
            reference = case["native_headline_reference"]
            values[f"actual_cp{count}_cpu_affinity_slot_count"] = len(native_affinities[name])
            values[f"actual_cp{count}_first_execution_seconds"] = reference["execution_seconds"]
            values[f"actual_cp{count}_first_prepared_invocation_seconds"] = reference["prepared_invocation_seconds"]
            values[f"actual_cp{count}_warm_execution_median_seconds"] = statistics.median(row["native_execution_seconds"] for row in case["rows"])
        ratio = values["actual_cp8_first_execution_seconds"] / (8 * values["actual_cp1_first_execution_seconds"])
        values["actual_cp8_first_over_8cp1_first_ratio"] = ratio
        source = sources[anchor_modes[8], "execution"]
        row = tables[anchor_modes[8], "execution"][case_name]
        calibration_rows.append(replace(source.metric_rows(case_name, row, category_row=row)[0],
                                        method="Actual CP8 first / (8 × actual CP1 first)", speedup=ratio))
        data.append(values)
    destination = args.output_dir / "native_actual1_actual8_calibration"
    destination.mkdir(parents=True, exist_ok=True)
    table_path = destination / "actual_native_batch_calibration.csv"
    with table_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(data[0])); writer.writeheader(); writer.writerows(data)
    outputs = figures.FIGURE_STYLE.generate_average_point_figures(
        calibration_rows, methods=(calibration_rows[0].method,), output_dir=destination,
        output_formats=("png", "svg"), filename_stem="actual_native_first_batch_calibration",
        title=(f"Diagnostic: CP1 affinity {len(native_affinities[anchor_modes[1]])} CPU / "
               f"CP8 affinity {len(native_affinities[anchor_modes[8]])} CPUs"),
        ylabel="Actual CP8 first / (8 × actual CP1 first)", value_key="speedup", target_line=1, log_variant=True)
    save(destination, (table_path, *outputs), "Actual CP first batches use different CPU affinities (CP1 one slot versus CP8 four slots): this ratio cannot isolate batching savings. Cold-first model diagnostics cover three representative workflows, not full-cohort measured target validation, with cross-campaign anchor variation retained.")
    if args.calibration_only:
        return

    fixed_name = f"fixed{fixed_count}"
    reference_cases = cases[fixed[0]["archive_mode"]]
    for mode in fixed:
        if fixed_count % mode["openhcs_workers"]:
            raise ValueError("Fixed workload must partition evenly")
        for name, case in cases[mode["archive_mode"]].items():
            for field in ("wells", "selected_source_wells", "assignment_scope"):
                if case["mode"][field] != reference_cases[name]["mode"][field]:
                    raise ValueError(f"Fixed workload assignment roles differ: {field}")
    for scope in ("execution", "total"):
        for schedule_name, schedule in (("may", may), (fixed_name, fixed)):
            destination = args.output_dir / schedule_name / scope
            destination.mkdir(parents=True, exist_ok=True)
            paired, candidates = [], []
            for mode in schedule:
                source = sources[mode["archive_mode"], scope]
                for name, row in tables[mode["archive_mode"], scope].items():
                    native, candidate = source.metric_rows(name, row, category_row=row)
                    paired.extend((replace(native, method=f"CP first batch ({source.label})"), candidate))
                    candidates.append(candidate)
            table_path = destination / "first_use_workflow_metrics.csv"
            figures._write_metric_rows(table_path, paired)
            outputs = figures.generate_grouped_benchmark_metric_figures(
                paired, metrics=(figures.FigureMetricSpec("raw_seconds", "first_use_runtime", f"First-use CP / OH median {scope} runtime", "Seconds", log_variant=True),
                                 figures.FigureMetricSpec("speedup", "first_use_speedup", f"CP first-use reference / OH median {scope} speedup", "Speedup (x)", baseline_line=1, log_variant=True)),
                methods=tuple(dict.fromkeys(row.method for row in paired)), pipeline_names=tuple(tables[schedule[0]["archive_mode"], scope]),
                output_dir=destination, output_formats=("png", "svg"))
            average = figures.FIGURE_STYLE.generate_average_point_figures(
                candidates, methods=tuple(sources[mode["archive_mode"], scope].candidate_method for mode in schedule),
                output_dir=destination, output_formats=("png", "svg"), filename_stem=f"{schedule_name}_{scope}_mean_workflow_points",
                title=f"CP first batch / OH median: {scope}\nCP1/8 measured; CP12/16 projected",
                ylabel="CP first-use batch reference / OpenHCS speedup", value_key="speedup", target_line=1, log_variant=True)
            caption = destination / "first_use_policy.json"
            caption.write_text(json.dumps({**interpretation, "scope": scope}, indent=2) + "\n")
            save(destination, (table_path, caption, *outputs, *average), "Thirty workflow dots, arithmetic mean bars and median lines. May changing-workload CP-relative ratios are not fixed-workload parallel efficiency.")
        reference_source = sources[fixed[0]["archive_mode"], scope]
        reference = {name: reference_source.metric_rows(name, row, category_row=row)[1].raw_seconds
                     for name, row in tables[fixed[0]["archive_mode"], scope].items()}
        for metric in ("scaling", "efficiency"):
            destination = args.output_dir / fixed_name / scope / metric
            destination.mkdir(parents=True, exist_ok=True)
            rows = []
            for mode in fixed:
                source = sources[mode["archive_mode"], scope]
                for name, row in tables[mode["archive_mode"], scope].items():
                    candidate = source.metric_rows(name, row, category_row=row)[1]
                    value = reference[name] / candidate.raw_seconds
                    if metric == "efficiency": value /= mode["openhcs_workers"]
                    rows.append(replace(candidate, method=f"OH {mode['openhcs_workers']} workers / {fixed_count} assignments", speedup=value))
            table_path = destination / "derived_workflow_metrics.csv"
            dictionaries = [asdict(row) for row in rows]
            if metric == "efficiency":
                for values in dictionaries: values["efficiency_unit_fraction"] = values.pop("speedup")
            with table_path.open("w", newline="", encoding="utf-8") as stream:
                writer = csv.DictWriter(stream, fieldnames=tuple(dictionaries[0])); writer.writeheader(); writer.writerows(dictionaries)
            outputs = () if metric == "efficiency" else figures.FIGURE_STYLE.generate_average_point_figures(
                rows, methods=tuple(dict.fromkeys(row.method for row in rows)), output_dir=destination,
                output_formats=("png", "svg"), filename_stem=f"{fixed_name}_{scope}_scaling",
                title=f"{fixed_count} measured assignments: OH {scope} scaling",
                ylabel="Actual OH one-worker / n-worker speedup", value_key="speedup", target_line=1, log_variant=True)
            save(destination, (table_path, *outputs), "Entirely actual OpenHCS fixed-workload medians; efficiency divides one-/n-worker speedup by workers. No CP projection is used.")


if __name__ == "__main__":
    main()
