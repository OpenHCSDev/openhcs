"""Compare complete qualified fixed12 captures; never execute processing."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import statistics
from pathlib import Path

HEAD = "3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9"
BASELINE_HEAD = "753d4b26de7eab3ac592b29c10d70c2c769a6763"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--qualified-view", type=Path, required=True)
    parser.add_argument("--baseline-root", type=Path, required=True)
    parser.add_argument("--baseline-qualified-view", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output_dir.exists(), "Fresh comparison output directory required")
    load = lambda path: json.loads(path.read_text())
    goal = load(args.qualified_view / "scaling_goal_summary.json")
    require(goal["source_head"] == HEAD and goal["workflow_count"] == 30
            and goal["assignments"] == 12, "Current full-cohort qualification differs")
    inputs, all_rows, native_anchors = {}, [], {}
    cohort = None
    for workers in (1, 4):
        name = f"12assignments-{workers}worker{'s' if workers != 1 else ''}"
        current_dir = args.qualified_view / "data/first_use" / name
        baseline_dir = args.baseline_qualified_view / "data/first_use" / name
        custody_paths = (current_dir / "summary_custody.json", baseline_dir / "summary_custody.json")
        current, baseline = (load(path) for path in custody_paths)
        for path in custody_paths:
            inputs[str(path)] = sha(path)
        require(current["status"] == baseline["status"] == "PASS", "Unqualified capture")
        require(current["source_head"] == HEAD and baseline["source_head"] == BASELINE_HEAD,
                "Compared source revisions differ")
        names = tuple(case["case"] for case in current["cases"])
        require(len(names) == len(set(names)) == 30, "All thirty distinct workflows required")
        require(names == tuple(case["case"] for case in baseline["cases"]), "Baseline cohort differs")
        require(cohort is None or cohort == names, "Worker cohort order differs")
        cohort = names
        for scope in ("execution", "total"):
            filename = f"first_use_{scope}_summary.csv"
            published = args.baseline_root / "data" / name / filename
            retained = baseline_dir / filename
            require(sha(published) == sha(retained), "Published baseline differs from qualified original")
            inputs[str(published)] = sha(published)
            inputs[str(retained)] = sha(retained)
            inputs[str(current_dir / filename)] = sha(current_dir / filename)
        for new, old in zip(current["cases"], baseline["cases"], strict=True):
            require(new["source_commit"] == HEAD and old["source_commit"] == BASELINE_HEAD,
                    "Per-case source differs")
            require(new["mode"]["candidate_worker_count"] == old["mode"]["candidate_worker_count"] == workers,
                    "Worker count differs")
            for case in (new, old):
                require(tuple(row["repetition"] for row in case["rows"]) == (0, 1, 2),
                        "Exactly three measured observations required; warmup excluded")
                require(len(case["mode"]["wells"]) == 12 and case["mode"]["native_job_count"] == 1,
                        "Actual workload/native serial reference differs")
                anchor = case["native_headline_reference"]
                projection = case["native_execution_projection"]
                require(anchor["kind"] == "projected_first_batch" and anchor["target_native_observation_count"] == 0,
                        "Native reference must remain explicitly projected")
                require(projection["source_assignment_count"] == 8 and projection["target_assignment_count"] == 12,
                        "Retained actual CP8 / projected CP12 domain differs")
                path = Path(anchor["source_report_path"])
                require(sha(path) == anchor["source_report_sha256"], "Retained actual CP8 bytes changed")
                inputs[str(path)] = sha(path)
            require(new["native_headline_reference"] == old["native_headline_reference"]
                    and new["native_execution_projection"] == old["native_execution_projection"],
                    "Native anchor or authorized CP12 projection changed")
            anchor = new["native_headline_reference"]
            require(new["case"] not in native_anchors or native_anchors[new["case"]] == anchor,
                    "Native reference differs across worker modes")
            native_anchors[new["case"]] = anchor
            for scope, key in (
                ("execution", "openhcs_execution_seconds"),
                ("total", "openhcs_total_seconds"),
                ("server_compile_plus_execution", "openhcs_server_compile_plus_execution_seconds"),
                ("server_compile", "openhcs_compile_seconds"),
            ):
                before = statistics.median(row[key] for row in old["rows"])
                after = statistics.median(row[key] for row in new["rows"])
                require(before > 0 and after > 0, "Nonpositive timing")
                all_rows.append({"case_name": new["case"], "worker_count": workers, "scope": scope,
                                 "baseline_median_seconds": before, "current_median_seconds": after,
                                 "current_over_baseline": after / before, "delta_seconds": after - before,
                                 "regressed": after > before, "baseline_source_head": BASELINE_HEAD,
                                 "current_source_head": HEAD})
    args.output_dir.mkdir(parents=True)
    csv_path = args.output_dir / "all30_old_new_timings.csv"
    with csv_path.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=tuple(all_rows[0]))
        writer.writeheader()
        writer.writerows(all_rows)
    summary = {"status": "PASS", "source_head": HEAD, "baseline_source_head": BASELINE_HEAD,
               "workflow_count": 30, "assignments": 12, "workers": [1, 4],
               "warmup_repetition": -1, "measured_repetitions": [0, 1, 2],
               "scaling": goal, "native_reference": "Unchanged CP12 projected from retained actual serial CP8",
               "regressions": [row for row in all_rows if row["regressed"]],
               "input_sha256": inputs, "output_sha256": {csv_path.name: sha(csv_path)},
               "script_sha256": sha(Path(__file__)),
               "interpretation": "All workflows retained. Timing deltas are observations, not significance tests. No selected-subset or modeled scaling headline."}
    (args.output_dir / "comparison_custody.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "workflow_count": 30, "rows": len(all_rows),
                      "output_dir": str(args.output_dir)}))


if __name__ == "__main__":
    main()
