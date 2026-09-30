"""Derive timing attribution and revised native ratios from retained observations."""

import csv
import json
from collections import defaultdict
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parent
LABELS = (
    "historical_control",
    "historical_fused",
    "control_1",
    "fused_1",
    "fused_2",
    "control_2",
    "audit_overlap",
)


def main():
    observations = []
    for label in LABELS:
        row = json.loads((ROOT / f"{label}_observation.json").read_text())
        totals = defaultdict(float)
        waves = defaultdict(lambda: defaultdict(float))
        for step in csv.DictReader((ROOT / f"{label}_steps.csv").open()):
            totals[step["step_name"]] += float(step["step_seconds"])
            if step["axis_id"].startswith("W"):
                wave = (int(step["axis_id"][1:]) - 1) // 4 + 1
                waves[wave][step["step_name"]] += float(step["step_seconds"])
        item = {
            "label": label,
            "execution_seconds": float(row["execute_seconds"]),
            "total_seconds": float(row["total_seconds"]),
            "compile_seconds": float(row["compile_seconds"]),
            "step_sums": dict(totals),
            "wave_step_sums": dict(waves),
        }
        item["other_processing_step_seconds"] = (
            sum(totals.values())
            - totals["MeasureTexture"]
            - totals["ExportToSpreadsheet"]
        )
        observations.append(item)
    clean = {}
    for variant in ("control", "fused"):
        rows = [
            item
            for item in observations
            if item["label"] in (f"{variant}_1", f"{variant}_2")
        ]
        clean[variant] = {
            key: median(item[key] for item in rows)
            for key in (
                "execution_seconds",
                "total_seconds",
                "compile_seconds",
                "other_processing_step_seconds",
            )
        }
        clean[variant]["step_sums"] = {
            key: median(item["step_sums"][key] for item in rows)
            for key in rows[0]["step_sums"]
        }
    report = {
        "observations": observations,
        "clean_medians": clean,
        "warning": "Step aggregates sum four parallel workers; they are not wall time. Two clean observations per variant do not establish a confidence interval. Global PSI does not attribute each stall to a specific process.",
    }
    (ROOT / "analysis.json").write_text(json.dumps(report, indent=2) + "\n")
    native_dir = ROOT.parent / "perf_fused_haralick_scaling_20260929"
    previous_ratios = json.loads((native_dir / "measured_ratios.json").read_text())
    ratios = [previous_ratios[0], dict(previous_ratios[1])]
    ratios[1].update(
        openhcs_execution_seconds=clean["fused"]["execution_seconds"],
        openhcs_total_seconds=clean["fused"]["total_seconds"],
    )
    ratios[1]["execution_ratio"] = (
        ratios[1]["native_warm_invocation_seconds"]
        / ratios[1]["openhcs_execution_seconds"]
    )
    ratios[1]["openhcs_execution_range_seconds"] = [
        min(
            item["execution_seconds"]
            for item in observations
            if item["label"].startswith("fused_")
        ),
        max(
            item["execution_seconds"]
            for item in observations
            if item["label"].startswith("fused_")
        ),
    ]
    (ROOT / "measured_ratios.json").write_text(json.dumps(ratios, indent=2) + "\n")
    processes = [
        json.loads(line)
        for line in (ROOT / "audit_overlap_resources.jsonl").read_text().splitlines()
    ]
    pressure = [
        json.loads(line)
        for line in (ROOT / "audit_overlap_pressure.jsonl").read_text().splitlines()
    ]
    audits = [
        json.loads(line)
        for line in (ROOT / "audit_processes.jsonl").read_text().splitlines()
    ]
    for audit in audits:
        samples = [
            proc
            for sample in processes
            for proc in sample["processes"]
            if proc["pid"] == audit["pid"]
        ]
        audit["sampled_peak_rss_bytes"] = (
            max(proc["rss_pages"] for proc in samples) * 4096
        )
        audit["sampled_cpu_seconds"] = max(
            proc["utime"] + proc["stime"] for proc in samples
        )
        observations = [
            (sample["time"], proc)
            for sample in processes
            for proc in sample["processes"]
            if proc["pid"] == audit["pid"]
        ]
        audit["first_sample_at"] = observations[0][0]
        audit["last_non_zombie_sample_at"] = max(
            timestamp for timestamp, proc in observations if proc["state"] != "Z"
        )
        audit["first_zombie_sample_at"] = min(
            timestamp for timestamp, proc in observations if proc["state"] == "Z"
        )
    some_total = lambda sample: int(
        sample["memory_psi"].splitlines()[0].split("total=")[1]
    )
    resource_report = {
        "audits": audits,
        "minimum_memory_available_kib": min(
            int(sample["memory"]["MemAvailable"].split()[0]) for sample in pressure
        ),
        "global_memory_some_stall_seconds": (
            some_total(pressure[-1]) - some_total(pressure[0])
        )
        / 1e6,
        "page_size_bytes": 4096,
        "warning": "RSS includes shared pages. PSI is host-wide; no clean-run PSI comparison was captured.",
    }
    (ROOT / "resource_summary.json").write_text(
        json.dumps(resource_report, indent=2) + "\n"
    )
    print(
        json.dumps(
            {
                "clean_medians": clean,
                "revised_execution_ratio": ratios[1]["execution_ratio"],
                "resources": resource_report,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
