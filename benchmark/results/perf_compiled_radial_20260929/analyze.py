"""Summarize the retained ordinary-run measurements; no runtime profiling."""

from collections import defaultdict
import csv
import json
from pathlib import Path
from statistics import median

HERE = Path(__file__).resolve().parent


def main():
    result = {
        "modes": {},
        "native_reference": {
            "1w_execution_seconds": 65.923852724,
            "16w_execution_seconds": 364.230098475,
            "scope": "Previously completed physical CP 4.2.8.1 analysis; startup, full warmup and final shutdown excluded. Original 16w controller exit unobserved.",
        },
    }
    for mode in ("1w", "16w"):
        rows = [
            json.loads(line)
            for line in (HERE / f"observations_{mode}.jsonl").read_text().splitlines()
        ]
        data = {}
        for variant in ("control", "candidate"):
            selected = [row for row in rows if row["variant"] == variant]
            assert len(selected) == 2 and all(
                row["status"] == "success"
                and not row["new_or_modified_radial_cache_files"]
                for row in selected
            )
            step_totals = defaultdict(list)
            for row in selected:
                totals = defaultdict(float)
                with (
                    HERE
                    / "runs"
                    / mode
                    / f"{variant}_{row['repetition']}"
                    / "steps.csv"
                ).open() as stream:
                    for step in csv.DictReader(stream):
                        totals[step["step_name"]] += float(step["step_seconds"])
                for name, seconds in totals.items():
                    step_totals[name].append(seconds)
            data[variant] = dict(
                median={
                    key: median(row[key] for row in selected)
                    for key in ("compile", "execution", "total", "warming_seconds")
                },
                observations=selected,
                median_step_sums={
                    name: median(values) for name, values in step_totals.items()
                },
            )
        data["improvement"] = {
            key: dict(
                seconds=data["control"]["median"][key]
                - data["candidate"]["median"][key],
                percent=100
                * (
                    1
                    - data["candidate"]["median"][key] / data["control"]["median"][key]
                ),
            )
            for key in ("execution", "total")
        }
        data["native_execution_ratio"] = (
            result["native_reference"][f"{mode}_execution_seconds"]
            / data["candidate"]["median"]["execution"]
        )
        result["modes"][mode] = data
    (HERE / "analysis.json").write_text(json.dumps(result, indent=2) + "\n")
    print(
        json.dumps(
            {
                mode: {
                    "control": data["control"]["median"],
                    "candidate": data["candidate"]["median"],
                    "improvement": data["improvement"],
                    "native_execution_ratio": data["native_execution_ratio"],
                }
                for mode, data in result["modes"].items()
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
