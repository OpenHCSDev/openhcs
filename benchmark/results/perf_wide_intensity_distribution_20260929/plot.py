"""Plot measured OpenHCS phases against the retained native CP scaling run."""

from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
NATIVE_ROOT = ROOT.parent / "perf_native_synthetic_scaling_20260929"
CASE = "ExampleImagingFlowCytometryObjectsInGrid"


def main() -> None:
    with (ROOT / "observations.csv").open(newline="") as stream:
        observations = tuple(csv.DictReader(stream))
    selected = {
        (row["role"], int(row["well_count"])): row
        for row in observations
        if row["role"] in ("control", "candidate")
    }
    wells = (1, 16)
    native = []
    for count in wells:
        report = json.loads((NATIVE_ROOT / f"{CASE}_{count}w_summary.json").read_text())
        assert report["total_image_sets"] == 2 * count
        (timing,) = (row for row in report["timing"] if row["repetition"] == 0)
        native.append(timing["invocation_through_completion_makespan_seconds"])

    figure, (scaling, phases) = plt.subplots(1, 2, figsize=(12, 4.8))
    scaling.plot(
        wells,
        native,
        "o-",
        color="#b46239",
        label="Native CP, measured warm invocation",
    )
    for role, label, color in (
        ("control", "OpenHCS parent", "#677687"),
        ("candidate", "OpenHCS wide output", "#138579"),
    ):
        durations = [float(selected[role, count]["execute_seconds"]) for count in wells]
        scaling.plot(wells, durations, "o-", color=color, label=label)
        if role == "candidate":
            for count, cp, seconds in zip(wells, native, durations, strict=True):
                scaling.annotate(
                    f"{cp / seconds:.2f}×",
                    (count, seconds),
                    xytext=(0, -15),
                    textcoords="offset points",
                    ha="center",
                    color=color,
                )
    scaling.set(
        title="Execution scaling",
        xlabel="Synthetic replicated wells",
        ylabel="Seconds",
        xticks=wells,
        yscale="log",
    )
    scaling.grid(axis="y", alpha=0.25)
    scaling.margins(y=0.15)
    scaling.legend(fontsize=8)

    phase_rows = [
        selected[role, count] for count in wells for role in ("control", "candidate")
    ]
    labels = [f"{row['well_count']}w\n{row['role']}" for row in phase_rows]
    compile_seconds = [float(row["compile_seconds"]) for row in phase_rows]
    execution = [float(row["execute_seconds"]) for row in phase_rows]
    total = [float(row["total_seconds"]) for row in phase_rows]
    other = [
        t - c - e for t, c, e in zip(total, compile_seconds, execution, strict=True)
    ]
    phases.bar(labels, execution, label="Server execution", color="#138579")
    phases.bar(
        labels, compile_seconds, bottom=execution, label="Compilation", color="#dfb14b"
    )
    phases.bar(
        labels,
        other,
        bottom=[c + e for c, e in zip(compile_seconds, execution, strict=True)],
        label="Other measured overhead",
        color="#677687",
    )
    for index, seconds in enumerate(total):
        phases.text(index, seconds + 2, f"{seconds:.2f}s", ha="center", fontsize=9)
    phases.set(
        title="Fresh-server total time", ylabel="Seconds", ylim=(0, max(total) * 1.15)
    )
    phases.legend(fontsize=8)
    phases.grid(axis="y", alpha=0.2)
    phases.set_axisbelow(True)
    figure.suptitle("ImagingFlow: wide intensity-distribution columns")
    figure.text(
        0.5,
        0.01,
        "1/4 OpenHCS fork workers; 1/4 native CP jobs. Native points reuse the retained measured run. "
        "Replicated pixels benefit from OpenHCS content caches.",
        ha="center",
        fontsize=8,
    )
    figure.tight_layout(rect=(0, 0.04, 1, 0.94))
    for suffix in ("png", "svg"):
        figure.savefig(ROOT / f"measured_scaling.{suffix}", dpi=180)
    plt.close(figure)


if __name__ == "__main__":
    main()
