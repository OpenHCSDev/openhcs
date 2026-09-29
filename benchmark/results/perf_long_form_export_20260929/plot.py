"""Render native-relative ImagingFlow execution figures from recorded observations."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def main() -> None:
    with (ROOT / "observations.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    by_pair = {(row["pair"], row["variant"]): row for row in rows}

    figure, (scaling, stacked) = plt.subplots(1, 2, figsize=(11, 4.5))
    wells = (1, 16)
    for variant, color in (("control", "#677687"), ("candidate", "#138579")):
        values = [
            float(by_pair[(f"integrated_{count}w", variant)]["execute_seconds"])
            for count in wells
        ]
        scaling.plot(
            wells,
            values,
            marker="o",
            linewidth=2.2,
            color=color,
            label=f"OpenHCS {variant}",
        )
    native = [
        float(
            by_pair[(f"integrated_{count}w", "candidate")][
                "projected_native_execution_seconds"
            ]
        )
        for count in wells
    ]
    scaling.plot(
        wells,
        native,
        marker="o",
        linestyle="--",
        linewidth=1.7,
        color="#b46239",
        label="Native CP (16w projected)",
    )
    scaling.set(
        title="Integrated checkout: one vs 16 wells",
        xlabel="Wells",
        ylabel="Execution seconds (log scale)",
        xticks=wells,
        ylim=(12, 1400),
    )
    scaling.set_yscale("log")
    scaling.grid(axis="y", alpha=0.25)
    scaling.legend(loc="upper left", fontsize=8)
    for count, native_seconds in zip(wells, native, strict=True):
        candidate_seconds = float(
            by_pair[(f"integrated_{count}w", "candidate")]["execute_seconds"]
        )
        scaling.annotate(
            f"{native_seconds / candidate_seconds:.2f}×",
            (count, candidate_seconds),
            xytext=(0, 11 if count == 1 else -19),
            textcoords="offset points",
            ha="center",
            fontsize=9,
            color="#116e64",
        )

    exact = [
        float(by_pair[("stacked_pr_16w", variant)]["execute_seconds"])
        for variant in ("control", "candidate")
    ]
    bars = stacked.bar(
        ("Control", "Candidate"),
        exact,
        color=("#677687", "#138579"),
        width=0.55,
    )
    stacked.bar_label(bars, labels=[f"{value:.1f}s" for value in exact], padding=4)
    stacked.set(
        title="Exact stacked PR: 16 wells",
        ylabel="Execution seconds",
        ylim=(0, max(exact) * 1.18),
    )
    stacked.grid(axis="y", alpha=0.25)
    stacked.set_axisbelow(True)
    stacked.text(
        0.5,
        0.91,
        f"{exact[0] - exact[1]:.1f}s saved",
        transform=stacked.transAxes,
        ha="center",
        color="#116e64",
        fontsize=10,
    )

    figure.suptitle("ImagingFlow execution: long-form spreadsheet folding")
    figure.text(
        0.5,
        0.015,
        "Native CP: one sample measured; 16 wells = 16 × that measurement, "
        "not a native plate run.",
        ha="center",
        fontsize=8,
        color="#555555",
    )
    figure.tight_layout(rect=(0, 0.04, 1, 0.95))
    figure.savefig(ROOT / "imagingflow_scaling_vs_native.png", dpi=170)


if __name__ == "__main__":
    main()
