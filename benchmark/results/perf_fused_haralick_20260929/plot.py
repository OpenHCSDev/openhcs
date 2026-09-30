"""Plot the fresh-server observations after existing backend warming."""

import csv
from pathlib import Path
from statistics import median

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def main() -> None:
    with (ROOT / "observations.csv").open(newline="") as stream:
        rows = tuple(
            row for row in csv.DictReader(stream) if row["scope"] == "prewarmed"
        )
    figure, axes = plt.subplots(1, 2, figsize=(8.3, 3.8))
    for axis, metric, title in zip(
        axes,
        ("execute_seconds", "total_seconds"),
        ("Execution including export", "Total fresh-server lifecycle"),
        strict=True,
    ):
        for index, (variant, color) in enumerate(
            (("control", "#677687"), ("fused", "#138579"))
        ):
            samples = tuple(
                float(row[metric]) for row in rows if row["variant"] == variant
            )
            value = median(samples)
            axis.bar(index, value, color=color, alpha=0.75, width=0.6)
            axis.scatter(
                (index,) * len(samples), samples, color=color, edgecolor="black"
            )
            axis.text(index, value + 0.55, f"{value:.2f}s", ha="center")
        axis.set(
            title=title,
            ylabel="Seconds",
            xticks=(0, 1),
            xticklabels=("Main", "Fused"),
            ylim=(0, 28),
        )
        axis.grid(axis="y", alpha=0.2)
    figure.suptitle("ImagingFlow: one well, one native thread")
    figure.text(
        0.5,
        0.015,
        "Two observations each; persistent kernels warmed before the shown timing scopes.",
        ha="center",
        fontsize=8,
    )
    figure.tight_layout(rect=(0, 0.04, 1, 0.95))
    figure.savefig(ROOT / "measured_phases.png", dpi=180)
    figure.savefig(ROOT / "measured_phases.svg")


if __name__ == "__main__":
    main()
