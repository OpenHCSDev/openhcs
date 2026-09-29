"""Plot retained ordinary cold and warm timings, including every repetition."""

from __future__ import annotations

import csv
from pathlib import Path
from statistics import median

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def main() -> None:
    with (ROOT / "observations.csv").open(newline="") as stream:
        rows = tuple(csv.DictReader(stream))
    figure, axes = plt.subplots(1, 2, figsize=(10, 4.5), sharey=True)
    for axis, cache in zip(axes, ("cold", "warm"), strict=True):
        for index, role in enumerate(("control", "candidate")):
            selected = [
                row
                for row in rows
                if row["role"] == role and row["cache_state"] == cache
            ]
            compile_seconds = median(float(row["compile_seconds"]) for row in selected)
            execute_seconds = median(float(row["execute_seconds"]) for row in selected)
            total_seconds = median(float(row["total_seconds"]) for row in selected)
            other = total_seconds - compile_seconds - execute_seconds
            axis.bar(
                index,
                execute_seconds,
                color="#138579",
                label="Server execution" if index == 0 else None,
            )
            axis.bar(
                index,
                compile_seconds,
                bottom=execute_seconds,
                color="#dfb14b",
                label="Compilation" if index == 0 else None,
            )
            axis.bar(
                index,
                other,
                bottom=execute_seconds + compile_seconds,
                color="#677687",
                label="Other measured overhead" if index == 0 else None,
            )
            axis.scatter(
                [index] * len(selected),
                [float(row["total_seconds"]) for row in selected],
                color="black",
                marker="_",
                zorder=3,
            )
            axis.text(index, total_seconds + 1.5, f"{total_seconds:.2f}s", ha="center")
        axis.set(
            title=f"{cache.title()} persistent cache",
            xticks=(0, 1),
            xticklabels=("Main", "Fork preparation"),
            ylim=(0, 72),
            ylabel="Seconds",
        )
        axis.grid(axis="y", alpha=0.2)
        axis.set_axisbelow(True)
    axes[0].legend(fontsize=8)
    figure.suptitle("ImagingFlow: one well, one execution worker")
    figure.text(
        0.5,
        0.01,
        "Fresh ordinary server each run. Cold candidate uses up to four compiler fork children.\nBars show medians; black ticks retain all measured totals (two cold repetitions, one warm).",
        ha="center",
        fontsize=8,
    )
    figure.tight_layout(rect=(0, 0.07, 1, 0.93))
    for suffix in ("png", "svg"):
        figure.savefig(ROOT / f"measured_phases.{suffix}", dpi=180)
    plt.close(figure)


if __name__ == "__main__":
    main()
