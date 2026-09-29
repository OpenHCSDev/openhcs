"""Rebuild the measured native-CP/OpenHCS well-scaling figure."""

from __future__ import annotations

import csv
import json
from pathlib import Path

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def _native_seconds(case: str, wells: int) -> float:
    report = json.loads((ROOT / f"{case}_{wells}w_summary.json").read_text())
    assert report["case"] == case and report["wells"] == wells
    assert report["native_jobs"] == (1 if wells == 1 else 4)
    assert report["total_image_sets"] == 2 * wells
    (timing,) = (row for row in report["timing"] if row["repetition"] == 0)
    return float(timing["invocation_through_completion_makespan_seconds"])


def main() -> None:
    with (ROOT / "openhcs_observations.csv").open(newline="") as stream:
        observations = tuple(csv.DictReader(stream))
    figure, axes = plt.subplots(1, 2, figsize=(11.6, 4.5), sharey=True)
    for axis, observation in zip(axes, observations, strict=True):
        case = observation["case"]
        wells = (1, 16)
        openhcs = (
            float(observation["openhcs_1w_execution_seconds"]),
            float(observation["openhcs_16w_execution_seconds"]),
        )
        native = tuple(_native_seconds(case, count) for count in wells)
        cold_projection = float(observation["native_cold_1w_seconds"]) * 16
        axis.plot(
            wells,
            openhcs,
            color="#138579",
            marker="o",
            linewidth=2.2,
            label="OpenHCS measured",
        )
        axis.plot(
            wells,
            native,
            color="#b46239",
            marker="o",
            linewidth=2.2,
            label="Native CP measured, warm",
        )
        axis.scatter(
            (16,),
            (cold_projection,),
            color="#677687",
            marker="x",
            s=65,
            linewidths=2,
            label="16 × CP cold-launch reference",
        )
        for count, native_seconds, openhcs_seconds in zip(
            wells, native, openhcs, strict=True
        ):
            axis.annotate(
                f"{native_seconds / openhcs_seconds:.2f}×",
                (count, openhcs_seconds),
                xytext=(0, 8),
                textcoords="offset points",
                ha="center",
                color="#116e64",
                fontsize=9,
            )
        axis.set(
            title=observation["label"],
            xlabel="Synthetic wells",
            xticks=wells,
            ylabel="Execution seconds" if axis is axes[0] else None,
            ylim=(1.5, 1400),
        )
        axis.set_yscale("log")
        axis.grid(axis="y", alpha=0.25)
    axes[0].legend(loc="upper left", fontsize=8)
    figure.suptitle("Measured one- and 16-well throughput: native CP vs OpenHCS")
    figure.text(
        0.5,
        0.015,
        "Native CP: warm invocation, one job at 1w and four jobs at 16w. "
        "OpenHCS: server execution, one/four fork workers. "
        "Gray crosses project a separate cold-launch CP reference.",
        ha="center",
        fontsize=8,
        color="#555555",
    )
    figure.tight_layout(rect=(0, 0.045, 1, 0.95))
    figure.savefig(ROOT / "measured_native_scaling.png", dpi=180)


if __name__ == "__main__":
    main()
