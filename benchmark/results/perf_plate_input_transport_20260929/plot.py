"""Regenerate the plate-input transport benchmark figures from committed CSVs."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent
CONTROL_COLOR = "#4263a6"
CANDIDATE_COLOR = "#159c85"


def read_rows(name: str) -> list[dict[str, str]]:
    with (ROOT / name).open(newline="") as stream:
        return list(csv.DictReader(stream))


def plot_official30() -> None:
    rows = {
        label: read_rows(f"official30_{label}.csv")
        for label in ("control", "candidate")
    }
    totals = {}
    for label, observations in rows.items():
        compile_seconds = sum(float(row["compile_seconds"]) for row in observations)
        execute_seconds = sum(float(row["execute_seconds"]) for row in observations)
        total_seconds = sum(float(row["total_seconds"]) for row in observations)
        totals[label] = (
            compile_seconds,
            execute_seconds,
            total_seconds - compile_seconds - execute_seconds,
            total_seconds,
        )

    fig, ax = plt.subplots(figsize=(9, 4.8))
    positions = np.arange(4)
    width = 0.35
    for offset, label, color in (
        (-width / 2, "control", CONTROL_COLOR),
        (width / 2, "candidate", CANDIDATE_COLOR),
    ):
        bars = ax.bar(
            positions + offset,
            totals[label],
            width,
            label=label.title(),
            color=color,
        )
        ax.bar_label(bars, fmt="%.1f", padding=3, fontsize=8)
    ax.set_xticks(positions, ("Compile", "Execute", "Other", "Total"))
    ax.set_ylabel("Summed seconds over 30 one-well observations")
    ax.set_title("Fresh-server official30: plate-input record transport")
    ax.legend(frameon=False)
    ax.set_ylim(0, 245)
    ax.spines[["top", "right"]].set_visible(False)
    fig.tight_layout()
    fig.savefig(ROOT / "official30_phase_totals.png", dpi=170)
    plt.close(fig)


def plot_multiwell() -> None:
    rows = read_rows("multiwell.csv")
    cases = ("ExampleColocalization", "ExampleImagingFlowCytometryObjectsInGrid")
    labels = ("Colocalization", "ImagingFlow")
    by_case = {(row["case_name"], row["variant"]): row for row in rows}
    fig, axes = plt.subplots(1, 2, figsize=(11, 4.8))
    positions = np.arange(len(cases))
    width = 0.36
    for axis, field, title in (
        (axes[0], "execute_seconds", "Server execution"),
        (axes[1], "post_worker_gap_seconds", "Worker finish to plate export"),
    ):
        for offset, variant, color in (
            (-width / 2, "control", CONTROL_COLOR),
            (width / 2, "candidate", CANDIDATE_COLOR),
        ):
            values = [float(by_case[(case, variant)][field]) for case in cases]
            bars = axis.bar(
                positions + offset,
                values,
                width,
                color=color,
                label=variant.title(),
            )
            axis.bar_label(bars, fmt="%.1f", padding=3, fontsize=8)
        axis.set_xticks(positions, labels)
        axis.set_title(title)
        axis.set_ylabel("Seconds")
        axis.spines[["top", "right"]].set_visible(False)
        axis.set_ylim(0, max(float(row[field]) for row in rows) * 1.18)
    native_speedups = tuple(
        float(by_case[(case, "candidate")]["projected_native_execution_seconds"])
        / float(by_case[(case, "candidate")]["execute_seconds"])
        for case in cases
    )
    axes[0].set_xticks(
        positions,
        tuple(
            f"{label}\nCP cold projection: {speedup:.1f}×"
            for label, speedup in zip(labels, native_speedups, strict=True)
        ),
    )
    axes[0].legend(frameon=False)
    fig.suptitle(
        "16 wells, four fork workers; native CP is a 16× cold-launch projection"
    )
    fig.tight_layout()
    fig.savefig(ROOT / "multiwell_execution_and_transfer.png", dpi=170)
    plt.close(fig)


if __name__ == "__main__":
    plot_official30()
    plot_multiwell()
