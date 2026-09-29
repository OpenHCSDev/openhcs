"""Regenerate Costes cache execution figures from retained benchmark CSVs."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent
TARGETS = (
    "cp_tutorial_advanced_segmentation_final",
    "cp_tutorial_beginner_segmentation_final",
)


def rows(path: Path) -> dict[str, dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return {row["case_name"]: row for row in csv.DictReader(handle)}


control = rows(HERE / "full_warm_control.csv")
candidate = rows(HERE / "full_warm_candidate.csv")
native = rows(HERE.parent / "perf_lazy_catalog_20260929" / "native_cp_summary.csv")

fig, ax = plt.subplots(figsize=(9.5, 4.5), layout="constrained")
x = np.arange(len(TARGETS))
width = 0.23
for offset, label, values, color in (
    (
        -width,
        "Native CellProfiler",
        [float(native[name]["median_native_execution_seconds"]) for name in TARGETS],
        "#697b8c",
    ),
    (
        0,
        "OpenHCS control",
        [float(control[name]["execute_seconds"]) for name in TARGETS],
        "#d87a57",
    ),
    (
        width,
        "OpenHCS step cache",
        [float(candidate[name]["execute_seconds"]) for name in TARGETS],
        "#3a8c83",
    ),
):
    bars = ax.bar(x + offset, values, width, label=label, color=color)
    ax.bar_label(bars, fmt="%.2f", padding=3, fontsize=9)
ax.set_xticks(x, ("Advanced segmentation", "Beginner segmentation"))
ax.set_ylabel("Execution seconds, one well / one thread")
ax.set_ylim(0, 42)
ax.legend(frameon=False, ncol=3, loc="upper right")
ax.set_title("Repeated Costes inputs: exact step-local threshold reuse")
fig.savefig(HERE / "affected_case_execution.png", dpi=180)
plt.close(fig)

ordered = sorted(
    control,
    key=lambda name: float(candidate[name]["execute_seconds"])
    - float(control[name]["execute_seconds"]),
)
deltas = [
    float(candidate[name]["execute_seconds"]) - float(control[name]["execute_seconds"])
    for name in ordered
]
colors = ["#3a8c83" if name in TARGETS else "#aeb7bf" for name in ordered]
fig, ax = plt.subplots(figsize=(10, 9), layout="constrained")
ax.barh(range(len(ordered)), deltas, color=colors)
ax.set_yticks(range(len(ordered)), ordered, fontsize=7.5)
ax.invert_yaxis()
ax.axvline(0, color="#2f3640", linewidth=0.8)
ax.set_xlabel("Candidate minus control execution seconds (lower is faster)")
ax.set_title("Warmed official30 paired execution differences")
fig.savefig(HERE / "full_suite_execution_delta.png", dpi=180)
plt.close(fig)
