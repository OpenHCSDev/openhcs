"""Regenerate startup and total-time figures from the retained CSVs."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent


def rows(path: Path) -> dict[str, dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return {row["case_name"]: row for row in csv.DictReader(handle)}


def nonjob(row: dict[str, str]) -> float:
    return (
        float(row["total_seconds"])
        - float(row["compile_seconds"])
        - float(row["execute_seconds"])
    )


control = rows(HERE / "control.csv")
candidate = rows(HERE / "candidate.csv")
native = rows(HERE.parent / "perf_lazy_catalog_20260929" / "native_cp_summary.csv")

names = ("Control", "Lazy NGFF imports")
observations = (control, candidate)
compile_time = [
    sum(float(row["compile_seconds"]) for row in dataset.values())
    for dataset in observations
]
execute_time = [
    sum(float(row["execute_seconds"]) for row in dataset.values())
    for dataset in observations
]
nonjob_time = [sum(nonjob(row) for row in dataset.values()) for dataset in observations]
native_five_x_line = (
    sum(float(row["median_native_total_phase_seconds"]) for row in native.values()) / 5
)

fig, ax = plt.subplots(figsize=(8, 5), layout="constrained")
x = np.arange(2)
ax.bar(x, compile_time, label="Server compilation", color="#697b8c")
ax.bar(
    x,
    execute_time,
    bottom=compile_time,
    label="Server execution",
    color="#d87a57",
)
bottom = np.array(compile_time) + np.array(execute_time)
ax.bar(x, nonjob_time, bottom=bottom, label="Other measured time", color="#3a8c83")
totals = bottom + np.array(nonjob_time)
for index, total in enumerate(totals):
    ax.text(
        index,
        total - 7,
        f"{total:.1f} s",
        ha="center",
        color="white",
        fontsize=10,
        fontweight="bold",
    )
ax.axhline(
    native_five_x_line,
    color="#3f4b56",
    linestyle="--",
    linewidth=1,
    label="Native CP total-phase / 5 (different timer boundary)",
)
ax.set_xticks(x, names)
ax.set_ylabel("Sum of 30 fresh-server observations (seconds)")
ax.set_ylim(0, max(totals) + 24)
ax.legend(
    frameon=False,
    fontsize=8,
    loc="upper center",
    bbox_to_anchor=(0.5, -0.13),
    ncol=2,
)
ax.set_title("Lazy NGFF imports remove fresh-server startup work")
fig.savefig(HERE / "fresh_server_total_breakdown.png", dpi=180)
plt.close(fig)

ordered = sorted(
    control, key=lambda name: nonjob(candidate[name]) - nonjob(control[name])
)
deltas = [nonjob(candidate[name]) - nonjob(control[name]) for name in ordered]
fig, ax = plt.subplots(figsize=(10, 9), layout="constrained")
ax.barh(range(len(ordered)), deltas, color="#3a8c83")
ax.set_yticks(range(len(ordered)), ordered, fontsize=7.5)
ax.invert_yaxis()
ax.axvline(0, color="#2f3640", linewidth=0.8)
ax.set_xlabel("Candidate minus control non-job seconds (lower is faster)")
ax.set_title("All 30 fresh-server cases spend less time outside jobs")
fig.savefig(HERE / "per_case_nonjob_delta.png", dpi=180)
plt.close(fig)
