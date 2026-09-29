"""Regenerate the fresh-server registry-lookup comparison figures."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent


def rows(path: Path) -> dict[str, dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return {row["case_name"]: row for row in csv.DictReader(handle)}


def summed(dataset: dict[str, dict[str, str]], column: str) -> float:
    return sum(float(row[column]) for row in dataset.values())


control = rows(HERE / "control.csv")
lookup_only = rows(HERE / "lookup_only.csv")
candidate = rows(HERE / "candidate.csv")
scoped = rows(HERE / "scoped.csv")
native = rows(HERE.parent / "perf_lazy_catalog_20260929" / "native_cp_summary.csv")
assert control.keys() == lookup_only.keys() == candidate.keys() == scoped.keys()

observations = (control, lookup_only, candidate, scoped)
compile_time = [summed(dataset, "compile_seconds") for dataset in observations]
execute_time = [summed(dataset, "execute_seconds") for dataset in observations]
totals = [summed(dataset, "total_seconds") for dataset in observations]
other_time = [
    total - compile - execute
    for total, compile, execute in zip(totals, compile_time, execute_time, strict=True)
]
native_five_x_line = (
    sum(float(row["median_native_total_phase_seconds"]) for row in native.values()) / 5
)

fig, ax = plt.subplots(figsize=(9, 5), layout="constrained")
x = np.arange(4)
ax.bar(x, compile_time, label="Server compilation", color="#697b8c")
ax.bar(x, execute_time, bottom=compile_time, label="Server execution", color="#d87a57")
ax.bar(
    x,
    other_time,
    bottom=np.array(compile_time) + np.array(execute_time),
    label="Other measured time",
    color="#3a8c83",
)
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
ax.set_xticks(x, ("Control", "Exact lookup", "Recorded owner", "Scoped lookup"))
ax.set_ylabel("Sum of 30 fresh-server observations (seconds)")
ax.set_ylim(0, max(totals) + 25)
ax.set_title("Exact owners avoid cold catalog scans in compilation and execution")
ax.legend(
    frameon=False, fontsize=8, loc="upper center", bbox_to_anchor=(0.5, -0.13), ncol=2
)
fig.savefig(HERE / "fresh_server_total_breakdown.png", dpi=180)
plt.close(fig)

ordered = sorted(
    control,
    key=lambda name: float(scoped[name]["compile_seconds"])
    - float(control[name]["compile_seconds"]),
)
compile_deltas = [
    float(scoped[name]["compile_seconds"]) - float(control[name]["compile_seconds"])
    for name in ordered
]
execute_deltas = [
    float(scoped[name]["execute_seconds"]) - float(control[name]["execute_seconds"])
    for name in ordered
]
fig, ax = plt.subplots(figsize=(11, 10), layout="constrained")
y = np.arange(len(ordered))
ax.barh(y - 0.19, compile_deltas, height=0.38, label="Compilation", color="#3a8c83")
ax.barh(y + 0.19, execute_deltas, height=0.38, label="Execution", color="#d87a57")
ax.set_yticks(y, ordered, fontsize=7)
ax.invert_yaxis()
ax.axvline(0, color="#2f3640", linewidth=0.8)
ax.set_xlabel("Candidate minus control seconds per case (lower is faster)")
ax.set_title("Compilation falls; timed relationship discovery is removed")
ax.legend(frameon=False, loc="lower right")
fig.savefig(HERE / "per_case_phase_deltas.png", dpi=180)
plt.close(fig)
