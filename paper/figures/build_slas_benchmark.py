"""Render the manuscript benchmark panel from the archived May 13 tables.

Run from any directory. Outputs are derived; input measurements are never edited.
The native wound-healing timing is unresolved and omitted from speed comparisons.
"""

from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
import pandas as pd


ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "benchmark/results/labmeeting_20260513/official30_well_throughput/data"
OUTPUT = Path(__file__).resolve().parent / "slas"
UNRESOLVED_NATIVE_TIMING = "ExampleWoundHealing"
SOURCES = (
    "single_process_summary.csv",
    "wells_per_core_2c3c4c.csv",
    "wells_per_core_4c_6wpc_8wpc.csv",
    "core_scaling_well_throughput.csv",
)


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def load_tables() -> tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    single = pd.read_csv(DATA / SOURCES[0])
    scaled = pd.concat([pd.read_csv(DATA / name) for name in SOURCES[1:3]])
    core = pd.read_csv(DATA / SOURCES[3])
    if len(single) != 30 or single.case_name.duplicated().any():
        raise ValueError("Expected the archived 30 distinct benchmark workflows")
    if not ((single.n == 1) & (single.equivalent_count == 1)).all():
        raise ValueError("Archived repetition/equivalence counts changed")
    if not (single.min_parity_accuracy == 1).all():
        raise ValueError("Archived equivalence summary changed")
    if scaled.duplicated(["case_name", "worker_count", "well_count"]).any():
        raise ValueError("Ambiguous throughput observations")
    if not ((scaled.status == "success") & (scaled.successful_wells == scaled.well_count)).all():
        raise ValueError("Incomplete throughput measurements require explicit review")
    if not ((core.status == "success") & (core.successful_wells == core.well_count)).all():
        raise ValueError("Incomplete core-scaling measurements require explicit review")
    return single, scaled, core


def build() -> None:
    single, scaled, core = load_tables()
    timed = single[single.case_name != UNRESOLVED_NATIVE_TIMING].copy()
    timed["execution_phase_ratio"] = timed.median_native_execution_seconds / timed.median_openhcs_execution_seconds
    timed["phase_sum_ratio"] = timed.median_native_total_phase_seconds / timed.median_openhcs_total_phase_seconds
    np.testing.assert_allclose(timed.execution_phase_ratio, timed.median_speedup)
    np.testing.assert_allclose(timed.phase_sum_ratio, timed.median_total_phase_speedup)
    scaling = core[(core.case_name != UNRESOLVED_NATIVE_TIMING) & (core.worker_count > 1)].copy()
    if not (scaling.well_count == 4 * scaling.worker_count).all():
        raise ValueError("Core comparison requires four wells per worker")
    scaling["projected_phase_ratio"] = scaling.native_single_sample_execution_seconds * scaling.well_count / scaling.execute_seconds
    np.testing.assert_allclose(scaling.projected_phase_ratio, scaling.projected_execution_speedup)
    throughput = core[core.worker_count > 1].copy()
    if not (throughput.well_count == 4 * throughput.worker_count).all():
        raise ValueError("Throughput panel requires four wells per worker")
    if not (throughput.execute_seconds > 0).all():
        raise ValueError("Throughput panel requires positive execution durations")
    throughput["completed_wells_per_execution_second"] = throughput.successful_wells / throughput.execute_seconds
    np.testing.assert_allclose(throughput.completed_wells_per_execution_second, throughput.wells_per_second)
    memory = pd.concat([scaled[scaled.worker_count == 4], core[core.worker_count == 4]]).copy()
    if memory.duplicated(["case_name", "well_count"]).any():
        raise ValueError("Duplicate memory observations")
    memory["wells_per_worker"] = memory.well_count // memory.worker_count
    memory["peak_gib"] = memory.peak_memory_mb / 1024
    expected = set(timed.case_name)
    for _, group in scaling.groupby("worker_count"):
        if set(group.case_name) != expected:
            raise ValueError("Incomplete per-worker comparison population")
    for _, group in memory.groupby("wells_per_worker"):
        if set(group.case_name) != set(single.case_name):
            raise ValueError("Incomplete memory comparison population")
    for _, group in throughput.groupby("worker_count"):
        if set(group.case_name) != set(single.case_name):
            raise ValueError("Incomplete measured throughput population")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 10.5, "axes.spines.top": False, "axes.spines.right": False, "svg.fonttype": "none"})
    historical_figure, historical_axes = plt.subplots(1, 2, figsize=(8, 3.5), layout="constrained")
    fig, axes = plt.subplots(1, 2, figsize=(8, 3.5), layout="constrained")
    blue, orange, grey = "#247BA0", "#C56B29", "#6B7280"
    a, b = historical_axes
    c, d = axes

    a.scatter(timed.median_native_execution_seconds, timed.median_openhcs_execution_seconds, color=blue, s=28)
    times = timed[["median_native_execution_seconds", "median_openhcs_execution_seconds"]].to_numpy()
    limits = (10 ** np.floor(np.log10(times.min())), 10 ** np.ceil(np.log10(times.max())))
    a.plot(limits, limits, linestyle="--", color=grey, linewidth=1, label="Equal recorded duration")
    a.set(xscale="log", yscale="log", xlim=limits, ylim=limits, xlabel="Native CellProfiler command (s)\nIncludes process startup", ylabel="Prepared OpenHCS execution (s)", title="A  Different timing boundaries")
    a.legend(frameon=False, loc="upper left", fontsize=10)

    ordered = timed.sort_values("execution_phase_ratio")
    positions = np.arange(1, len(ordered) + 1)
    b.scatter(positions, ordered.execution_phase_ratio, color=blue, s=20, label="Execution phases")
    b.scatter(positions, ordered.phase_sum_ratio, color=orange, marker="x", s=22, label="Summed phases")
    b.axhline(1, color=grey, linestyle="--", linewidth=1)
    b.set(yscale="log", xlabel="Workflow rank by phase-time ratio", ylabel="Native CP time / OpenHCS time", title="B  Archived phase-time ratios")
    b.legend(frameon=False, fontsize=10)

    for _, group in throughput.groupby("case_name"):
        group = group.sort_values("worker_count")
        c.plot(group.worker_count, group.completed_wells_per_execution_second, color=blue, alpha=.15, linewidth=.7)
    medians = throughput.groupby("worker_count").completed_wells_per_execution_second.median()
    c.plot(medians.index, medians, color=blue, marker="o", linewidth=2, label="Median across 30 workflows")
    c.set(yscale="log", xticks=sorted(throughput.worker_count.unique()), xlabel="OpenHCS workers\n(4 wells per worker)", ylabel="Completed wells / execution second", title="A  Measured OpenHCS throughput")
    c.legend(frameon=False, fontsize=10)

    for _, group in memory.groupby("case_name"):
        group = group.sort_values("wells_per_worker")
        d.plot(group.wells_per_worker, group.peak_gib, color=orange, alpha=.18, linewidth=.7)
    medians = memory.groupby("wells_per_worker").peak_gib.median()
    d.plot(medians.index, medians, color=orange, marker="o", linewidth=2, label="Median across 30 workflows")
    d.set(ylim=(0, None), xticks=sorted(memory.wells_per_worker.unique()), xlabel="Wells per worker\n(4 workers)", ylabel="Peak RAM (GiB)", title="B  Memory use")
    d.legend(frameon=False, fontsize=10)
    for axis in (*historical_axes, *axes):
        axis.grid(axis="y", alpha=.18, linewidth=.5)
        axis.set_axisbelow(True)
    fig.suptitle("Persistent-worker execution across 30 workflows", fontsize=12)
    historical_figure.suptitle("Archived single-sample observations: unequal timing boundaries", fontsize=12)
    for plot, stem in ((fig, "figure2_benchmarks"), (historical_figure, "figure2_historical_timings")):
        for suffix in ("png", "pdf", "svg"):
            plot.savefig(OUTPUT / f"{stem}.{suffix}", dpi=300)
        plt.close(plot)

    for name, frame in (("timed_workflows", timed), ("scaling_comparisons", scaling), ("throughput_observations", throughput), ("memory_observations", memory)):
        frame.to_csv(OUTPUT / f"figure2_{name}.csv", index=False, quoting=csv.QUOTE_MINIMAL)
    outputs = sorted(OUTPUT.glob("figure2_*"))
    outputs = [path for path in outputs if path.suffix != ".json"]
    receipt = {
        "source_sha256": {str((DATA / name).relative_to(ROOT)): sha256(DATA / name) for name in SOURCES},
        "generator_sha256": sha256(Path(__file__)),
        "output_sha256": {path.name: sha256(path) for path in outputs},
        "unresolved_native_timing_excluded_from_speed_comparisons": UNRESOLVED_NATIVE_TIMING,
        "single_sample_workflows": len(timed),
        "repetitions_per_single_sample_row": sorted(single.n.unique().tolist()),
        "memory_workflows": memory.case_name.nunique(),
        "throughput_workflows": throughput.case_name.nunique(),
        "throughput_panel": "Measured completed wells divided by execution seconds, four wells per worker; historical native projections retained separately but not plotted",
        "memory_conversion": "Source collector reports RSS bytes / 1024**2; divide by 1024 for GiB",
        "interpretation": "Historical phase ratios with different timing boundaries: native command includes startup, OpenHCS execution follows preparation, and phase sums include different work. Native persistent or parallel throughput was not measured.",
    }
    (OUTPUT / "figure2_provenance.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Rendered benchmark panels and plotted observations to {OUTPUT}")


if __name__ == "__main__":
    build()
