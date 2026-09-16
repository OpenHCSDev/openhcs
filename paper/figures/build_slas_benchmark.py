"""Render the manuscript benchmark panel from the archived May 13 tables.

Run from any directory. Outputs are derived; input measurements are never edited.
The native wound-healing timing is unresolved and omitted from speed comparisons.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LogNorm
from matplotlib.lines import Line2D
from matplotlib.patches import Patch
import numpy as np
import pandas as pd

ROOT = Path(__file__).resolve().parents[2]
DEFAULT_DATA = (
    ROOT / "benchmark/results/labmeeting_20260513/official30_well_throughput/data"
)
DEFAULT_OUTPUT = Path(__file__).resolve().parent / "slas"
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


def load_tables(
    data_dir: Path,
) -> tuple[pd.DataFrame, pd.DataFrame, pd.DataFrame]:
    single = pd.read_csv(data_dir / SOURCES[0])
    scaled = pd.concat([pd.read_csv(data_dir / name) for name in SOURCES[1:3]])
    core = pd.read_csv(data_dir / SOURCES[3])
    if len(single) != 30 or single.case_name.duplicated().any():
        raise ValueError("Expected the archived 30 distinct benchmark workflows")
    if not ((single.n == 1) & (single.equivalent_count == 1)).all():
        raise ValueError("Archived repetition/equivalence counts changed")
    if not (single.min_parity_accuracy == 1).all():
        raise ValueError("Archived equivalence summary changed")
    if scaled.duplicated(["case_name", "worker_count", "well_count"]).any():
        raise ValueError("Ambiguous throughput observations")
    if not (
        (scaled.status == "success") & (scaled.successful_wells == scaled.well_count)
    ).all():
        raise ValueError("Incomplete throughput measurements require explicit review")
    if not (
        (core.status == "success") & (core.successful_wells == core.well_count)
    ).all():
        raise ValueError("Incomplete core-scaling measurements require explicit review")
    return single, scaled, core


def _case_jitter(case_names: pd.Series, width: float = 0.15) -> np.ndarray:
    """Return stable horizontal offsets derived from workflow identity."""
    return np.asarray(
        [
            (
                int.from_bytes(hashlib.sha256(name.encode("utf-8")).digest()[:8], "big")
                / (2**64 - 1)
                - 0.5
            )
            * 2
            * width
            for name in case_names
        ]
    )


def _distribution_panel(
    axis,
    frame: pd.DataFrame,
    *,
    condition: str,
    value: str,
    conditions: tuple[int, ...],
    color: str,
    title: str,
    xlabel: str,
    ylabel: str,
    logarithmic: bool,
    annotation_unit: str,
) -> None:
    """Show every workflow with its interquartile range and median."""
    for position, condition_value in enumerate(conditions, start=1):
        group = frame[frame[condition] == condition_value].sort_values("case_name")
        values = group[value].to_numpy(dtype=float)
        if len(values) != 30:
            raise ValueError(
                f"Expected 30 workflows for {condition}={condition_value}, got {len(values)}"
            )
        minimum, first_quartile, median, third_quartile, maximum = np.quantile(
            values, (0, 0.25, 0.5, 0.75, 1)
        )
        axis.vlines(position, minimum, maximum, color=color, linewidth=1.0, alpha=0.8)
        axis.bar(
            position,
            third_quartile - first_quartile,
            bottom=first_quartile,
            width=0.56,
            color=color,
            alpha=0.28,
            edgecolor=color,
            linewidth=1.0,
        )
        axis.hlines(
            median,
            position - 0.28,
            position + 0.28,
            color="#202020",
            linewidth=2.0,
            zorder=4,
        )
        axis.scatter(
            position + _case_jitter(group.case_name),
            values,
            s=22,
            facecolor=color,
            edgecolor="#202020",
            linewidth=0.35,
            alpha=0.72,
            zorder=3,
        )
        axis.annotate(
            f"{median:.2f}{annotation_unit}",
            xy=(position, median),
            xytext=(0, 5),
            textcoords="offset points",
            color=color,
            fontsize=8,
            fontweight="bold",
            ha="center",
            va="bottom",
            zorder=5,
            bbox={"facecolor": "white", "edgecolor": "none", "alpha": 0.78, "pad": 0.6},
        )
    if logarithmic:
        axis.set_yscale("log")
    axis.set(
        xticks=np.arange(1, len(conditions) + 1),
        xticklabels=[str(item) for item in conditions],
        xlabel=xlabel,
        ylabel=ylabel,
        title=title,
    )
    axis.grid(axis="y", alpha=0.22, linewidth=0.6)
    axis.set_axisbelow(True)


def _workflow_heatmaps(
    throughput: pd.DataFrame,
    memory: pd.DataFrame,
):
    """Render a supplementary workflow-by-condition view of the same records."""
    throughput_table = throughput.pivot(
        index="case_name",
        columns="worker_count",
        values="completed_wells_per_execution_second",
    )
    memory_table = memory.pivot(
        index="case_name", columns="wells_per_worker", values="peak_gib"
    )
    workflow_order = tuple(
        throughput_table.median(axis=1).sort_values(ascending=False).index
    )
    throughput_table = throughput_table.loc[list(workflow_order)]
    memory_table = memory_table.loc[list(workflow_order)]
    if throughput_table.isna().any().any() or memory_table.isna().any().any():
        raise ValueError("Supplementary heatmaps require complete workflow matrices")

    figure, axes = plt.subplots(
        1,
        2,
        figsize=(10.2, 10.0),
        gridspec_kw={"width_ratios": (1.0, 1.45)},
        layout="constrained",
    )
    throughput_image = axes[0].imshow(
        throughput_table.to_numpy(),
        aspect="auto",
        cmap="Blues",
        norm=LogNorm(
            vmin=float(throughput_table.to_numpy().min()),
            vmax=float(throughput_table.to_numpy().max()),
        ),
    )
    axes[0].set(
        title="A  Throughput by workflow",
        xlabel="OpenHCS workers\n(4 assignments per worker)",
        xticks=np.arange(len(throughput_table.columns)),
        xticklabels=[str(item) for item in throughput_table.columns],
        yticks=np.arange(len(workflow_order)),
        yticklabels=workflow_order,
    )
    figure.colorbar(
        throughput_image,
        ax=axes[0],
        label="Completed assignments per execution second",
        shrink=0.55,
    )

    memory_image = axes[1].imshow(
        memory_table.to_numpy(), aspect="auto", cmap="Oranges"
    )
    axes[1].set(
        title="B  Peak RAM by workflow",
        xlabel="Assignments per worker (4 workers)",
        xticks=np.arange(len(memory_table.columns)),
        xticklabels=[str(item) for item in memory_table.columns],
        yticks=np.arange(len(workflow_order)),
        yticklabels=[],
    )
    figure.colorbar(memory_image, ax=axes[1], label="Peak RAM (GiB)", shrink=0.55)
    for axis in axes:
        axis.tick_params(axis="y", labelsize=7)
    figure.suptitle(
        "Per-workflow measurements underlying the aggregate benchmark",
        fontsize=13,
        fontweight="bold",
    )
    return figure


def build(data_dir: Path = DEFAULT_DATA, output_dir: Path = DEFAULT_OUTPUT) -> None:
    data_dir = data_dir.resolve()
    output_dir = output_dir.resolve()
    single, scaled, core = load_tables(data_dir)
    timed = single[single.case_name != UNRESOLVED_NATIVE_TIMING].copy()
    timed["execution_phase_ratio"] = (
        timed.median_native_execution_seconds / timed.median_openhcs_execution_seconds
    )
    timed["phase_sum_ratio"] = (
        timed.median_native_total_phase_seconds
        / timed.median_openhcs_total_phase_seconds
    )
    np.testing.assert_allclose(timed.execution_phase_ratio, timed.median_speedup)
    np.testing.assert_allclose(timed.phase_sum_ratio, timed.median_total_phase_speedup)
    scaling = core[
        (core.case_name != UNRESOLVED_NATIVE_TIMING) & (core.worker_count > 1)
    ].copy()
    if not (scaling.well_count == 4 * scaling.worker_count).all():
        raise ValueError("Core comparison requires four wells per worker")
    scaling["projected_phase_ratio"] = (
        scaling.native_single_sample_execution_seconds
        * scaling.well_count
        / scaling.execute_seconds
    )
    np.testing.assert_allclose(
        scaling.projected_phase_ratio, scaling.projected_execution_speedup
    )
    throughput = core[core.worker_count > 1].copy()
    if not (throughput.well_count == 4 * throughput.worker_count).all():
        raise ValueError("Throughput panel requires four wells per worker")
    if not (throughput.execute_seconds > 0).all():
        raise ValueError("Throughput panel requires positive execution durations")
    throughput["completed_wells_per_execution_second"] = (
        throughput.successful_wells / throughput.execute_seconds
    )
    np.testing.assert_allclose(
        throughput.completed_wells_per_execution_second, throughput.wells_per_second
    )
    memory = pd.concat(
        [scaled[scaled.worker_count == 4], core[core.worker_count == 4]]
    ).copy()
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

    output_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.size": 10.5,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "svg.fonttype": "none",
        }
    )
    historical_figure, historical_axes = plt.subplots(
        1, 2, figsize=(8, 3.5), layout="constrained"
    )
    fig, axes = plt.subplots(1, 2, figsize=(8.8, 4.2), layout="constrained")
    blue, orange, grey = "#247BA0", "#C56B29", "#6B7280"
    a, b = historical_axes
    c, d = axes

    a.scatter(
        timed.median_native_execution_seconds,
        timed.median_openhcs_execution_seconds,
        color=blue,
        s=28,
    )
    times = timed[
        ["median_native_execution_seconds", "median_openhcs_execution_seconds"]
    ].to_numpy()
    limits = (
        10 ** np.floor(np.log10(times.min())),
        10 ** np.ceil(np.log10(times.max())),
    )
    a.plot(
        limits,
        limits,
        linestyle="--",
        color=grey,
        linewidth=1,
        label="Equal recorded duration",
    )
    a.set(
        xscale="log",
        yscale="log",
        xlim=limits,
        ylim=limits,
        xlabel="Native CellProfiler command (s)\nIncludes process startup",
        ylabel="Prepared OpenHCS execution (s)",
        title="A  Different timing boundaries",
    )
    a.legend(frameon=False, loc="upper left", fontsize=10)

    ordered = timed.sort_values("execution_phase_ratio")
    positions = np.arange(1, len(ordered) + 1)
    b.scatter(
        positions,
        ordered.execution_phase_ratio,
        color=blue,
        s=20,
        label="Execution phases",
    )
    b.scatter(
        positions,
        ordered.phase_sum_ratio,
        color=orange,
        marker="x",
        s=22,
        label="Summed phases",
    )
    b.axhline(1, color=grey, linestyle="--", linewidth=1)
    b.set(
        yscale="log",
        xlabel="Workflow rank by phase-time ratio",
        ylabel="Native CP time / OpenHCS time",
        title="B  Archived phase-time ratios",
    )
    b.legend(frameon=False, fontsize=10)

    _distribution_panel(
        c,
        throughput,
        condition="worker_count",
        value="completed_wells_per_execution_second",
        conditions=tuple(sorted(throughput.worker_count.unique())),
        color=blue,
        title="A  Throughput across workflows",
        xlabel="OpenHCS workers\n(4 assignments per worker)",
        ylabel="Completed assignments per execution second",
        logarithmic=True,
        annotation_unit="",
    )
    _distribution_panel(
        d,
        memory,
        condition="wells_per_worker",
        value="peak_gib",
        conditions=tuple(sorted(memory.wells_per_worker.unique())),
        color=orange,
        title="B  Peak memory across workflows",
        xlabel="Assignments per worker\n(4 workers)",
        ylabel="Peak process-tree RAM (GiB)",
        logarithmic=False,
        annotation_unit="",
    )
    d.set_ylim(bottom=0)
    fig.legend(
        handles=(
            Line2D(
                (),
                (),
                marker="o",
                linestyle="none",
                markerfacecolor="#6B7280",
                markeredgecolor="#202020",
                markersize=5,
                label="One workflow",
            ),
            Patch(
                facecolor="#6B7280",
                edgecolor="#6B7280",
                alpha=0.28,
                label="Interquartile range",
            ),
            Line2D((), (), color="#202020", linewidth=2, label="Median"),
        ),
        loc="outside lower center",
        ncol=3,
        frameon=False,
        fontsize=9,
    )
    for axis in historical_axes:
        axis.grid(axis="y", alpha=0.18, linewidth=0.5)
        axis.set_axisbelow(True)
    fig.suptitle(
        "Measured execution across 30 imported workflows",
        fontsize=12,
        fontweight="bold",
    )
    historical_figure.suptitle(
        "Archived single-sample observations: unequal timing boundaries", fontsize=12
    )
    detail_figure = _workflow_heatmaps(throughput, memory)
    for plot, stem in (
        (fig, "figure2_benchmarks"),
        (detail_figure, "figure2_benchmarks_by_workflow"),
        (historical_figure, "figure2_historical_timings"),
    ):
        for suffix in ("png", "pdf", "svg"):
            plot.savefig(output_dir / f"{stem}.{suffix}", dpi=300)
        plt.close(plot)

    for name, frame in (
        ("timed_workflows", timed),
        ("scaling_comparisons", scaling),
        ("throughput_observations", throughput),
        ("memory_observations", memory),
    ):
        frame.to_csv(
            output_dir / f"figure2_{name}.csv", index=False, quoting=csv.QUOTE_MINIMAL
        )
    outputs = sorted(output_dir.glob("figure2_*"))
    outputs = [path for path in outputs if path.suffix != ".json"]
    receipt = {
        "source_sha256": {
            (
                str((data_dir / name).relative_to(ROOT))
                if (data_dir / name).is_relative_to(ROOT)
                else str(data_dir / name)
            ): sha256(data_dir / name)
            for name in SOURCES
        },
        "generator_sha256": sha256(Path(__file__)),
        "output_sha256": {path.name: sha256(path) for path in outputs},
        "unresolved_native_timing_excluded_from_speed_comparisons": UNRESOLVED_NATIVE_TIMING,
        "single_sample_workflows": len(timed),
        "repetitions_per_single_sample_row": sorted(single.n.unique().tolist()),
        "memory_workflows": memory.case_name.nunique(),
        "throughput_workflows": throughput.case_name.nunique(),
        "throughput_panel": "Measured completed assignments divided by execution seconds, four assignments per worker; points show all 30 workflows, boxes show interquartile ranges, and lines show medians",
        "supplementary_workflow_panel": "The same throughput and memory observations arranged by workflow and condition; workflow order is descending median throughput",
        "memory_conversion": "Source collector reports RSS bytes / 1024**2; divide by 1024 for GiB",
        "interpretation": "Historical phase ratios with different timing boundaries: native command includes startup, OpenHCS execution follows preparation, and phase sums include different work. Native persistent or parallel throughput was not measured.",
    }
    (output_dir / "figure2_provenance.json").write_text(
        json.dumps(receipt, indent=2) + "\n"
    )
    print(f"Rendered benchmark panels and plotted observations to {output_dir}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, default=DEFAULT_DATA)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    arguments = parser.parse_args()
    build(arguments.data_dir, arguments.output_dir)
