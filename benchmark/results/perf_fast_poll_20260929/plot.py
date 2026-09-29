"""Rebuild the fresh-server completion-poll comparison figure."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
BASELINE = HERE.parent / "perf_lazy_catalog_20260929" / "lazy_fresh.csv"
FAST = HERE / "fast_poll_well_throughput.csv"
WAITS = HERE / "wait_breakdown.csv"
NATIVE = HERE.parent / "perf_lazy_catalog_20260929" / "native_cp_summary.csv"


def read_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as file:
        return list(csv.DictReader(file))


def total(rows: list[dict[str, str]], column: str) -> float:
    return sum(float(row[column]) for row in rows)


def main() -> None:
    baseline = read_rows(BASELINE)
    fast = read_rows(FAST)
    waits = read_rows(WAITS)
    native = read_rows(NATIVE)
    assert {row["case_name"] for row in baseline} == {row["case_name"] for row in fast}
    assert len(baseline) == len(fast) == len(waits) == 30

    stacks = []
    for rows in (baseline, fast):
        compile_time = total(rows, "compile_seconds")
        execution_time = total(rows, "execute_seconds")
        other = total(rows, "total_seconds") - compile_time - execution_time
        stacks.append((compile_time, execution_time, other))

    native_total = total(native, "median_native_total_phase_seconds") / 5
    fig, (ax, slack_ax) = plt.subplots(
        1, 2, figsize=(11, 5), gridspec_kw={"width_ratios": [1.35, 1]}
    )
    colors = ("#6789a7", "#3a6f91", "#d19b59")
    labels = ("Server compilation", "Server execution", "Other measured time")
    for i, (components, title) in enumerate(
        zip(stacks, ("0.5 s polling", "0.05 s polling"), strict=True)
    ):
        bottom = 0.0
        for component, label, color in zip(components, labels, colors, strict=True):
            ax.bar(
                i,
                component,
                bottom=bottom,
                color=color,
                label=label if i == 0 else None,
            )
            bottom += component
        ax.text(i, bottom + 2, f"{bottom:.1f}s", ha="center", fontsize=10)
    ax.axhline(native_total, color="#665b83", linestyle="--", linewidth=1.5)
    ax.text(
        1.48,
        native_total - 13,
        f"Native CP / 5: {native_total:.1f}s",
        ha="right",
        fontsize=8,
    )
    ax.set_xticks([0, 1], ["0.5 s polling", "0.05 s polling"])
    ax.set_ylim(0, 320)
    ax.set_ylabel("Sum across 30 fresh-server observations (s)")
    ax.set_title("Total measured time")
    ax.legend(loc="lower center", bbox_to_anchor=(0.5, -0.25), ncol=3, fontsize=8)

    slack = [
        sum(
            float(row[f"{label}_wait_seconds"])
            - float(row[f"{label}_server_jobs_seconds"])
            for row in waits
        )
        for label in ("baseline", "fast")
    ]
    bars = slack_ax.bar([0, 1], slack, color=["#d19b59", "#3a6f91"], width=0.6)
    for bar, value in zip(bars, slack, strict=True):
        slack_ax.text(
            bar.get_x() + bar.get_width() / 2, value + 0.3, f"{value:.2f}s", ha="center"
        )
    slack_ax.set_xticks([0, 1], ["0.5 s polling", "0.05 s polling"])
    slack_ax.set_ylim(0, 16)
    slack_ax.set_ylabel("Client wait minus server job duration (s)")
    slack_ax.set_title("Completion-detection slack")
    fig.suptitle("Official30 CPU-only 1w_1t: ordinary compiled-pipeline waits")
    fig.tight_layout()
    fig.savefig(HERE / "polling_total_and_slack.png", dpi=180)
    plt.close(fig)


if __name__ == "__main__":
    main()
