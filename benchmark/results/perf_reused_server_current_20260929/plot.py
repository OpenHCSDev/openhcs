"""Render fresh-versus-reused OpenHCS benchmark phase sums."""

from __future__ import annotations

import csv
from pathlib import Path

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def _phase_sums(path: Path) -> tuple[tuple[str, ...], tuple[float, float, float]]:
    with path.open(newline="") as stream:
        rows = tuple(csv.DictReader(stream))
    assert len(rows) == 30 and all(row["status"] == "success" for row in rows)
    cases = tuple(row["case_name"] for row in rows)
    assert len(set(cases)) == 30
    execution = sum(float(row["execute_seconds"]) for row in rows)
    compilation = sum(float(row["compile_seconds"]) for row in rows)
    other = sum(
        float(row["total_seconds"])
        - float(row["execute_seconds"])
        - float(row["compile_seconds"])
        for row in rows
    )
    return cases, (execution, compilation, other)


def main() -> None:
    fresh_cases, fresh = _phase_sums(ROOT / "fresh.csv")
    reused_cases, reused = _phase_sums(ROOT / "reused.csv")
    assert fresh_cases == reused_cases
    with (ROOT / "wall_times.csv").open(newline="") as stream:
        wall_rows = tuple(csv.DictReader(stream))
    assert tuple(row["server_lifecycle"] for row in wall_rows) == (
        "fresh-per-observation",
        "reused-per-sweep",
    )
    assert all(row["exit_code"] == "0" for row in wall_rows)
    fresh_wall, reused_wall = (float(row["elapsed_seconds"]) for row in wall_rows)
    fig, axis = plt.subplots(figsize=(7.8, 5.1))
    labels = ("Fresh per case", "One reused server")
    bottom = [0.0, 0.0]
    for index, (name, color) in enumerate(
        (
            ("Server execution", "#138579"),
            ("Compilation", "#b46239"),
            ("Other per-case work", "#677687"),
        )
    ):
        values = (fresh[index], reused[index])
        bars = axis.bar(labels, values, bottom=bottom, color=color, label=name)
        axis.bar_label(
            bars,
            labels=[f"{value:.1f}s" for value in values],
            label_type="center",
            color="white",
            fontsize=10,
        )
        bottom = [start + value for start, value in zip(bottom, values, strict=True)]
    for position, total in enumerate(bottom):
        axis.text(position, total + 3, f"{total:.1f}s", ha="center", fontsize=11)
    axis.set(
        title="Official 30 cases: per-observation phase sums",
        ylabel="Summed seconds",
        ylim=(0, max(bottom) * 1.13),
    )
    axis.spines[["top", "right"]].set_visible(False)
    axis.legend(frameon=False)
    fig.text(
        0.5,
        0.02,
        "Reused per-case totals exclude one-time server startup. "
        f"Whole CLI wall time: {fresh_wall:.1f} s fresh, "
        f"{reused_wall:.1f} s reused.",
        ha="center",
        fontsize=8,
        color="#555555",
    )
    fig.tight_layout(rect=(0, 0.05, 1, 1))
    fig.savefig(ROOT / "fresh_vs_reused_phase_sums.png", dpi=180)


if __name__ == "__main__":
    main()
