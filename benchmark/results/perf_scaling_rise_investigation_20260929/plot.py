"""Rebuild native scaling using uncontaminated OpenHCS repetitions."""

import json
from pathlib import Path

import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent


def main() -> None:
    rows = json.loads((ROOT / "measured_ratios.json").read_text())
    wells = tuple(row["wells"] for row in rows)
    figure, (timing, ratio) = plt.subplots(1, 2, figsize=(10.5, 4.5))
    for metric, label, color, style in (
        ("native_warm_invocation_seconds", "Native CP warm invocation", "#b46239", "-"),
        ("openhcs_execution_seconds", "OpenHCS execution", "#138579", "-"),
        ("openhcs_total_seconds", "OpenHCS fresh-server total", "#677687", "--"),
    ):
        timing.plot(
            wells,
            [row[metric] for row in rows],
            style,
            marker="o",
            color=color,
            label=label,
        )
    timing.set(
        yscale="log",
        ylabel="Seconds",
        title="Measured timing scopes",
        xlabel="Synthetic wells",
        xticks=wells,
    )
    timing.legend(fontsize=8)
    timing.grid(axis="y", alpha=0.2)
    values = tuple(row["execution_ratio"] for row in rows)
    ratio.bar(range(len(rows)), values, color="#138579", width=0.6)
    for index, value in enumerate(values):
        ratio.text(index, value + 0.08, f"{value:.2f}×", ha="center")
    ratio.axhline(1, color="#677687", linestyle="--", linewidth=1)
    ratio.set(
        title="Native / OpenHCS execution",
        ylabel="Ratio",
        xticks=range(len(rows)),
        xticklabels=("1 well / 1 lane", "16 wells / 4 lanes"),
        ylim=(0, 4.5),
    )
    ratio.grid(axis="y", alpha=0.2)
    figure.suptitle(
        "ImagingFlow: clean OpenHCS repeats relative to native CellProfiler"
    )
    figure.text(
        0.5,
        0.025,
        "OpenHCS: one 1w observation; median of two clean 16w repeats. CP excludes startup/warmup.\nRepeated pixels; native 16w reports recovered after controller loss (see report).",
        ha="center",
        fontsize=8,
    )
    figure.tight_layout(rect=(0, 0.085, 1, 0.95))
    figure.savefig(ROOT / "measured_native_scaling.png", dpi=180)
    svg = ROOT / "measured_native_scaling.svg"
    figure.savefig(svg)
    svg.write_text(
        "\n".join(line.rstrip() for line in svg.read_text().splitlines()) + "\n"
    )


if __name__ == "__main__":
    main()
