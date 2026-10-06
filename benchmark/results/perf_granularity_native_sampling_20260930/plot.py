"""Export the recorded paired granularity performance and CP comparison."""

import json
from pathlib import Path
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    data = json.loads((HERE / "analysis.json").read_text())
    modes = ("1w", "16w")
    figure, axes = plt.subplots(1, 2, figsize=(11, 5))
    colors = {"control": "#718096", "candidate": "#168b78"}
    x = np.arange(2)
    for offset, variant in ((-0.18, "control"), (0.18, "candidate")):
        values = [data["modes"][mode][variant]["median"]["execution"] for mode in modes]
        bars = axes[0].bar(
            x + offset, values, 0.34, label=f"OpenHCS {variant}", color=colors[variant]
        )
        axes[0].bar_label(bars, fmt="%.2fs", padding=3)
    axes[0].set_xticks(x, ("1 well / inline", "16 wells / 4 fork workers"))
    axes[0].set_ylabel("Execution wall time (seconds)")
    axes[0].set_ylim(
        0, max(data["modes"]["16w"]["control"]["median"]["execution"] * 1.25, 1)
    )
    axes[0].legend(frameon=False)
    ratios = [data["modes"][mode]["native_execution_ratio"] for mode in modes]
    bars = axes[1].bar(x, ratios, 0.6, color=colors["candidate"])
    axes[1].bar_label(bars, fmt="%.2f×", padding=3)
    axes[1].set_xticks(x, ("1 well / 1 process", "16 wells / 4 processes"))
    axes[1].set_ylabel("Native CellProfiler time / OpenHCS execution")
    axes[1].set_ylim(0, max(ratios) * 1.25)
    figure.suptitle("Native granularity sampling: isolated, warmed-cache measurements")
    figure.text(
        0.5,
        0.02,
        "OpenHCS: two observations per variant; 16-well wall gain inconclusive.\nCP: earlier physical analysis timings; warmup/startup excluded. Repeated source pixels; timing scopes differ.",
        ha="center",
        fontsize=9,
    )
    figure.tight_layout(rect=(0, 0.10, 1, 0.93))
    for suffix in ("png", "svg"):
        path = HERE / f"measured_granularity_scaling.{suffix}"
        figure.savefig(path, dpi=170)
        if suffix == "svg":
            path.write_text(
                "\n".join(line.rstrip() for line in path.read_text().splitlines())
                + "\n"
            )
    plt.close(figure)


if __name__ == "__main__":
    main()
