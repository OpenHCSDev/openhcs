"""Plot measured well-level drug effects; never process or tune images."""

import argparse
import json
from math import isclose
from pathlib import Path
from statistics import mean, stdev
from textwrap import fill

from build_slas_visual_story import BLUE, TEAL, INK, MUTED, ROOT, FigureSheet
from compare_personal_neurite import DEFAULT_METRICS, METRICS, endpoint_declarations, read_rows


class NeuriteEffectFigure(FigureSheet):
    """One well table supplies points for every requested endpoint panel."""

    def __init__(self, tables: Path, *, stem: str, metrics=DEFAULT_METRICS):
        super().__init__(stem, "Neurite outgrowth: drug responses across methods", 2.0 * len(metrics) + 1.4)
        self.source(Path(__file__))
        self.source(ROOT / "paper/figures/compare_personal_neurite.py")
        for name in ("joined_wells.csv", "treatment_effects.csv", "source_evidence.json"):
            self.source(tables / name)
        wells = read_rows(tables / "joined_wells.csv")
        effects = read_rows(tables / "treatment_effects.csv")
        evidence = json.loads((tables / "source_evidence.json").read_text())
        self.text(3, 91, evidence["protocol_figure_label"], size=11, color=MUTED)
        declarations = endpoint_declarations()
        conditions = tuple(sorted({item["condition"] for item in effects}))
        limits = {}
        for metric in metrics:
            extents = [float(group[f"{method}_fold_change"]) + sign *
                       float(group[f"{method}_treatment_sd"]) / float(group[f"{method}_control_mean"])
                       for group in effects if group["metric"] == metric
                       for method in ("metaxpress", "openhcs") for sign in (-1, 1)]
            lower, upper = min(extents), max(extents)
            padding = (upper - lower) * 0.08
            limits[metric] = (lower - padding, upper + padding)
        for column, condition in enumerate(conditions):
            for row, metric in enumerate(metrics):
                left = .14 + column * (.90 / len(conditions))
                bottom = .12 + (len(metrics) - 1 - row) * (.75 / len(metrics))
                height = .55 / len(metrics)
                axis = self.figure.add_axes((left, bottom, .68 / len(conditions), height))
                letter = chr(65 + row * len(conditions) + column)
                if row == 0:
                    self.panel(letter, condition, left * 100, (bottom + height + .02) * 100)
                else:
                    axis.text(.02, .98, letter, transform=axis.transAxes,
                              va="top", fontsize=14, weight="bold", color=BLUE)
                selected = sorted((item for item in effects
                                   if item["condition"] == condition and item["metric"] == metric),
                                  key=lambda item: float(item["dose_uM"]))
                if len(selected) != 5:
                    raise ValueError(f"Incomplete dose series: {condition}/{metric}")
                for method, prefix, color, offset, marker, label in (
                    ("metaxpress", "", BLUE, -0.13, "o", "MetaXpress"),
                    ("openhcs", "openhcs_", TEAL, 0.13, "s", "OpenHCS"),
                ):
                    positions, means = [], []
                    for index, group in enumerate(selected):
                        identities = set(group["treatment_wells"].split(";"))
                        drug = [item for item in wells
                                if item["plate"] == group["plate"] and item["well"] in identities]
                        baseline = float(group[f"{method}_control_mean"])
                        values = [float(item[prefix + metric]) / baseline for item in drug]
                        if len(values) != int(group["n_treatment"]) or len(values) < 2:
                            raise ValueError(f"Missing replicate: {condition}/{metric}/{group['dose_uM']}")
                        if not isclose(mean(values), float(group[f"{method}_fold_change"]), rel_tol=1e-10):
                            raise ValueError("Plot points disagree with the effect table")
                        position = index + offset
                        positions.append(position)
                        means.append(mean(values))
                        axis.errorbar(position, mean(values), yerr=stdev(values), color=color,
                                      fmt="_", markersize=11, capsize=3, linewidth=1.2, zorder=2)
                        axis.scatter((position - 0.035, position + 0.035), values,
                                     marker=marker, s=24, color=color, edgecolor="white",
                                     linewidth=0.5, zorder=3)
                    axis.plot(positions, means, color=color, linewidth=1.1, label=label, zorder=1)
                axis.axhline(1, color=MUTED, linewidth=0.8, linestyle="--", zorder=0)
                axis.set(xlim=(-0.5, 4.5), ylim=limits[metric],
                         ylabel=fill(declarations[metric].label, width=20), xlabel="Concentration (µM)")
                axis.set_xticks(range(5), [item["dose_uM"] for item in selected])
                axis.tick_params(labelsize=9, colors=INK)
                axis.spines[["top", "right"]].set_visible(False)
                axis.grid(axis="y", color="#e7ebef", linewidth=0.6)
                axis.set_axisbelow(True)
                if row == 0 and column == 0:
                    axis.legend(fontsize=9, frameon=False)
        self.text(3, 8, "Dots: two technical wells. Marks and whiskers: mean ± between-well SD, not confidence intervals.", size=10)
        self.text(3, 4.5, "Each curve uses its own zero-dose DMSO mean. Dose positions are equally spaced for display.", size=10)
        self.text(3, 1, "Within-method ratios compare response; they do not establish equivalent segmentation or absolute lengths.", size=10)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tables", type=Path, required=True)
    parser.add_argument("--stem", required=True)
    parser.add_argument("--metrics", nargs="+", choices=METRICS, default=DEFAULT_METRICS)
    args = parser.parse_args()
    NeuriteEffectFigure(args.tables.resolve(), stem=args.stem, metrics=tuple(args.metrics)).save()
