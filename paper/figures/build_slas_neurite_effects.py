"""Plot measured well-level drug effects; never process or tune images."""

import argparse
import json
from math import isclose
from pathlib import Path
from statistics import mean, stdev
from textwrap import fill

from build_slas_visual_story import (
    BLUE,
    TEAL,
    ORANGE,
    PURPLE,
    INK,
    MUTED,
    ROOT,
    FigureSheet,
)
from compare_personal_neurite import (
    DEFAULT_METRICS,
    METRICS,
    endpoint_declarations,
    read_rows,
)


class NeuriteEffectFigure(FigureSheet):
    """Retained well tables supply every plotted method and author."""

    @staticmethod
    def cohort_tables(sheet: FigureSheet, cohort: Path):
        """Author identity comes from the frozen cohort record, not plot order."""
        record = cohort / "cohort.json"
        sheet.source(record)
        authors = json.loads(record.read_text())["authors"]
        return {author["label"]: cohort / author["tables"] for author in authors}

    def __init__(self, tables: Path, *, stem: str, metrics=DEFAULT_METRICS):
        super().__init__(
            stem,
            "Neurite outgrowth: drug responses across methods",
            2.0 * len(metrics) + 1.4,
        )
        protocol_label = self.draw_panels(self, tables, metrics=metrics)
        self.text(3, 91, protocol_label, size=11, color=MUTED)
        self.text(
            3,
            8,
            "Dots: two technical wells. Marks and whiskers: mean ± between-well SD, not confidence intervals.",
            size=10,
        )
        self.text(
            3,
            4.5,
            "Each curve uses its own zero-dose DMSO mean. Dose positions are equally spaced for display.",
            size=10,
        )
        self.text(
            3,
            1,
            "Concordant outgrowth responses have different measured magnitudes; neither method is ground truth.",
            size=10,
        )

    @staticmethod
    def draw_panels(
        sheet: FigureSheet,
        tables: Path | dict[str, Path],
        *,
        metrics=DEFAULT_METRICS,
        bounds=(0, 0, 100, 100),
        start_letter="A",
    ):
        """Draw measured panels directly into a standalone or composite sheet."""
        sheet.source(Path(__file__))
        sheet.source(ROOT / "paper/figures/compare_personal_neurite.py")
        table_sets = {"OpenHCS": tables} if isinstance(tables, Path) else tables
        datasets = []
        for label, directory in table_sets.items():
            for name in (
                "joined_wells.csv",
                "treatment_effects.csv",
                "source_evidence.json",
            ):
                sheet.source(directory / name)
            datasets.append(
                (
                    label,
                    read_rows(directory / "joined_wells.csv"),
                    read_rows(directory / "treatment_effects.csv"),
                    json.loads((directory / "source_evidence.json").read_text()),
                )
            )
        _, wells, effects, evidence = datasets[0]
        reference_columns = ("plate", "well", "condition", "nominal_dose_uM", *metrics)
        reference_rows = [
            {key: item[key] for key in reference_columns} for item in wells
        ]
        for _, other_wells, _, other_evidence in datasets[1:]:
            if (
                reference_rows
                != [
                    {key: item[key] for key in reference_columns}
                    for item in other_wells
                ]
                or evidence["aggregation_protocol"]
                != other_evidence["aggregation_protocol"]
            ):
                raise ValueError(
                    "Authors must use the same reference wells and aggregation protocol"
                )
        series = [("MetaXpress", wells, effects, "metaxpress", "", BLUE, "o")]
        colours = (TEAL, ORANGE, PURPLE)
        markers = ("s", "^", "D")
        for index, (label, author_wells, author_effects, _) in enumerate(datasets):
            series.append(
                (
                    label,
                    author_wells,
                    author_effects,
                    "openhcs",
                    "openhcs_",
                    colours[index],
                    markers[index],
                )
            )
        x, y, width, extent = (value / 100 for value in bounds)
        declarations = endpoint_declarations()
        conditions = tuple(sorted({item["condition"] for item in effects}))
        limits = {}
        for metric in metrics:
            extents = [
                float(group[f"{method}_fold_change"])
                + sign
                * float(group[f"{method}_treatment_sd"])
                / float(group[f"{method}_control_mean"])
                for _, _, source_effects, method, _, _, _ in series
                for group in source_effects
                if group["metric"] == metric
                for sign in (-1, 1)
            ]
            lower, upper = min(extents), max(extents)
            padding = (upper - lower) * 0.08
            limits[metric] = (lower - padding, upper + padding)
        for column, condition in enumerate(conditions):
            for row, metric in enumerate(metrics):
                left = x + width * (0.14 + column * (0.90 / len(conditions)))
                bottom = y + extent * (
                    0.12 + (len(metrics) - 1 - row) * (0.75 / len(metrics))
                )
                height = extent * 0.55 / len(metrics)
                axis = sheet.figure.add_axes(
                    (left, bottom, width * 0.68 / len(conditions), height)
                )
                letter = chr(ord(start_letter) + row * len(conditions) + column)
                if row == 0:
                    sheet.panel(
                        letter,
                        condition,
                        left * 100,
                        (bottom + height + extent * 0.02) * 100,
                    )
                else:
                    axis.text(
                        0.02,
                        0.98,
                        letter,
                        transform=axis.transAxes,
                        va="top",
                        fontsize=14,
                        weight="bold",
                        color=BLUE,
                    )
                for series_index, (
                    label,
                    source_wells,
                    source_effects,
                    method,
                    prefix,
                    color,
                    marker,
                ) in enumerate(series):
                    selected = sorted(
                        (
                            item
                            for item in source_effects
                            if item["condition"] == condition
                            and item["metric"] == metric
                        ),
                        key=lambda item: float(item["dose_uM"]),
                    )
                    if len(selected) != 5:
                        raise ValueError(
                            f"Incomplete dose series: {label}/{condition}/{metric}"
                        )
                    offset = (series_index - (len(series) - 1) / 2) * (
                        0.26 if len(series) == 2 else 0.18
                    )
                    positions, means = [], []
                    for index, group in enumerate(selected):
                        identities = set(group["treatment_wells"].split(";"))
                        drug = [
                            item
                            for item in source_wells
                            if item["plate"] == group["plate"]
                            and item["well"] in identities
                        ]
                        baseline = float(group[f"{method}_control_mean"])
                        values = [
                            float(item[prefix + metric]) / baseline for item in drug
                        ]
                        if len(values) != int(group["n_treatment"]) or len(values) < 2:
                            raise ValueError(
                                f"Missing replicate: {condition}/{metric}/{group['dose_uM']}"
                            )
                        if not isclose(
                            mean(values),
                            float(group[f"{method}_fold_change"]),
                            rel_tol=1e-10,
                        ):
                            raise ValueError(
                                "Plot points disagree with the effect table"
                            )
                        position = index + offset
                        positions.append(position)
                        means.append(mean(values))
                        axis.errorbar(
                            position,
                            mean(values),
                            yerr=stdev(values),
                            color=color,
                            fmt="_",
                            markersize=11,
                            capsize=3,
                            linewidth=1.2,
                            zorder=2,
                        )
                        axis.scatter(
                            (position - 0.035, position + 0.035),
                            values,
                            marker=marker,
                            s=24,
                            color=color,
                            edgecolor="white",
                            linewidth=0.5,
                            zorder=3,
                        )
                    axis.plot(
                        positions,
                        means,
                        color=color,
                        linewidth=1.1,
                        label=label,
                        zorder=1,
                    )
                axis.axhline(1, color=MUTED, linewidth=0.8, linestyle="--", zorder=0)
                axis.set(
                    xlim=(-0.5, 4.5),
                    ylim=limits[metric],
                    ylabel=fill(declarations[metric].label, width=20),
                    xlabel="Concentration (µM)",
                )
                axis.set_xticks(range(5), [item["dose_uM"] for item in selected])
                axis.tick_params(labelsize=9, colors=INK)
                axis.spines[["top", "right"]].set_visible(False)
                axis.grid(axis="y", color="#e7ebef", linewidth=0.6)
                axis.set_axisbelow(True)
                if row == 0 and column == 0:
                    if len(series) == 2:
                        axis.legend(fontsize=9, frameon=False)
                    else:
                        handles, labels = axis.get_legend_handles_labels()
                        sheet.figure.legend(
                            handles,
                            labels,
                            fontsize=9.5,
                            frameon=False,
                            ncols=len(series),
                            loc="upper center",
                            bbox_to_anchor=(
                                x + width / 2,
                                y + extent * (0.94 if len(metrics) > 1 else 0.85),
                            ),
                        )
        return evidence["protocol_figure_label"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tables", type=Path, required=True)
    parser.add_argument("--stem", required=True)
    parser.add_argument(
        "--metrics", nargs="+", choices=METRICS, default=DEFAULT_METRICS
    )
    args = parser.parse_args()
    NeuriteEffectFigure(
        args.tables.resolve(), stem=args.stem, metrics=tuple(args.metrics)
    ).save()
