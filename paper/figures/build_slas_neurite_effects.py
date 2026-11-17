"""Plot measured well-level drug effects; never process or tune images."""

import argparse
import json
from math import isclose
from pathlib import Path
from statistics import correlation, mean, stdev
from textwrap import fill

from build_slas_visual_story import (
    BLUE,
    TEAL,
    ORANGE,
    PURPLE,
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

    publication_cohort = ROOT / "paper/supplementary/personal_neurite_reanalysis_20261116"
    primary_metrics = ("mean_outgrowth", "branches_per_cell")
    analysis_colours = (TEAL, ORANGE, PURPLE)
    analysis_markers = ("s", "^", "D")

    @classmethod
    def cohort_tables(cls, sheet: FigureSheet):
        """Author identity and the selected evaluation come from one cohort record."""
        cohort = cls.publication_cohort
        record = cohort / "cohort.json"
        sheet.source(record)
        authors = json.loads(record.read_text())["authors"]
        return {author["label"].replace("Blind ", "Analysis ", 1): cohort / author["tables"]
                for author in authors}

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
    def read_datasets(sheet, tables, metrics):
        """Read the matched well tables and verify their shared reference values."""
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
        return datasets

    @staticmethod
    def condition_title(condition):
        return "Y27632" if condition == "Y27" else condition

    @classmethod
    def read_correlations(cls, sheet, tables, metrics):
        """One calculation supplies both the summary bars and complete heatmap."""
        datasets = cls.read_datasets(sheet, tables, metrics)
        values, counts = {}, set()
        for condition in sorted({row["condition"] for row in datasets[0][1]}):
            selected = [[row for row in wells if row["condition"] == condition]
                        for _, wells, _, _ in datasets]
            counts.update(len(wells) for wells in selected)
            values[condition] = [
                [correlation([float(row[metric]) for row in wells],
                             [float(row["openhcs_" + metric]) for row in wells])
                 for wells in selected]
                for metric in metrics
            ]
        return tuple(label for label, _, _, _ in datasets), values, counts

    @classmethod
    def draw_correlations(cls, sheet, tables, *, bounds=(0.40, 0.17, 0.48, 0.60)):
        """Compare every run and endpoint within each treatment, never pooled."""
        declarations = endpoint_declarations()
        metrics = tuple(declarations)
        labels, panels, counts = cls.read_correlations(sheet, tables, metrics)
        x, y, width, height = bounds
        gap = .04
        panel_width = (width - gap * (len(panels) - 1)) / len(panels)
        for column, (condition, values) in enumerate(panels.items()):
            left = x + column * (panel_width + gap)
            axis = sheet.plot_axes((left, y, panel_width, height))
            image = axis.imshow(values, vmin=-1, vmax=1, cmap="RdBu", aspect="auto")
            axis.set_xticks(range(len(labels)), labels,
                            rotation=45, ha="left", rotation_mode="anchor", fontsize=10)
            axis.set_yticks(range(len(metrics)), [declarations[metric].absolute_label for metric in metrics])
            axis.xaxis.tick_top()
            axis.tick_params(length=0, pad=7, labelleft=column == 0)
            sheet.text((left + panel_width / 2) * 100, 92,
                       NeuriteEffectFigure.condition_title(condition),
                       ha="center", size=14, weight="bold")
            for row, results in enumerate(values):
                for run, value in enumerate(results):
                    axis.text(run, row, f"{value:.3f}", ha="center", va="center",
                              fontsize=11, color="white" if abs(value) > .6 else "black")
        bar_axis = sheet.figure.add_axes((.915, y, .015, height))
        bar = sheet.figure.colorbar(image, cax=bar_axis)
        bar.ax.set_title("r", fontsize=11, pad=8)
        bar.ax.tick_params(labelsize=10)
        return counts

    @classmethod
    def draw_correlation_bars(cls, sheet, tables, *, metrics,
                              bounds=(.14, .345, .80, .13), start_letter="E"):
        """Group treatments and primary endpoints on one correlation axis."""
        labels, panels, counts = cls.read_correlations(sheet, tables, metrics)
        declarations = endpoint_declarations()
        groups = [(condition, metric, values)
                  for condition, rows in panels.items()
                  for metric, values in zip(metrics, rows, strict=True)]
        axis = sheet.plot_axes(bounds)
        bar_width = .8 / len(labels)
        for run, (label, colour) in enumerate(zip(labels, cls.analysis_colours, strict=True)):
            positions = [index + (run - (len(labels) - 1) / 2) * bar_width
                         for index in range(len(groups))]
            bars = axis.bar(positions, [values[run] for _, _, values in groups],
                            width=bar_width * .9, color=colour, label=label, zorder=3)
            axis.bar_label(bars, fmt="%.3f", label_type="center", rotation=90,
                           fontsize=12, fontweight="bold", color="white")
        axis.set(ylim=(min(0, *(value for _, _, values in groups for value in values)), 1.20),
                 yticks=(0, .5, 1), xticks=range(len(groups)),
                 xticklabels=[f"{cls.condition_title(condition)}\n"
                              f"{fill(declarations[metric].absolute_label, 16)}"
                              for condition, metric, _ in groups])
        axis.tick_params(labelsize=11.5)
        axis.set_title(f"{start_letter}  Pearson r against MetaXpress", loc="left",
                       fontsize=sheet.plot_font_size, fontweight="bold", color=BLUE)
        axis.spines[["top", "right"]].set_visible(False)
        axis.grid(axis="y", color="#e7ebef", linewidth=.6)
        axis.set_axisbelow(True)
        return counts

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
        datasets = NeuriteEffectFigure.read_datasets(sheet, tables, metrics)
        _, wells, effects, evidence = datasets[0]
        series = [("MetaXpress", wells, effects, "metaxpress", "", BLUE, "o")]
        colours = NeuriteEffectFigure.analysis_colours
        markers = NeuriteEffectFigure.analysis_markers
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
        figure_width, figure_height = sheet.figure.get_size_inches() * 72
        column_gap = 6.5 * sheet.plot_font_size / figure_width
        plot_width = (width * 0.79 - column_gap * (len(conditions) - 1)) / len(conditions)
        row_stride = extent * 0.75 / len(metrics)
        height = min(extent * 0.55 / len(metrics),
                     row_stride - 3.2 * sheet.plot_font_size / figure_height)
        for column, condition in enumerate(conditions):
            for row, metric in enumerate(metrics):
                left = x + width * 0.14 + column * (plot_width + column_gap)
                bottom = y + extent * 0.12 + (len(metrics) - 1 - row) * row_stride
                axis = sheet.plot_axes((left, bottom, plot_width, height))
                letter = chr(ord(start_letter) + row * len(conditions) + column)
                if row == 0:
                    sheet.panel(
                        letter,
                        NeuriteEffectFigure.condition_title(condition),
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
                axis.spines[["top", "right"]].set_visible(False)
                axis.grid(axis="y", color="#e7ebef", linewidth=0.6)
                axis.set_axisbelow(True)
        handles, labels = axis.get_legend_handles_labels()
        sheet.figure.legend(
            handles,
            labels,
            fontsize=sheet.plot_font_size,
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
