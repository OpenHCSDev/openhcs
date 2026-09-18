"""Render held-out results from the three prospective agent-authored assays."""

from __future__ import annotations

import csv
import hashlib
import json
from collections import defaultdict
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "paper/supplementary/independent_validation"
OUTPUT = Path(__file__).resolve().parent / "slas"
SCORE_PATHS = (
    DATA / "bbbc039_heldout_score.json",
    DATA / "bbbc007_heldout_score.json",
    DATA / "bbbc013_heldout_score.json",
)
EVIDENCE_PATHS = (
    DATA / "bbbc039_frozen_pipeline.py",
    DATA / "bbbc007_frozen_pipeline.py",
    DATA / "bbbc013_frozen_pipeline.py",
    DATA / "bbbc013_development_freeze.json",
    DATA / "bbbc013_heldout_freeze.json",
)


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def load_score(path: Path, dataset: str) -> dict[str, object]:
    score = json.loads(path.read_text(encoding="utf-8"))
    if score["dataset"] != dataset or score["partition"] != "held_out":
        raise ValueError(f"Unexpected held-out score identity in {path}")
    return score


def plot_nuclear_instances(axis: plt.Axes, score: dict[str, object]) -> None:
    fields = score["fields"]
    if len(fields) != 50:
        raise ValueError("BBBC039 figure requires all 50 held-out fields")
    object_f1 = np.asarray([field["metrics"]["object_f1"] for field in fields])
    foreground_dice = np.asarray([field["metrics"]["pixel_dice"] for field in fields])
    order = np.argsort(object_f1)
    x = np.arange(1, len(fields) + 1)
    axis.plot(x, object_f1[order], color="#247BA0", marker="o", ms=3, label="Object F1")
    axis.plot(
        x,
        foreground_dice[order],
        color="#16877f",
        marker="o",
        ms=3,
        label="Foreground Dice",
    )
    metrics = score["metrics"]
    axis.text(
        0.03,
        0.05,
        f"Pooled object F1 {metrics['object_f1']:.3f}\n"
        f"Mean foreground Dice {metrics['mean_field_pixel_dice']:.3f}",
        transform=axis.transAxes,
        fontsize=9,
        va="bottom",
    )
    axis.set(
        title="A  BBBC039 nuclear instances",
        xlabel="Held-out field rank by object F1",
        ylabel="Score",
        ylim=(0, 1.03),
    )
    axis.legend(frameon=False, fontsize=9, loc="lower right")


def plot_cell_boundaries(axis: plt.Axes, score: dict[str, object]) -> None:
    fields = score["fields"]
    if len(fields) != 12:
        raise ValueError("BBBC007 figure requires all 12 held-out fields")
    fractions = np.asarray(
        [field["boundary"]["adjacent_boundary_within_2px_fraction"] for field in fields]
    )
    axis.bar(
        np.arange(1, len(fields) + 1),
        fractions,
        color="#C56B29",
        width=0.72,
    )
    metrics = score["metrics"]
    axis.axhline(
        metrics["pooled_adjacent_boundary_within_2px_fraction"],
        color="#6B7280",
        linestyle="--",
        linewidth=1.2,
        label="Pooled fraction",
    )
    axis.text(
        0.03,
        0.05,
        f"Pooled within 2 px {metrics['pooled_adjacent_boundary_within_2px_fraction']:.3f}\n"
        f"Nuclei without a cell {metrics['nuclei_without_cell_overlap']}",
        transform=axis.transAxes,
        fontsize=9,
        va="bottom",
    )
    axis.set(
        title="B  BBBC007 adjacent-cell boundaries",
        xlabel="Held-out field",
        ylabel="Predicted boundary within 2 px",
        ylim=(0, 1.03),
        xticks=np.arange(1, len(fields) + 1),
    )
    axis.legend(frameon=False, fontsize=9, loc="upper right")


def plot_translocation(
    axis: plt.Axes, treatment: dict[str, object], panel: str
) -> None:
    by_dose: dict[float, list[float]] = defaultdict(list)
    for observation in treatment["dose_response"]:
        by_dose[float(observation["dose"])].append(
            float(observation["mean_nuclear_cytoplasmic_gfp_ratio"])
        )
    doses = np.asarray(sorted(by_dose))
    means = np.asarray([np.mean(by_dose[dose]) for dose in doses])
    deviations = np.asarray(
        [
            np.std(by_dose[dose], ddof=1) if len(by_dose[dose]) > 1 else 0
            for dose in doses
        ]
    )
    for dose in doses:
        values = by_dose[dose]
        axis.scatter(
            np.full(len(values), dose),
            values,
            color="#247BA0",
            s=19,
            alpha=0.55,
            zorder=2,
        )
    axis.errorbar(
        doses,
        means,
        yerr=deviations,
        color="#16877f",
        marker="o",
        linewidth=1.7,
        capsize=2.5,
        label="Held-out wells, mean +/- SD",
        zorder=3,
    )
    axis.axhline(
        treatment["negative_mean"],
        color="#6B7280",
        linestyle=":",
        linewidth=1.1,
        label="Negative-control mean",
    )
    axis.axhline(
        treatment["positive_mean"],
        color="#C56B29",
        linestyle="--",
        linewidth=1.1,
        label="Positive-control mean",
    )
    unit = treatment["dose_response"][0]["unit"]
    axis.text(
        0.03,
        0.94,
        f"Z' = {treatment['z_prime']:.3f}",
        transform=axis.transAxes,
        fontsize=9.5,
        va="top",
    )
    axis.set(
        title=f"{panel}  BBBC013 {treatment['treatment']}",
        xscale="log",
        xlabel=f"Dose ({unit})",
        ylabel="Mean nuclear / cytoplasmic GFP",
        ylim=(0, None),
    )
    axis.legend(frameon=False, fontsize=8, loc="lower right")


def write_plot_data(
    path: Path,
    nuclei_score: dict[str, object],
    cells_score: dict[str, object],
    translocation_score: dict[str, object],
) -> None:
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(
            stream,
            fieldnames=("dataset", "record", "series", "x", "value", "unit"),
        )
        writer.writeheader()
        for index, field in enumerate(nuclei_score["fields"], 1):
            for series, value in (
                ("object_f1", field["metrics"]["object_f1"]),
                ("foreground_dice", field["metrics"]["pixel_dice"]),
            ):
                writer.writerow(
                    {
                        "dataset": "BBBC039",
                        "record": index,
                        "series": series,
                        "x": index,
                        "value": value,
                        "unit": "fraction",
                    }
                )
        for index, field in enumerate(cells_score["fields"], 1):
            writer.writerow(
                {
                    "dataset": "BBBC007",
                    "record": index,
                    "series": "predicted_boundary_within_2px",
                    "x": index,
                    "value": field["boundary"]["adjacent_boundary_within_2px_fraction"],
                    "unit": "fraction",
                }
            )
        for treatment in translocation_score["metrics"]["treatments"]:
            for observation in treatment["dose_response"]:
                writer.writerow(
                    {
                        "dataset": "BBBC013",
                        "record": observation["well"],
                        "series": treatment["treatment"],
                        "x": observation["dose"],
                        "value": observation["mean_nuclear_cytoplasmic_gfp_ratio"],
                        "unit": observation["unit"],
                    }
                )


def build() -> None:
    nuclei_score = load_score(SCORE_PATHS[0], "BBBC039")
    cells_score = load_score(SCORE_PATHS[1], "BBBC007")
    translocation_score = load_score(SCORE_PATHS[2], "BBBC013")
    treatments = translocation_score["metrics"]["treatments"]
    if [item["treatment"] for item in treatments] != ["Wortmannin", "LY294002"]:
        raise ValueError("BBBC013 treatment order or identity changed")

    OUTPUT.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.size": 10,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "svg.fonttype": "none",
        }
    )
    figure, axes = plt.subplots(2, 2, figsize=(8.2, 7.1), layout="constrained")
    plot_nuclear_instances(axes[0, 0], nuclei_score)
    plot_cell_boundaries(axes[0, 1], cells_score)
    plot_translocation(axes[1, 0], treatments[0], "C")
    plot_translocation(axes[1, 1], treatments[1], "D")
    for axis in axes.flat:
        axis.grid(axis="y", color="#d9e0e5", linewidth=0.6)
        axis.set_axisbelow(True)
    figure.suptitle(
        "Held-out results from three independently authored workflows",
        fontsize=12,
    )

    outputs: list[Path] = []
    for suffix in ("png", "pdf", "svg"):
        destination = OUTPUT / f"independent_agent_validation.{suffix}"
        figure.savefig(destination, dpi=300)
        outputs.append(destination)
    plt.close(figure)

    plot_data = OUTPUT / "independent_agent_validation_plot_data.csv"
    write_plot_data(plot_data, nuclei_score, cells_score, translocation_score)
    outputs.append(plot_data)
    receipt = {
        "source_sha256": {
            str(path.relative_to(ROOT)): sha256(path)
            for path in (*SCORE_PATHS, *EVIDENCE_PATHS)
        },
        "generator_sha256": sha256(Path(__file__)),
        "held_out_populations": {
            "BBBC039_fields": len(nuclei_score["fields"]),
            "BBBC007_fields": len(cells_score["fields"]),
            "BBBC013_wells": len(translocation_score["wells"]),
        },
        "output_sha256": {path.name: sha256(path) for path in outputs},
    }
    (OUTPUT / "independent_agent_validation_provenance.json").write_text(
        json.dumps(receipt, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Rendered independent validation figure to {OUTPUT}")


if __name__ == "__main__":
    build()
