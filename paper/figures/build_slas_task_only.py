"""Render Figure 7 from retained postfreeze evaluations, without rescoring images.

Run from any directory. Defaults use the existing SLAS paper tree; --root and
--output permit the same generator to render a separate handoff packet.
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
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
SOURCE_DIRECTORY = Path("paper/supplementary/task_only_analysis")
H001_SOURCE = SOURCE_DIRECTORY / "h001-fresh586-postfreeze-evaluation.json"
BBBC039_SOURCE = SOURCE_DIRECTORY / "bbbc039-fresh612-postfreeze-evaluation.json"
STEM = "task_only_analysis"
BLUE = "#216da5"
TEAL = "#16877f"
ORANGE = "#b76a29"


def sha256(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def load_evaluations(root: Path) -> tuple[dict, dict]:
    """Read the original score receipts; do not open their prediction/reference paths."""
    h001 = json.loads((root / H001_SOURCE).read_text(encoding="utf-8"))
    bbbc039 = json.loads((root / BBBC039_SOURCE).read_text(encoding="utf-8"))
    if h001["author_run"] != "H001_FRESH586_96":
        raise ValueError("Expected the retained H001586 evaluation")
    attempts = h001["attempts"]
    if [item["attempt"] for item in attempts] != ["a01", "a04"]:
        raise ValueError("Expected the paired H001 a01/a04 evaluations")
    if attempts[0]["score"]["shape"] != attempts[1]["score"]["shape"]:
        raise ValueError("H001 paired evaluations must cover the same image")
    if (
        attempts[0]["score"]["reference_objects"]
        != attempts[1]["score"]["reference_objects"]
    ):
        raise ValueError("H001 reference populations differ")

    fields = bbbc039["instance_metrics"]
    keys = [(item["source_set_id"], item["channel"]) for item in fields]
    if (
        len(fields) != 200
        or len(set(keys)) != 200
        or bbbc039["summary"]["fields"] != 200
    ):
        raise ValueError("Final coverage requires all 200 distinct evaluated fields")
    if any(not np.isfinite(item["f1"]) or not 0 <= item["f1"] <= 1 for item in fields):
        raise ValueError(
            "The complete F1 distribution must contain finite scores in [0, 1]"
        )
    paired = bbbc039["first_vs_final_same_three"]
    first_fields = paired["first_instance_metrics"]
    first_keys = [(item["source_set_id"], item["channel"]) for item in first_fields]
    declared_keys = [tuple(key) for key in paired["source_keys"]]
    if (
        len(first_keys) != 3
        or len(set(first_keys)) != 3
        or set(first_keys) != set(declared_keys)
    ):
        raise ValueError(
            "The first/final comparison requires the original three source identities"
        )
    final_by_key = dict(zip(keys, fields, strict=True))
    for field, key in zip(first_fields, first_keys, strict=True):
        if field["reference_count"] != final_by_key[key]["reference_count"]:
            raise ValueError("BBBC039 paired reference populations differ")
    if paired["first"]["fields"] != 3 or paired["final"]["fields"] != 3:
        raise ValueError(
            "Do not project a first-200 score from the three-field comparison"
        )
    return h001, bbbc039


def plot_pair(
    axis: plt.Axes, first: float, final: float, title: str, detail: str
) -> None:
    bars = axis.bar((0, 1), (100 * first, 100 * final), width=0.55, color=(BLUE, TEAL))
    axis.bar_label(
        bars,
        labels=(f"{100 * first:.2f}", f"{100 * final:.2f}"),
        padding=4,
        fontsize=11,
    )
    axis.set(
        title=title,
        xticks=(0, 1),
        xticklabels=("First", "Final"),
        ylabel="Object F1 (%)",
        ylim=(0, 108),
        yticks=(0, 20, 40, 60, 80, 100),
    )
    axis.text(
        0.5, -0.19, detail, transform=axis.transAxes, ha="center", va="top", fontsize=9
    )


def plot_coverage(
    axis: plt.Axes, bbbc039: dict
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    fields = bbbc039["instance_metrics"]
    ordinary = [100 * field["f1"] for field in fields if field["reference_count"] > 0]
    empty = [100 * field["f1"] for field in fields if field["reference_count"] == 0]
    edges = np.linspace(0, 100, 11)
    ordinary_counts, _ = np.histogram(ordinary, bins=edges)
    empty_counts, _ = np.histogram(empty, bins=edges)
    if int(ordinary_counts.sum() + empty_counts.sum()) != len(fields):
        raise ValueError("Coverage histogram omitted an evaluated field")
    bars = axis.bar(
        edges[:-1],
        ordinary_counts,
        width=10,
        align="edge",
        color=TEAL,
        edgecolor="white",
        label=f"Annotated fields (n={len(ordinary)})",
    )
    axis.bar(
        edges[:-1],
        empty_counts,
        width=10,
        align="edge",
        bottom=ordinary_counts,
        color=ORANGE,
        edgecolor="white",
        label=f"Annotation-empty fields (n={len(empty)})",
    )
    for left, count in zip(edges[:-1], ordinary_counts + empty_counts, strict=True):
        if count:
            axis.text(left + 5, count + 1.4, str(int(count)), ha="center", fontsize=9)
    pooled = 100 * bbbc039["summary"]["micro_f1"]
    axis.axvline(
        pooled,
        color=BLUE,
        linestyle="--",
        linewidth=1.4,
        label=f"Pooled object F1 {pooled:.2f}%",
    )
    axis.set(
        title="C  BBBC039: final coverage, all 200 fields",
        xlabel="Per-field object F1 (%)",
        ylabel="Fields",
        xlim=(0, 100),
        xticks=np.arange(0, 101, 10),
        ylim=(0, max(ordinary_counts + empty_counts) * 1.2),
    )
    axis.legend(frameon=False, fontsize=9, loc="upper left")
    return edges, ordinary_counts, empty_counts


def write_plot_data(path: Path, h001: dict, bbbc039: dict) -> None:
    """Export the plotted observations verbatim, not a second scoring calculation."""
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.writer(stream)
        writer.writerow(
            (
                "panel",
                "dataset",
                "scope",
                "stage",
                "source_set_id",
                "channel",
                "reference_count",
                "object_f1_fraction",
            )
        )
        for item in h001["attempts"]:
            writer.writerow(
                (
                    "A",
                    "H001586",
                    "whole image",
                    item["attempt"],
                    "image.tif",
                    "",
                    item["score"]["reference_objects"],
                    item["derived_f1"],
                )
            )
        paired = bbbc039["first_vs_final_same_three"]
        for stage in ("first", "final"):
            writer.writerow(
                (
                    "B",
                    "BBBC039612",
                    "same three fields pooled",
                    stage,
                    "",
                    "DNA",
                    paired[stage]["reference_objects"],
                    paired[stage]["micro_f1"],
                )
            )
        for item in paired["first_instance_metrics"]:
            writer.writerow(
                (
                    "B",
                    "BBBC039612",
                    "same three fields",
                    "first",
                    item["source_set_id"],
                    item["channel"],
                    item["reference_count"],
                    item["f1"],
                )
            )
        for item in bbbc039["instance_metrics"]:
            writer.writerow(
                (
                    "C",
                    "BBBC039612",
                    "full 200 fields",
                    "final",
                    item["source_set_id"],
                    item["channel"],
                    item["reference_count"],
                    item["f1"],
                )
            )


def build(root: Path, output: Path) -> None:
    h001, bbbc039 = load_evaluations(root)
    output.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update(
        {
            "font.size": 10,
            "axes.spines.top": False,
            "axes.spines.right": False,
            "svg.fonttype": "none",
        }
    )
    figure = plt.figure(figsize=(8.2, 7.1), layout="constrained")
    grid = figure.add_gridspec(2, 2, height_ratios=(1, 1.05), hspace=0.09)
    axes = (
        figure.add_subplot(grid[0, 0]),
        figure.add_subplot(grid[0, 1]),
        figure.add_subplot(grid[1, :]),
    )
    attempts = h001["attempts"]
    plot_pair(
        axes[0],
        attempts[0]["derived_f1"],
        attempts[1]["derived_f1"],
        "A  H001: same whole image",
        "Notebook-derived computational reference\na01 → a04",
    )
    paired = bbbc039["first_vs_final_same_three"]
    plot_pair(
        axes[1],
        paired["first"]["micro_f1"],
        paired["final"]["micro_f1"],
        "B  BBBC039: same three fields",
        "Independent annotations\nOriginal three development fields",
    )
    edges, ordinary_counts, empty_counts = plot_coverage(axes[2], bbbc039)
    for axis in axes:
        axis.grid(axis="y", color="#d9e0e5", linewidth=0.6)
        axis.set_axisbelow(True)
    figure.suptitle(
        "Task-only analysis: within-run revision and final coverage", fontsize=12
    )
    outputs = []
    for suffix in ("png", "pdf", "svg"):
        path = output / f"{STEM}.{suffix}"
        figure.savefig(path, dpi=300)
        outputs.append(path)
    plt.close(figure)
    plot_data = output / f"{STEM}_plot_data.csv"
    write_plot_data(plot_data, h001, bbbc039)
    outputs.append(plot_data)
    receipt = {
        "source_sha256": {
            str(path): sha256(root / path) for path in (H001_SOURCE, BBBC039_SOURCE)
        },
        "generator_sha256": sha256(Path(__file__)),
        "output_sha256": {path.name: sha256(path) for path in outputs},
        "panels": {
            "A": {
                "author_run": h001["author_run"],
                "attempts": [item["attempt"] for item in attempts],
                "reference": "notebook-derived computational primary; not manual annotations",
                "f1": [item["derived_f1"] for item in attempts],
                "shape": attempts[0]["score"]["shape"],
            },
            "B": {
                "reference": "independent BBBC039 annotations",
                "paired_source_keys": paired["source_keys"],
                "pooled_f1": {
                    stage: paired[stage]["micro_f1"] for stage in ("first", "final")
                },
            },
            "C": {
                "fields": len(bbbc039["instance_metrics"]),
                "pooled_f1": bbbc039["summary"]["micro_f1"],
                "histogram_edges_percent": edges.tolist(),
                "annotated_counts": ordinary_counts.tolist(),
                "annotation_empty_counts": empty_counts.tolist(),
                "annotation_empty_source_ids": [
                    item["source_set_id"]
                    for item in bbbc039["instance_metrics"]
                    if item["reference_count"] == 0
                ],
            },
        },
        "scope": "Retained postfreeze task-only trials; no new scoring, pipeline execution or author feedback.",
        "limits": [
            "No first-200 score exists; the paired comparison is limited to the original three fields.",
            "Full-200 final coverage includes development fields and the complete low-score tail.",
            "First refers to the retained initial completed candidate, not first technical execution success.",
            "Neither reference agreement nor within-run improvement isolates a causal skill effect.",
        ],
        "rendering": {
            "matplotlib": matplotlib.__version__,
            "figure_inches": [8.2, 7.1],
            "png_dpi": 300,
        },
    }
    (output / f"{STEM}_provenance.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )
    print(f"Rendered Figure 7 to {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    root = arguments.root.resolve()
    build(root, arguments.output or root / "paper/figures/slas")
