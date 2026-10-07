"""Render Figure 7 from retained postfreeze evaluations, without rescoring images.

Run from any directory. Defaults use the existing SLAS paper tree; --root and
--output permit the same generator to render a separate handoff packet.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
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
    axis: plt.Axes, first: float, final: float, title: str, detail: str,
    *, font_size: int = 11,
) -> None:
    bars = axis.bar((0, 1), (100 * first, 100 * final), width=0.55, color=(BLUE, TEAL))
    axis.bar_label(
        bars,
        labels=(f"{100 * first:.2f}", f"{100 * final:.2f}"),
        padding=4,
        fontsize=font_size,
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
        0.5, -0.19, detail, transform=axis.transAxes, ha="center", va="top", fontsize=font_size - 2
    )


def plot_coverage(
    axis: plt.Axes, bbbc039: dict, *, font_size: int = 9,
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
            axis.text(left + 5, count + 1.4, str(int(count)), ha="center", fontsize=font_size)
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
    axis.legend(frameon=False, fontsize=font_size, loc="upper left")
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


def submission_summary() -> None:
    """Draw distinct endpoints from published tables, without reopening predictions."""
    from build_slas_visual_story import FigureSheet, MUTED
    from build_slas_bbbc013_fresh23 import AssaySeries, MedianLog2Ratio, SOURCE

    h001, bbbc039 = load_evaluations(ROOT)
    sheet = FigureSheet("submission_analysis_summary", "Different biological tasks require different checks", 9.0)
    sources = [H001_SOURCE, BBBC039_SOURCE,
               SOURCE_DIRECTORY / "bbbc039-uninspected-fields.csv",
               SOURCE_DIRECTORY / "bbbc007-fresh19-qualified-completion.rst",
               SOURCE_DIRECTORY / "bbbc007-fresh26-final-candidate.rst",
               SOURCE_DIRECTORY / "h002-fresh15-postfreeze-evaluation.json",
               SOURCE.relative_to(ROOT),
               Path("paper/supplementary/personal_neurite_repaired_morphometry/treatment_effects.csv")]
    sheet.source(Path(__file__))
    sheet.source(ROOT / "paper/figures/build_slas_bbbc013_fresh23.py")
    for path in sources:
        sheet.source(ROOT / path)
    axes = [sheet.figure.add_axes((0.09 + col * 0.49, bottom, 0.37, 0.19))
            for bottom in (0.70, 0.405, 0.11) for col in (0, 1)]
    titles = ("A  Bright objects", "B  Independent nuclear analyses",
            "C  DNA / actin cell boundaries", "D  Three-dimensional centres",
              "E  Protein translocation", "F  Laboratory neurite response")
    details = ("Same image · computational reference",
               "Three authors · independent instance annotations",
               "16 fields each · manual-outline union",
               "15 manual centres · coverage not exhaustive",
               "96 wells, including development · 4 wells / dose",
               "Assisted repair · 2 technical wells / dose")
    for axis, title, detail in zip(axes, titles, details, strict=True):
        axis.set_title(title, loc="left", fontsize=12, fontweight="bold", pad=28)
        axis.text(0, 1.06, detail, transform=axis.transAxes, fontsize=9, color=MUTED)
        axis.spines[["top", "right"]].set_visible(False)
        axis.grid(axis="y", color="#e7ebef", linewidth=0.6)
        axis.set_axisbelow(True)
        axis.tick_params(labelsize=10)
        axis.yaxis.label.set_size(11)

    values = [item["derived_f1"] for item in h001["attempts"]]
    bars = axes[0].bar((0, 1), values, color=(BLUE, TEAL), width=0.5)
    axes[0].bar_label(bars, labels=[f"{v:.3f}" for v in values], padding=4, fontsize=11)
    axes[0].set(xticks=(0, 1), xticklabels=("First", "Final"), ylabel="Object F1", ylim=(0, 1.08))

    fields = list(csv.DictReader((ROOT / sources[2]).open()))
    authors = ("fresh612", "fresh10", "fresh13")
    for subset, marker, color, label in ((False, "o", BLUE, "All 200 fields"),
                                        (True, "s", TEAL, "175 image-uninspected")):
        scores = []
        for author in authors:
            rows = [row for row in fields if row["author"] == author
                    and (not subset or row["opened_by_any_of_three_authors"] == "False")]
            if len(rows) != (175 if subset else 200):
                raise ValueError("Wrong BBBC039 comparison population")
            tp, fp, fn = (sum(int(row[key]) for row in rows) for key in
                          ("true_positive_count", "false_positive_count", "false_negative_count"))
            scores.append(2 * tp / (2 * tp + fp + fn))
        positions = np.arange(3) + (0.045 if subset else -0.045)
        axes[1].scatter(positions, scores, marker=marker, color=color, label=label, s=36)
    axes[1].set(xticks=range(3), xticklabels=("Author 1", "Author 2", "Author 3"),
                ylabel="Pooled object F1", ylim=(0.87, 0.94))
    axes[1].legend(frameon=False, fontsize=9, loc="upper left")
    paired = bbbc039["first_vs_final_same_three"]
    axes[1].text(0.02, 0.055,
                 f"Author 1, same 3 fields: {paired['first']['micro_f1']:.3f} → {paired['final']['micro_f1']:.3f}",
                 transform=axes[1].transAxes, fontsize=9, color=MUTED)

    # Decode the two existing publication tables; their units and populations differ
    # from instance matching, so no common accuracy scale is introduced.
    text = (ROOT / sources[3]).read_text()
    block = text.split(".. list-table:: Frozen field-level outline comparison", 1)[1]
    cells = re.findall(r"^\s+(?:\* )?- (.+)$", block, flags=re.MULTILINE)
    rows19 = [cells[i:i + 5] for i in range(5, len(cells), 5)]
    text26 = (ROOT / sources[4]).read_text()
    block26 = text26.split(".. csv-table:: Final frozen candidate, all fields", 1)[1]
    rows26 = list(csv.reader(line.strip() for line in block26.splitlines()
                             if re.match(r"\s+A\d\d_\d+,", line)))
    for index, rows in enumerate((rows19, rows26)):
        if len(rows) != 16 or any(len(row) != 5 for row in rows):
            raise ValueError("Expected sixteen original BBBC007 rows")
        fractions = [int(row[4]) / int(row[3]) for row in rows]
        pooled = sum(int(row[4]) for row in rows) / sum(int(row[3]) for row in rows)
        axes[2].scatter(index + np.linspace(-0.13, 0.13, 16), fractions, color=BLUE, s=15, alpha=0.65)
        axes[2].plot((index - 0.22, index + 0.22), (pooled, pooled), color=TEAL, linewidth=3)
        axes[2].text(index, 0.86, f"Pooled {pooled:.3f}", ha="center", fontsize=10)
    axes[2].set(xticks=(0, 1), xticklabels=("Author 1", "Author 2"), ylim=(0.55, 0.90),
                ylabel="Boundary fraction within 2 px")

    scores = json.loads((ROOT / sources[5]).read_text())["scores"]
    thresholds = sorted(map(int, scores))
    errors = [scores[str(t)]["mean_localisation_error_voxels"] for t in thresholds]
    axes[3].plot(thresholds, errors, "o-", color=TEAL)
    for t, error in zip(thresholds, errors, strict=True):
        axes[3].annotate(f"{scores[str(t)]['true_positives']}/15", (t, error), xytext=(0, 10),
                         textcoords="offset points", ha="center", fontsize=10)
    axes[3].set(xlabel="Matching distance (voxels)", ylabel="Mean matched-centre error (voxels)",
                ylim=(0, 6.1), xticks=thresholds)

    series = AssaySeries.load(SOURCE)
    for assay, color in zip(series, (BLUE, TEAL), strict=True):
        means = [np.mean([MedianLog2Ratio().value(well) for well in dose.wells]) for dose in assay.doses]
        deviations = [np.std([MedianLog2Ratio().value(well) for well in dose.wells], ddof=1) for dose in assay.doses]
        axes[4].errorbar(range(9), means, yerr=deviations, marker="o", markersize=4,
                         color=color, label=f"{assay.compound} · Z′ {assay.control_zprime:.3f}", capsize=2)
    axes[4].set(xticks=range(9), xticklabels=[f"{a.concentration:g}\n{b.concentration:g}"
                for a, b in zip(series[0].doses, series[1].doses, strict=True)],
                xlabel="Concentration: LY294002 (µM) / Wortmannin (nM)",
                ylabel="Well median cell log₂(N/C GFP)", ylim=(-0.5, 2.7))
    axes[4].tick_params(axis="x", labelsize=8)
    axes[4].legend(frameon=False, fontsize=9, loc="upper left")

    rows = list(csv.DictReader((ROOT / sources[7]).open()))
    selected = [row for row in rows if row["metric"] == "mean_outgrowth" and float(row["dose_uM"]) == 40]
    if len(selected) != 2:
        raise ValueError("Expected two retained 40 µM neurite treatment endpoints")
    for offset, key, color, label in ((-0.14, "metaxpress_fold_change", BLUE, "MetaXpress"),
                                     (0.14, "openhcs_fold_change", TEAL, "OpenHCS")):
        values = [float(row[key]) for row in selected]
        bars = axes[5].bar(np.arange(2) + offset, values, width=0.26, color=color, label=label)
        axes[5].bar_label(bars, labels=[f"{v:.2f}" for v in values], padding=3, fontsize=10)
    axes[5].axhline(1, color=MUTED, linestyle="--", linewidth=0.8)
    axes[5].set(xticks=(0, 1), xticklabels=[{"Y27": "Y27632", "FCA": "FC-A"}.get(row["condition"], row["condition"]) for row in selected],
                xlabel="40 µM relative to matched DMSO", ylabel="Outgrowth per cell (fold)", ylim=(0, 2.6))
    axes[5].legend(frameon=False, fontsize=9, loc="lower left")
    sheet.save()


def publish_briefs() -> None:
    """Publish retained instructions, not reconstructed successful-run recipes."""
    directory = ROOT / SOURCE_DIRECTORY
    trials = list(csv.DictReader((directory / "trial_resources.csv").open()))
    documents: dict[str, dict] = {}
    catalogue = []
    for trial in trials:
        root = Path(trial["source_root"])
        paths = [root.parent / name for name in ("TASK.rst", "SCIENCE-BRIEF.rst", "BRIEF.md", "BRIEF.rst")
                 if (root.parent / name).is_file()]
        journal = root / "runtime/author-events.typescript"
        input_root = None
        if journal.is_file():
            with journal.open() as stream:
                for index, line in enumerate(stream):
                    match = re.search(r"FLEET_INPUT=([^\s]+)", line)
                    if match:
                        input_root = Path(match[1].split(chr(92))[0].split(chr(34))[0])
                        break
                    if index > 400:
                        break
        if input_root is not None:
            paths.extend(input_root / name for name in ("BRIEF.md", "BRIEF.rst", "SCIENCE-BRIEF.rst", "OPENHCS_AUTHORING.md")
                         if (input_root / name).is_file())
        row = {"trial_id": trial["trial_id"], "dataset": trial["dataset"], "documents": []}
        for path in dict.fromkeys(paths):
            raw = path.read_bytes()
            checksum = hashlib.sha256(raw).hexdigest()
            document = documents.setdefault(checksum, {"sha256": checksum, "text": raw.decode(),
                                                        "original_paths": [], "trials": [],
                                                        "kind": "operational task" if path.name == "TASK.rst" else "scientific brief"})
            if str(path) not in document["original_paths"]:
                document["original_paths"].append(str(path))
            if trial["trial_id"] not in document["trials"]:
                document["trials"].append(trial["trial_id"])
            row["documents"].append(checksum)
        catalogue.append(row)
    archive = {"source_catalogue_sha256": sha256(directory / "trial_resources.csv"),
               "scope": "Verbatim retained files. Exported input roots are recovered from original launch logs; this is not proof that every instruction was read.",
               "trials": catalogue, "documents": list(documents.values())}
    (directory / "original_task_briefs.json").write_text(json.dumps(archive, indent=2) + "\n")
    lines = ["### Original scientific briefs", "",
             "The following retained scientific instructions are reproduced verbatim, including technical hints and operational restrictions. Identical texts are shared across trials; the [complete instruction archive](task_only_analysis/original_task_briefs.json) retains operational TASK files and exact byte hashes, mapping every retained trial to its documents. These instructions demonstrate the supplied task context, not usability with untrained scientists or proof that every instruction was followed.", "",
             "The public assay briefs supply typed source bindings, catalogue tracks and output contracts. BBBC007 explicitly requests seeded cell segmentation; BBBC013 specifies nuclear versus cytoplasmic GFP measurement. Optional registered-custom tracks are also supplied, although their presence does not establish that an author used them. The H003 brief directs `SourceBindingsConfig` pairing. Neurite briefs request crossing review; the thick-shaft-only target was clarified later, not supplied retrospectively. Some historical packets contain resource caps subsequently removed from the programme. They are reproduced as history, not current requirements.", ""]
    # Collapse whitespace-only duplicate editions in the typeset appendix while
    # preserving every original byte sequence in the archive above.
    editions: dict[str, list[dict]] = {}
    for document in documents.values():
        if document["kind"] == "scientific brief":
            editions.setdefault(document["text"].strip(), []).append(document)
    for number, (text, versions) in enumerate(editions.items(), 1):
        ids = list(dict.fromkeys(trial for version in versions for trial in version["trials"]))
        title = ("Unavailable pooled-stack scientific brief" if text.startswith("sed: can't read")
                 else text.splitlines()[0].lstrip("# "))
        lines.extend([f"#### Brief {number}: {title}", "",
                      "Trials: " + "; ".join(f"`{trial}`" for trial in ids) + ".", ""])
        if "OPENHCS_AUTHORING" in versions[0]["original_paths"][0]:
            hint = "Technical guidance: explicit source bindings, catalogue authoring tracks, typed artifact requirements and freeze procedure; optional custom-registration tracks where stated. These are not method-free briefs."
        elif "SourceBindingsConfig" in text:
            hint = "Technical guidance: exact channel pairing through SourceBindingsConfig, compiled-workspace checks, instance outputs and multi-window image review."
        elif "H002" in text.splitlines()[0]:
            hint = "Technical guidance: a 3-D volume, z/y/x voxel-coordinate outputs and orthogonal multi-window review; no verified physical scale or detection parameters."
        elif "H001" in text.splitlines()[0]:
            hint = "Technical guidance: 2-D instance labels, pixel areas, counts and matched regional review; no segmentation algorithm or parameter values."
        elif any(token in text for token in ("RBPMS", "R0010")):
            hint = "Technical guidance: RBPMS/Hoechst channel hints, instance/count outputs and distributed matched-view review; additional workflow/resource restrictions remain visible in the text."
        elif "neurite" in text.lower():
            hint = "Technical guidance: paired-channel soma/process outputs and crossing/extent review. Declared channels and calibration, where supplied, are acquisition hints. Retained-development and mosaic instructions are continuations, not fresh trials."
        else:
            hint = "The full retained instruction is reproduced below; no successful-run method has been substituted for it."
        lines.extend([hint, ""])
        if text.startswith("sed: can't read"):
            lines.extend(["This retained file contains a failed-copy error, not a valid scientific brief. The corresponding operational task is retained verbatim in the archive; no missing brief has been invented.", ""])
        for line in text.splitlines():
            # Retain the original text as a quotation, not a second hierarchy of
            # oversized manuscript headings parsed from its Markdown/RST syntax.
            if line.startswith("#") or re.fullmatch(r"[=-]{3,}", line):
                line = chr(92) + line
            lines.append("> " + line if line else ">")
        lines.append("")
    missing = [row["trial_id"] for row in catalogue if not row["documents"]]
    if missing:
        lines.extend(["#### Earlier prospective records", "",
                      "The resource catalogue contains no recoverable original instruction file for "
                      + ", ".join(f"`{trial}`" for trial in missing)
                      + ". Their published prospective protocol and partitions remain in Supplementary Data 7; author-written candidate plans are not relabelled as original prompts.", ""])
    appendix = "\n".join(lines)
    (directory / "original_task_briefs.md").write_text(appendix)
    supplement = ROOT / "paper/supplementary/README.md"
    current = supplement.read_text()
    heading = ("### Scientific briefs and the limits of the domain-expert framing"
               if "### Scientific briefs and the limits of the domain-expert framing" in current
               else "### Original scientific briefs")
    start = current.index(heading)
    end = current.index("The current skill describes intended inspection", start)
    supplement.write_text(current[:start] + appendix + "\n\n" + current[end:])
    print(f"Published {len(editions)} scientific brief editions and {sum(bool(row['documents']) for row in catalogue)} trial instruction mappings")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--submission-summary", action="store_true")
    parser.add_argument("--publish-briefs", action="store_true")
    arguments = parser.parse_args()
    root = arguments.root.resolve()
    if arguments.publish_briefs:
        publish_briefs()
    elif arguments.submission_summary:
        submission_summary()
    else:
        build(root, arguments.output or root / "paper/figures/slas")
