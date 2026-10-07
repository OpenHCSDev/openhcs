"""Original manuscript diagrams and panels assembled from retained UI captures.

Editorial layout is explicit here. Capture identities and file hashes are read
from the published gallery authority; no UI state or scientific image is invented.
"""

from __future__ import annotations

import csv
import json
from io import BytesIO
from pathlib import Path
import subprocess

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch, Rectangle
from PIL import Image

from build_slas_agent import ROOT, OUTPUT, digest, normalize_generated_svg

GALLERY = ROOT / "website/assets/gallery"
INK = "#203044"
MUTED = "#59697b"
BLUE = "#216da5"
TEAL = "#16877f"
PURPLE = "#7960a5"
ORANGE = "#b76a29"
PALE = "#f3f6f9"


class FigureSheet:
    """A single editable figure canvas with its actual source receipt."""

    def __init__(self, stem: str, title: str, height: float = 7.7):
        self.stem = stem
        self.figure = plt.figure(figsize=(9, height), facecolor="white")
        self.axis = self.figure.add_axes((0, 0, 1, 1))
        self.axis.set(xlim=(0, 100), ylim=(0, 100))
        self.axis.set_axis_off()
        self.sources: dict[str, str] = {}
        self.crops: list[dict] = []
        self.text(3, 97, title, size=16, weight="bold", va="top")

    def text(self, x, y, value, *, size=11, color=INK, **kwargs):
        return self.axis.text(x, y, value, fontsize=size, color=color, **kwargs)

    def panel(self, letter, title, x, y):
        self.text(x, y, letter, size=14, weight="bold", color=BLUE)
        self.text(x + 3.1, y, title, size=12, weight="bold")

    def box(self, x, y, width, height, title, detail="", *, color=BLUE):
        self.axis.add_patch(
            FancyBboxPatch(
                (x, y),
                width,
                height,
                boxstyle="round,pad=0.2,rounding_size=0.65",
                linewidth=1.15,
                edgecolor=color,
                facecolor="white",
                zorder=2,
            )
        )
        self.text(
            x + width / 2,
            y + height * (0.65 if detail else 0.5),
            title,
            size=11,
            weight="bold",
            ha="center",
            va="center",
            color=color,
        )
        if detail:
            self.text(
                x + width / 2,
                y + height * 0.28,
                detail,
                size=9,
                ha="center",
                va="center",
            )

    def arrow(self, start, end, *, color=MUTED, both=False, dashed=False):
        self.axis.add_patch(
            FancyArrowPatch(
                start,
                end,
                arrowstyle="<->" if both else "-|>",
                mutation_scale=13,
                linewidth=1.4,
                color=color,
                linestyle="--" if dashed else "-",
                shrinkA=1.5,
                shrinkB=1.5,
                zorder=1,
            )
        )

    def route(self, points, *, color=MUTED, dashed=False):
        self.axis.plot(
            *zip(*points[:-1]),
            color=color,
            linewidth=1.4,
            linestyle="--" if dashed else "-",
            zorder=1,
        )
        self.arrow(points[-2], points[-1], color=color, dashed=dashed)

    def source(self, path):
        self.sources[str(path.relative_to(ROOT))] = digest(path)

    def asset(self, path, bounds):
        """Place an existing mark without altering its colors or aspect ratio."""
        self.source(path)
        if path.suffix == ".svg":
            raw = subprocess.run(
                ["rsvg-convert", "--width", "600", str(path)],
                check=True,
                capture_output=True,
            ).stdout
            pixels = Image.open(BytesIO(raw)).convert("RGBA")
        else:
            pixels = Image.open(path).convert("RGBA")
        x, y, width, height = bounds
        axis = self.figure.add_axes((x / 100, y / 100, width / 100, height / 100))
        axis.imshow(pixels)
        axis.set_axis_off()

    def stack(self, x, y, width=9, height=7):
        for offset in (2, 1, 0):
            self.axis.add_patch(
                Rectangle(
                    (x + offset, y + offset),
                    width,
                    height,
                    edgecolor=BLUE,
                    facecolor="#e7f1fa",
                    linewidth=1.2,
                )
            )
        for dx, dy in ((0.25, 0.3), (0.65, 0.65), (0.72, 0.2)):
            self.axis.add_patch(
                Circle((x + width * dx, y + height * dy), width * 0.08, color=TEAL)
            )

    def chip(self, x, y, label):
        self.axis.add_patch(
            Rectangle(
                (x, y), 12, 8, edgecolor=ORANGE, facecolor="#fff7ed", linewidth=1.5
            )
        )
        for dx in (2, 4, 6, 8, 10):
            self.axis.plot([x + dx, x + dx], [y - 1, y], color=ORANGE)
            self.axis.plot([x + dx, x + dx], [y + 8, y + 9], color=ORANGE)
        self.text(
            x + 6, y + 4, label, ha="center", va="center", weight="bold", color=ORANGE
        )

    def gallery_image(self, name, bounds, *, crop=None):
        record_path = GALLERY / "release-media-record.json"
        record = json.loads(record_path.read_text())
        entries = [
            item
            for capture in record["captures"]
            for item in capture["published"]
            if item["path"] == name
        ]
        if len(entries) != 1:
            raise ValueError(f"Expected one published capture for {name}")
        path = GALLERY / name
        if digest(path) != entries[0]["sha256"]:
            raise ValueError(f"Gallery hash mismatch: {name}")
        self.source(record_path)
        self.source_image(path, bounds, crop=crop)

    def native_image(self, name, bounds, *, crop=None):
        """Use an unmodified screenshot checked against its native MCP receipt."""
        path = OUTPUT / f"{name}.png"
        record_path = OUTPUT / f"{name}_provenance.json"
        record = json.loads(record_path.read_text())["response"]["results"][0][
            "payloads"
        ][0]
        if not record["captured"] or digest(path) != record["resource"]["sha256"]:
            raise ValueError(f"Native screenshot hash mismatch: {name}")
        self.source(record_path)
        self.source_image(path, bounds, crop=crop)

    def source_image(self, path, bounds, *, crop=None):
        """Place retained pixels and record any editorial detail crop."""
        self.source(path)
        with Image.open(path) as original:
            pixels = original.convert("RGB")
        if crop is not None:
            left, top, right, bottom = crop
            if not (
                0 <= left < right <= pixels.width and 0 <= top < bottom <= pixels.height
            ):
                raise ValueError(f"Invalid crop for {path.name}: {crop}")
            self.crops.append(
                {
                    "source": str(path.relative_to(ROOT)),
                    "xyxy_pixels": list(crop),
                    "source_size": list(pixels.size),
                }
            )
            pixels = pixels.crop(crop)
        x, y, width, height = bounds
        axis = self.figure.add_axes((x / 100, y / 100, width / 100, height / 100))
        axis.imshow(pixels, interpolation="nearest")
        axis.set_axis_off()

    def save(self):
        OUTPUT.mkdir(parents=True, exist_ok=True)
        outputs = []
        for extension in ("png", "pdf", "svg"):
            path = OUTPUT / f"{self.stem}.{extension}"
            self.figure.savefig(path, dpi=300)
            if extension == "svg":
                normalize_generated_svg(path)
            outputs.append(path)
        plt.close(self.figure)
        receipt = {
            "generator_sha256": digest(Path(__file__)),
            "source_sha256": self.sources,
            "ui_crops": self.crops,
            "output_sha256": {p.name: digest(p) for p in outputs},
            "interpretation": "Original explanatory layout; retained captures are not new scientific evaluations",
        }
        (OUTPUT / f"{self.stem}_provenance.json").write_text(
            json.dumps(receipt, indent=2) + "\n"
        )
        print(f"Rendered {self.stem}")


def h001_scored():
    """Native witnesses from the exact fresh author evaluated in Figure 5B."""
    sheet = FigureSheet("h001_scored_native", "", 6.4)
    sheet.source(
        ROOT / "figure-collection-20261004/H001-FRESH586-SCORED-NATIVE-REVIEW.rst"
    )
    evaluation_path = (
        ROOT / "paper/supplementary/task_only_analysis/h001-fresh586-postfreeze-evaluation.json"
    )
    sheet.source(evaluation_path)
    evaluation = json.loads(evaluation_path.read_text())
    first, final = evaluation["attempts"]
    sheet.text(
        3, 97, "H001: native views from the scored task-only run",
        size=18, weight="bold", va="top",
    )
    for y, title, prefix, crop, bottom, height in (
        (89, "A  Matched overview", "overview", (553, 40, 995, 478), 47, 36),
        (41, "B  Elongated-body false split repaired", "detail", (297, 28, 1037, 492), 9, 26),
    ):
        sheet.text(3, y, title, size=15, weight="bold")
        for x, stage, label in (
            (3, "raw", "Raw"), (35, "first", "First, a01"), (67, "final", "Final, a04")
        ):
            sheet.text(x, y - 5, label, size=14)
            sheet.source_image(
                OUTPUT / "h001_scored_sources" / f"{prefix}_{stage}.png",
                (x, bottom, 29, height), crop=crop,
            )
    sheet.text(
        3, 3,
        f"Object F1 {first['derived_f1']:.3f} → {final['derived_f1']:.3f}; "
        f"{final['score']['false_negative_objects']} reference misses remain.",
        size=14,
    )
    sheet.save()


def task_only_story():
    """Main-text native evidence and scores from the same frozen author runs."""
    from build_slas_task_only import (
        BBBC039_SOURCE, H001_SOURCE, load_evaluations, plot_coverage, plot_pair,
    )

    h001, bbbc039 = load_evaluations(ROOT)
    with plt.rc_context({"font.size": 14, "axes.titlesize": 15,
                         "axes.spines.top": False, "axes.spines.right": False}):
        sheet = FigureSheet("task_only_visual", "", 8.2)
        for path in (H001_SOURCE, BBBC039_SOURCE,
                     Path("paper/figures/build_slas_task_only.py"),
                     Path("figure-collection-20261004/H001-FRESH586-SCORED-NATIVE-REVIEW.rst")):
            sheet.source(ROOT / path)
        sheet.text(3, 98, "Autonomous segmentation: repair and field coverage",
                   size=18, weight="bold", va="top")
        sheet.text(3, 93, "A  H001: an elongated-body split repaired",
                   size=15, weight="bold")
        for x, stage, label in ((3, "raw", "Raw"), (35, "first", "First"),
                                (67, "final", "Final")):
            sheet.text(x, 89, label, size=14)
            sheet.source_image(
                OUTPUT / "h001_scored_sources" / f"detail_{stage}.png",
                (x, 64, 30, 24), crop=(297, 28, 1037, 492),
            )
        sheet.text(50, 64, "Own image review; no reference feedback",
                   size=14, ha="center", color=MUTED)
        axes = (sheet.figure.add_axes((.09, .37, .35, .23)),
                sheet.figure.add_axes((.60, .37, .35, .23)),
                sheet.figure.add_axes((.09, .12, .86, .15)))
        first, final = h001["attempts"]
        plot_pair(axes[0], first["derived_f1"], final["derived_f1"],
                  "B  H001: same whole image", "Notebook-derived reference", font_size=16)
        paired = bbbc039["first_vs_final_same_three"]
        plot_pair(axes[1], paired["first"]["micro_f1"], paired["final"]["micro_f1"],
                  "C  BBBC039: same three fields", "Independent annotations", font_size=16)
        plot_coverage(axes[2], bbbc039, font_size=14)
        axes[2].set_title("D  BBBC039: final coverage, all 200 fields")
        for axis in axes:
            axis.grid(axis="y", color="#d9e0e5", linewidth=.6)
            axis.set_axisbelow(True)
        sheet.text(50, 2,
                   "Independent full-200 repeat: caption and Supplementary Figure 15",
                   size=12, ha="center", color=MUTED)
        sheet.save()


def h002_measurement_first():
    """Retained native views and postfreeze centre agreement, without scoring."""
    import tifffile
    source_root = OUTPUT / "h002_firstmethod_sources"
    source_path = source_root / "source-receipt.json"
    evaluation_path = ROOT / "paper/supplementary/task_only_analysis/h002-fresh15-postfreeze-evaluation.json"
    sources = json.loads(source_path.read_text())
    evaluation = json.loads(evaluation_path.read_text())
    if sources["author_run"] != evaluation["author_run"]:
        raise ValueError("Native captures and evaluation name different authors")
    volumes = {}
    for role in ("raw", "labels", "measurements"):
        record = sources["frozen_scientific_inputs"][role]
        path = Path(record["path"])
        if digest(path) != record["sha256"]:
            raise ValueError(f"Frozen scientific input changed: {role}")
        if role == "measurements":
            with path.open(newline="") as stream:
                centres = np.array([
                    [float(row[f"center_{axis}"]) for axis in "zyx"]
                    for row in csv.DictReader(stream)
                ])
        else:
            volumes[role] = tifffile.imread(path)
    expected_shape = tuple(sources["scientific_scope"]["source_shape"])
    if any(volume.shape != expected_shape for volume in volumes.values()):
        raise ValueError("Frozen raw and label volumes do not share the declared ZYX shape")
    presentation = sources["orthogonal_presentation"]
    with plt.rc_context({"font.size": 13, "axes.spines.top": False,
                         "axes.spines.right": False}):
        sheet = FigureSheet("h002_measurement_first", "", 7.3)
        sheet.source(source_path)
        sheet.source(evaluation_path)
        sheet.source(ROOT / "figure-collection-20261004/H002-FRESH15-INDEPENDENT-CENTRES-REVIEW.rst")
        sheet.text(3, 98, "Measurement-first autonomous 3D localisation",
                   size=17, weight="bold", va="top")
        for name, bounds, heading_position in (
            ("xy", (3, 42, 47, 49), (3, 93)),
            ("xz", (55, 73, 42, 18), (55, 93)),
            ("yz", (55, 45, 42, 18), (55, 65)),
        ):
            if name == "xy":
                capture = sources["captures"][name]
                path = source_root / capture["asset"]
                if digest(path) != capture["sha256"]:
                    raise ValueError(f"Frozen native capture changed: {name}")
                sheet.text(*heading_position, capture["panel_heading"], size=13, weight="bold")
                sheet.source_image(path, bounds, crop=tuple(capture["crop_xyxy"]))
                continue
            plane = presentation["planes"][name]
            fixed_axis, index = plane["fixed_axis"], plane["index"]
            raw = np.take(volumes["raw"], index, axis=fixed_axis)
            labels = np.take(volumes["labels"], index, axis=fixed_axis)
            sheet.text(*heading_position, plane["panel_heading"], size=13, weight="bold")
            axis = sheet.figure.add_axes(tuple(value / 100 for value in bounds))
            low, high = presentation["raw_contrast_limits"]
            axis.imshow(raw, cmap="gray", vmin=low, vmax=high, interpolation="nearest")
            for identity in np.unique(labels):
                if identity:
                    axis.contour(labels == identity, levels=[0.5],
                                 colors=[presentation["outline_color"]], linewidths=0.9)
            in_plane = centres[np.abs(centres[:, fixed_axis] - index) <=
                               presentation["centre_plane_tolerance_voxels"]]
            projected = np.delete(in_plane, fixed_axis, axis=1)
            axis.scatter(projected[:, 1], projected[:, 0], s=65, marker="+",
                         color=presentation["centre_color"], linewidths=1.8)
            axis.set_xlim(-0.5, raw.shape[1] - 0.5)
            axis.set_ylim(raw.shape[0] - 0.5, -0.5)
            axis.set_axis_off()
        sheet.text(55, 70, "Y = 157 voxels", size=11, color=MUTED)
        sheet.text(55, 42, "X = 80 voxels", size=11, color=MUTED)
        sheet.text(3, 36, sources["presentation_note"],
                   size=11, color=MUTED)
        axis = sheet.figure.add_axes((.12, .14, .39, .18))
        thresholds = (10, evaluation["primary_threshold_voxels"])
        matches = [evaluation["scores"][str(value)]["true_positives"] for value in thresholds]
        total = evaluation["scores"][str(thresholds[-1])]["reference_points"]
        axis.bar((0, 1), matches, color=(BLUE, TEAL), width=.5)
        for index, matched in enumerate(matches):
            axis.text(index, matched + .3, f"{matched}/{total}", ha="center", size=13)
        axis.set(xticks=(0, 1), xticklabels=(f"{thresholds[0]} voxels", f"{thresholds[1]} voxels\n(primary)"),
                 ylim=(0, total+2), yticks=(0, 5, 10, 15), ylabel="Matched centres")
        axis.set_title("D  Postfreeze one-to-one matching", size=13)
        axis.grid(axis="y", color="#d9e0e5", linewidth=.6)
        axis.set_axisbelow(True)
        primary = evaluation["scores"][str(thresholds[-1])]
        sheet.text(58, 31, f"{primary['predicted_points']} candidate centres", size=15, weight="bold")
        sheet.text(58, 26, f"Mean matched error: {primary['mean_localisation_error_voxels']:.2f} voxels", size=12)
        sheet.text(58, 21, f"{primary['false_positives']} predictions unmatched to annotations", size=12)
        sheet.text(58, 15, "Annotation completeness is unestablished;\nunmatched does not mean biologically false", size=11, color=MUTED)
        sheet.text(50, 3, "One scientific method • technical rerun only • localisation, not boundary accuracy",
                   size=11, ha="center", color=MUTED)
        sheet.save()


def h002_fresh22_split_repair():
    """Frozen same-coordinate categorical labels, not a new segmentation."""
    sources = OUTPUT / "h002_fresh22_sources"
    receipt_path = sources / "source-receipt.json"
    receipt = json.loads(receipt_path.read_text())
    sheet = FigureSheet("h002_fresh22_split_repair", "", 6.4)
    sheet.source(receipt_path)
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h002-fresh22-postfreeze-localisation.rst")
    sheet.text(3, 97, "Autonomous repair of a continuous-body split", size=17,
               weight="bold", va="top")
    for name, x, y, heading in (
        ("raw", 3, 53, "A  Unchanged raw image"),
        ("first-labels", 52, 53, "B  First instance labels"),
        ("final-labels", 3, 13, "C  Repaired instance labels"),
        ("final-combined", 52, 13, "D  Repaired labels + raw"),
    ):
        path = sources / f"{name}.png"
        if digest(path) != receipt["captures"][name]["sha256"]:
            raise ValueError(f"Frozen H002 capture changed: {name}")
        sheet.text(x, y + 35, heading, size=13, weight="bold")
        sheet.source_image(path, (x, y, 45, 32), crop=(610, 28, 1250, 448))
    sheet.text(3, 7, "Same XY viewport, Z index 36; categorical colours are not shared IDs.",
               size=12, color=MUTED)
    sheet.text(3, 2, "Local partition repair, not proof of complete volume segmentation.",
               size=12, color=MUTED)
    sheet.save()


def retina_matched_repair():
    """Same raw presentation before and after a retained retinal repair."""
    source_root = OUTPUT / "retina_fresh16_sources"
    sheet = FigureSheet("retina_fresh16_repair", "", 5.4)
    sheet.source(ROOT / "figure-collection-20261004/R0010-FRESH16-INDEPENDENT-FIRST-REVIEW.rst")
    sheet.text(3, 97, "Retinal body outlines: local repair and remaining ambiguity",
               size=16, weight="bold", va="top")
    for row, (region, title) in enumerate((
        ("nw", "Bright neighbouring bodies remain separate"),
        ("edge", "Border outlines smooth; possible split remains"),
    )):
        y = 53 - row * 38
        sheet.text(3, y + 35, title, size=13, weight="bold")
        for column, (view, label) in enumerate((
            ("raw", "Raw RBPMS"),
            ("first", "First candidate + raw"),
            ("final", "Repaired candidate + raw"),
        )):
            x = 3 + column * 32
            letter = chr(ord("A") + 3 * row + column)
            sheet.text(x, y + 28, f"{letter}  {label}", size=11, weight="bold")
            sheet.source_image(source_root / f"{region}-{view}.png",
                               (x, y, 30, 26), crop=(297, 28, 1250, 470))
    sheet.text(50, 5, "Matched pixels and display • self-directed retained-run repair",
               size=12, ha="center", color=MUTED)
    sheet.text(50, 1, "Local geometry improvement; no manual-count accuracy estimate",
               size=11, ha="center", color=MUTED)
    sheet.save()


def translocation_repeat():
    """Plot frozen native well summaries, without rerunning scientific analysis."""
    source_path = ROOT / "paper/supplementary/task_only_analysis/bbbc013-fresh13-plot-source.json"
    source = json.loads(source_path.read_text())
    if source["author_run"] != "BBBC013_FRESH13_88":
        raise ValueError("Expected the frozen fresh13 translocation author")
    tables = source["tables"]
    with plt.rc_context({"font.size": 12, "axes.titlesize": 13,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.linewidth": 1.5, "xtick.major.width": 1.5,
                         "ytick.major.width": 1.5}):
        sheet = FigureSheet("translocation_fresh13", "", 6.3)
        sheet.source(source_path)
        sheet.source(ROOT / "figure-collection-20261004/BBBC013-FRESH13-DEVELOPMENT-VISUAL-REVIEW.rst")
        sheet.text(3, 97, "Fresh-context analysis recovers translocation response",
                   size=16, weight="bold", va="top")
        for index, (block, unit, color) in enumerate(
            (("Wortmannin", "nM", BLUE), ("LY294002", "uM", TEAL))
        ):
            rows = sorted(
                (row for row in tables["dose_response"]["rows"]
                 if row["assay_block"] == block and row["assay_role"] in {"empty", "dose"}),
                key=lambda row: float(row["concentration"]),
            )
            if any(row["concentration_unit"] != unit or row["treatment"] != block
                   or int(row["finite_wells"]) != 4 for row in rows):
                raise ValueError("Dose plots require the declared treatment, units and four wells")
            left = .09 + .49 * index
            dose_axis = sheet.figure.add_axes((left, .52, .36, .33))
            positions = list(range(len(rows)))
            dose_axis.errorbar(
                positions, [float(row["mean_well_ratio"]) for row in rows],
                yerr=[float(row["replicate_sd"]) for row in rows],
                fmt="o-", color=color, capsize=4, linewidth=2.2, markersize=6,
                elinewidth=2.0, capthick=2.0, markeredgewidth=1.2,
            )
            dose_axis.set(
                title=f"{'AB'[index]}  {block}", ylim=(0, 9),
                ylabel="Nuclear / cytoplasmic GFP",
                xlabel=f"Concentration ({'µM' if unit == 'uM' else unit})",
                xticks=positions,
                xticklabels=[f"{float(row['concentration']):g}" for row in rows],
            )
            dose_axis.tick_params(axis="x", labelrotation=45, labelsize=12)
            statistics, = (row for row in tables["assay_statistics"]["rows"]
                           if row["assay_block"] == block)
            control_axis = sheet.figure.add_axes((left, .13, .36, .21))
            control_axis.bar(
                (0, 1), (float(statistics["negative_mean"]), float(statistics["positive_mean"])),
                yerr=(float(statistics["negative_replicate_sd"]),
                      float(statistics["positive_replicate_sd"])),
                color=(MUTED, color), width=.5, capsize=4,
                edgecolor=INK, linewidth=1.5,
                error_kw={"elinewidth": 2.0, "capthick": 2.0},
            )
            control_axis.set(
                title=f"{'CD'[index]}  Controls: Z′ = {float(statistics['z_prime']):.3f}",
                xticks=(0, 1), xticklabels=("Vehicle", "Wortmannin\n150 nM"),
                ylabel="GFP ratio", ylim=(0, 9),
            )
            for axis in (dose_axis, control_axis):
                axis.set_yticks((0, 2, 4, 6, 8))
                axis.grid(axis="y", color="#d9e0e5", linewidth=.6)
                axis.set_axisbelow(True)
        sheet.text(50, 3, "Means ± between-well SD; four wells per group. Dose positions equally spaced.",
                   size=12, ha="center", color=MUTED)
        sheet.save()


def bbbc039_repeat():
    """Compare independent frozen authors using their existing score receipts."""
    from build_slas_task_only import BBBC039_SOURCE

    earlier_path = ROOT / BBBC039_SOURCE
    repeat_path = ROOT / "figure-collection-20261004/bbbc039-fresh10coverage-postfreeze-evaluation.json"
    earlier = json.loads(earlier_path.read_text())
    repeat = json.loads(repeat_path.read_text())
    if digest(earlier_path) != repeat["comparison612"]["report_sha256"]:
        raise ValueError("Repeat comparison must use the exact earlier receipt")
    key = lambda row: (row["source_set_id"], row["channel"], row["partition"])
    previous = {key(row): row for row in earlier["instance_metrics"]}
    current = {key(row): row for row in repeat["instance_metrics"]}
    if len(previous) != 200 or previous.keys() != current.keys():
        raise ValueError("Independent repeat requires the same 200 field identities")
    if repeat["match_iou"] != earlier["match_iou"] or repeat["match_iou"] != .5:
        raise ValueError("Independent repeat requires the same IoU matching rule")
    for identity, row in current.items():
        if row["reference_count"] != previous[identity]["reference_count"]:
            raise ValueError("Reference population changed between authors")

    with plt.rc_context({"font.size": 14, "axes.titlesize": 15,
                         "axes.spines.top": False, "axes.spines.right": False}):
        sheet = FigureSheet("bbbc039_independent_repeat", "", 4.9)
        sheet.source(earlier_path)
        sheet.source(repeat_path)
        sheet.text(3, 98, "Independent authors: agreement across the same 200 fields",
                   size=18, weight="bold", va="top")
        scatter = sheet.figure.add_axes((.09, .27, .35, .55))
        pooled = sheet.figure.add_axes((.61, .27, .35, .55))
        for empty, color, label in (
            (False, BLUE, "Annotated fields"),
            (True, ORANGE, "Annotation-empty fields (n=3)"),
        ):
            rows = [row for row in current.values()
                    if (row["reference_count"] == 0) == empty]
            scatter.scatter([100 * previous[key(row)]["f1"] for row in rows],
                            [100 * row["f1"] for row in rows],
                            s=24, alpha=.75, color=color, label=label, zorder=3)
        scatter.plot((0, 100), (0, 100), "--", color=MUTED, linewidth=1)
        scatter.set(title="A  Paired field scores", xlabel="Earlier author F1 (%)",
                    ylabel="Independent repeat F1 (%)", xlim=(-3, 103), ylim=(-3, 103))
        scatter.set_aspect("equal", adjustable="box")
        for offset, record, color, label in (
            (-.18, earlier, BLUE, "Earlier author"),
            (.18, repeat, TEAL, "Independent repeat"),
        ):
            values = [100 * record["summary"][name]
                      for name in ("precision", "recall", "micro_f1")]
            bars = pooled.bar([index + offset for index in range(3)], values,
                              width=.34, color=color, label=label)
            pooled.bar_label(bars, labels=[f"{value:.2f}" for value in values],
                             padding=3, fontsize=12, rotation=90)
        pooled.set(title="B  Pooled object agreement", ylabel="Agreement (%)",
                   xticks=(0, 1, 2), xticklabels=("Precision", "Recall", "F1"),
                   ylim=(0, 112), yticks=(0, 20, 40, 60, 80, 100))
        pooled.legend(frameon=False, fontsize=11, loc="upper center",
                      bbox_to_anchor=(.5, -.24), ncol=2)
        for axis in (scatter, pooled):
            axis.grid(color="#d9e0e5", linewidth=.6)
            axis.set_axisbelow(True)
        counts = repeat["distribution"]
        sheet.text(50, 4,
                   f"{counts['improved_vs612']} fields improved; "
                   f"{counts['regressed_vs612']} lower; "
                   f"{counts['unchanged_vs612']} unchanged",
                   size=14, ha="center", color=MUTED)
        sheet.save()


def h004_junction():
    """Retained neurite support repair, separate from crossing ownership."""
    sheet = FigureSheet("h004_junction_native", "", 6.3)
    sheet.source(ROOT / "figure-collection-20261004/H004-FRESH10-NATIVE-REVIEW.rst")
    metrics_path = ROOT / "paper/supplementary/task_only_analysis/h004-fresh10/final-metrics.json"
    sheet.source(metrics_path)
    metrics = json.loads(metrics_path.read_text())
    for attempt in ("BIO04", "BIO06"):
        sheet.source(ROOT / f"paper/supplementary/task_only_analysis/h004-fresh10/{attempt}.py")
    sheet.text(3, 97, "Neurite support: a recovered junction, remaining gaps", size=18, weight="bold", va="top")
    for x, y, name, label in (
        (3, 53, "raw", "A  Raw process channel"),
        (52, 53, "before", "B  Before: ridge-derived support"),
        (3, 12, "final", "C  Final: strong-raw support added"),
        (52, 12, "combined", "D  Final raw + skeleton / soma"),
    ):
        sheet.text(x, y + 35, label, size=14, weight="bold")
        sheet.source_image(
            OUTPUT / "h004_junction_sources" / f"{name}.png",
            (x, y, 45, 32), crop=(297, 28, 1250, 430),
        )
    sheet.text(
        3, 5,
        f"Selected bright-junction tile: {metrics['junction_raw20_count']} strong raw pixels; "
        f"{metrics['junction_raw20_missing_final']} excluded in final support.",
        size=14,
    )
    sheet.text(3, 1, "Local support recovery is not complete tracing or neuron ownership.", size=14)
    sheet.save()


def h004_faint_path():
    """Independent local recovery with visible sensitivity costs."""
    sheet = FigureSheet("h004_fresh20_faint_path", "", 6.3)
    sources = OUTPUT / "h004_fresh20_sources"
    index_path = sources / "QA-INDEX.json"
    measurements_path = sources / "ATTEMPT-MEASUREMENTS.csv"
    sheet.source(index_path)
    sheet.source(measurements_path)
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h004-fresh20-qualified-completion.rst")
    captures = {item["capture_group"]: item for item in json.loads(index_path.read_text())}
    with measurements_path.open(newline="") as stream:
        measurements = {row["attempt"]: row for row in csv.DictReader(stream)}
    first, final = measurements["first"], measurements["repair03"]
    sheet.text(3, 97, "Faint-path recovery adds uncertain short branches", size=17, weight="bold", va="top")
    for x, y, name, heading in (
        (3, 53, "first-bottom-raw", "A  Raw process-rich channel"),
        (52, 53, "first-bottom-result", "B  First result"),
        (3, 12, "repair03-bottom-result", "C  Final result"),
        (52, 12, "repair03-bottom-combined", "D  Final raw + result"),
    ):
        path = sources / f"{name}.png"
        if digest(path) != captures[name]["sha256"]:
            raise ValueError(f"Retained capture hash mismatch: {name}")
        sheet.text(x, y + 35, heading, size=13, weight="bold")
        sheet.source_image(path, (x, y, 45, 32), crop=(297, 28, 1250, 410))
    sheet.text(
        3, 5,
        f"Whole-field graph length: {float(first['total_outgrowth']):,.0f} → "
        f"{float(final['total_outgrowth']):,.0f} px; algorithm branches: "
        f"{first['total_branches']} → {final['total_branches']}.",
        size=13,
    )
    sheet.text(3, 1, "Eight soma candidates retained; neuron-specific topology remains uncertain.", size=13)
    sheet.save()


def assay_review_sheets():
    """Keep related native witnesses on one assay sheet, with original receipts."""
    groups = (
        ("h001_assay_review", "Bright-object separation", ("h001_scored_native",)),
        ("h002_assay_review", "Volumetric localisation and body separation", ("h002_fresh22_split_repair", "h002_fresh10_native")),
        ("retina_assay_review", "Retinal soma localisation", ("retina_fresh16_repair", "retinal_development_repair")),
        ("h003_assay_review", "Paired nuclear and cell-body analysis", ("h003_fresh656_native", "h003_fresh19_matched")),
        ("h004_assay_review", "Neurite main-shaft recovery", ("h004_main_shafts", "h004_junction_native")),
    )
    for stem, title, panels in groups:
        sheet = FigureSheet(stem, title, 5.2 * len(panels))
        height = 88 / len(panels)
        for index, panel in enumerate(panels):
            sheet.asset(OUTPUT / f"{panel}.png", (2, 5 + (len(panels) - index - 1) * height, 96, height - 2))
        sheet.save()


def h004_main_shafts():
    """Show the retained initial shaft result, not a fine-branch sensitivity trial."""
    sheet = FigureSheet("h004_main_shafts", "Main-shaft recovery", 4.2)
    sources = OUTPUT / "h004_fresh20_sources"
    index_path = sources / "QA-INDEX.json"
    sheet.source(index_path)
    captures = {item["capture_group"]: item for item in json.loads(index_path.read_text())}
    for x, name, title in ((3, "first-bottom-raw", "A  Raw process channel"), (52, "first-bottom-result", "B  Main-shaft result")):
        path = sources / f"{name}.png"
        if digest(path) != captures[name]["sha256"]:
            raise ValueError(f"Retained capture hash mismatch: {name}")
        sheet.text(x, 87, title, size=13, weight="bold")
        sheet.source_image(path, (x, 12, 45, 69), crop=(297, 28, 1250, 410))
    sheet.save()


def personal_stitched_development():
    """Retained development witnesses, not a fresh autonomous score."""
    sheet = FigureSheet("p001_stitched_dev13_native", "", 6.2)
    sheet.source(ROOT / "figure-collection-20261004/P001-STITCHED-DEV13-INDEPENDENT-REVIEW.rst")
    source_root = OUTPUT / "p001_stitched_dev13_sources"
    record_path = source_root / "capture-records.json"
    sheet.source(record_path)
    records = {item["phase"]: item["record"] for item in json.loads(record_path.read_text())}
    sheet.text(3, 97, "Nine-field neurite mosaic: retained-context development", size=16, weight="bold", va="top")
    for row, (region, suffix, heading) in enumerate((
        ("seam", "96", "Sampled tile overlap"),
        ("bottom", "97", "Lower-right field core"),
    )):
        y = 53 - row * 39
        sheet.text(3, y + 35, heading, size=13, weight="bold")
        for column, (view, label) in enumerate((
            ("raw", "Raw FITC"),
            ("result", "Bodies + paths"),
            ("combined", "Raw + result"),
        )):
            phase = f"{region}-{view}{suffix}"
            path = source_root / f"{phase}.png"
            record = records[phase]
            if not record["captured"] or digest(path) != record["resource"]["sha256"]:
                raise ValueError(f"Native screenshot hash mismatch: {phase}")
            x = 3 + column * 32
            letter = chr(ord("A") + row * 3 + column)
            sheet.text(x, y + 29, f"{letter}  {label}", size=12, weight="bold")
            sheet.source_image(path, (x, y, 30, 25), crop=(297, 28, 1250, 492))
    sheet.text(3, 7, "Shared channel-stack fit; acquisition-derived placement.", size=12)
    sheet.text(3, 4, "Faint paths and crowded ownership remain incomplete.", size=12)
    sheet.text(3, 1, "Attempt08 development outputs—not final09 validation or a fresh autonomous pass.", size=12)
    sheet.save()


def submission_neurite_results():
    """Show the retained shaft illustration without promoting an overextended repair."""
    sheet = FigureSheet("submission_neurite_results", "", 10.1)
    public = OUTPUT / "h004_fresh20_sources"
    personal = OUTPUT / "p001_fresh13_sources"
    sheet.source(public / "QA-INDEX.json")
    sheet.source(personal / "source-record.rst")
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h004-fresh20-qualified-completion.rst")
    sheet.source(ROOT / "figure-collection-20261004/P001-FRESH13-NINE-FIELD-REVIEW.rst")
    sheet.panel("I", "Public neurites: thick-shaft recovery", 3, 97)
    for x, name, title in (
        (3, "first-bottom-raw", "A  Raw process channel"),
        (52, "first-bottom-result", "B  Initial shaft result"),
    ):
        sheet.text(x, 91, title, size=10.5, weight="bold")
        sheet.source_image(public / f"{name}.png", (x, 70, 45, 18), crop=(297, 28, 1250, 410))
    sheet.text(3, 67, "Retained shaft candidate; fine filopodia are outside this endpoint.", size=10, color=MUTED)
    sheet.panel("II", "Laboratory neurites: final autonomous analysis", 3, 62)
    for x, name, title in (
        (3, "raw", "C  Raw FITC"),
        (35, "result", "D  Body and path result"),
        (67, "combined", "E  Combined"),
    ):
        sheet.text(x, 57, title, size=10.5, weight="bold")
        sheet.source_image(personal / f"site1-{name}.png", (x, 32, 30, 23), crop=(550, 28, 997, 437))
    sheet.panel("III", "Fixed-recipe transfer: treatment responses", 3, 28)
    sheet.source(OUTPUT / "personal_neurite_effects_transfer_provenance.json")
    sheet.source_image(OUTPUT / "personal_neurite_effects_transfer.png", (3, 3, 94, 23),
                       crop=(90, 280, 2640, 1125))
    sheet.text(3, 1, "Twenty matched wells; two technical wells per dose. Branching remains under investigation.",
               size=9.5, color=MUTED)
    sheet.save()


def submission_shared_workflow():
    """Combine the workflow diagram with its retained native editing evidence."""
    sheet = FigureSheet("submission_shared_workflow", "", 9.1)
    sheet.source(OUTPUT / "shared_workflow_provenance.json")
    sheet.source(OUTPUT / "authoring_verified_roundtrip_provenance.json")
    sheet.panel("I", "Shared analysis and execution", 3, 97)
    sheet.source_image(OUTPUT / "shared_workflow.png", (3, 45, 94, 50))
    sheet.panel("II", "Editable workflow", 3, 42)
    sheet.native_image("authoring_main_verified_capture", (3, 6, 33, 34))
    sheet.panel("III", "Execution server", 39, 42)
    sheet.native_image("authoring_server_browser_verified_capture", (39, 30, 58, 10))
    sheet.panel("IV", "Controls", 39, 27)
    sheet.panel("V", "Matching Python", 68, 27)
    sheet.native_image(
        "authoring_function_verified_capture", (39, 5, 25, 20), crop=(25, 153, 193, 290)
    )
    sheet.native_image(
        "authoring_code_verified_capture", (68, 5, 29, 20), crop=(74, 96, 292, 222)
    )
    sheet.save()


def submission_quantitative_results():
    """Show assay response, 3-D localisation and noisy retinal soma detection."""
    sheet = FigureSheet("submission_quantitative_results", "", 10.5)
    sheet.source(OUTPUT / "translocation_fresh23_provenance.json")
    sheet.source(OUTPUT / "h002_measurement_first_provenance.json")
    sheet.panel("I", "Translocation response", 3, 97)
    sheet.source_image(OUTPUT / "translocation_fresh23.png", (3, 67, 94, 26),
                       crop=(50, 270, 2650, 1290))
    sheet.panel("II", "Three-dimensional nuclear localisation", 3, 63)
    sheet.source_image(OUTPUT / "h002_measurement_first.png", (3, 31, 94, 29),
                       crop=(50, 110, 2660, 1300))
    sheet.panel("III", "Retinal somata in heterogeneous background", 3, 28)
    sheet.source(OUTPUT / "retinal_fresh_native_provenance.json")
    sheet.text(3, 24, "Raw RBPMS", size=10.5, weight="bold")
    sheet.text(52, 24, "Final outlines", size=10.5, weight="bold")
    sheet.source_image(OUTPUT / "retinal_fresh_native.png", (3, 2, 45, 21),
                       crop=(24, 790, 747, 1185))
    sheet.source_image(OUTPUT / "retinal_fresh_native.png", (52, 2, 45, 21),
                       crop=(770, 790, 1493, 1185))
    sheet.save()


def architecture():
    sheet = FigureSheet(
        "shared_workflow", "OpenHCS: one editable workflow from images to results", 8.1
    )
    for source in (
        "docs/source/architecture/quick_start.rst",
        "openhcs/core/pipeline_document.py",
        "openhcs/core/compiled_step_plan.py",
        "openhcs/core/runtime_stores.py",
        "openhcs/core/source_bindings.py",
        "openhcs/agent/capabilities.py",
    ):
        sheet.source(ROOT / source)

    logos = ROOT / "website/assets/logos"
    sheet.source(logos / "README.md")
    sheet.panel("A", "Choose how to work: UI editors and MCP bridge", 3, 89)
    # Original desktop pictogram; upstream product marks remain unmodified.
    sheet.axis.add_patch(
        Rectangle((8, 77), 14, 8, edgecolor=PURPLE, facecolor=PALE, linewidth=1.5)
    )
    for y in (79, 81, 83):
        sheet.axis.plot([10, 13, 13, 20], [y, y, y, y], color=PURPLE, linewidth=1.5)
        sheet.axis.add_patch(Circle((15, y), 0.5, color=PURPLE))
    sheet.axis.plot([11, 19], [75.5, 75.5], color=PURPLE, linewidth=2)
    sheet.asset(logos / "python.svg", (34, 77, 10, 9))
    sheet.asset(logos / "mcp.svg", (59, 77, 8, 8))
    sheet.asset(logos / "cellprofiler.png", (82, 77, 10, 9))
    for x, label in (
        (15, "Desktop forms"),
        (39, "Python code"),
        (63, "Agent conversation"),
        (87, "CellProfiler import"),
    ):
        sheet.text(x, 73.5, label, size=10.5, ha="center", weight="bold")
        sheet.arrow((x, 71.5), (x, 67.5), both=x != 87, color=PURPLE)
        sheet.text(
            x + 2, 69.5, "Import" if x == 87 else "Edit", size=10.5, color=PURPLE
        )

    sheet.axis.add_patch(
        FancyBboxPatch(
            (4, 39),
            92,
            28,
            boxstyle="round,pad=0.4",
            facecolor="#edf7f5",
            edgecolor=TEAL,
        )
    )
    sheet.text(
        50,
        63.5,
        "SHARED PIPELINE  •  configuration + ordered function steps",
        size=12,
        ha="center",
        weight="bold",
        color=TEAL,
    )
    sheet.stack(7, 48)
    for x, title in ((24, "Prepare"), (48, "Segment"), (72, "Measure")):
        sheet.box(x, 49, 19, 9, title, "Python function", color=TEAL)
    for start, end in ((19, 24), (43, 48), (67, 72)):
        sheet.arrow((start, 53.5), (end, 53.5), color=TEAL)
    sheet.text(12, 44, "Named images", size=11, ha="center")
    sheet.text(
        59,
        43,
        "Choose stack axes, processing groups,\nfunction chains and named results",
        size=11,
        ha="center",
    )

    sheet.panel("B", "Connect data and processing tools", 3, 34)
    sheet.asset(logos / "bioformats.svg", (6, 24, 9, 7))
    sheet.text(18, 28.5, "Image folders · Bio-Formats", size=10.5, va="center")
    sheet.text(18, 24, "OME-Zarr · OMERO (experimental)", size=11, va="center")
    sheet.asset(logos / "zarr.svg", (40, 23.5, 10, 8))
    for name, x in (("cupy.svg", 58), ("pytorch.svg", 70), ("jax.png", 82)):
        sheet.asset(logos / name, (x, 24, 8, 7))
    sheet.text(74, 21, "Scientific Python + custom functions", size=11, ha="center")
    sheet.route(((8, 31), (1.5, 31), (1.5, 53), (6, 53)), color=BLUE)
    sheet.route(((93, 28), (98.5, 28), (98.5, 53), (92, 53)), color=ORANGE)
    sheet.text(2.1, 45, "Images", size=11, color=BLUE, rotation=90)
    sheet.text(97, 43, "Functions", size=11, color=ORANGE, rotation=90)

    sheet.panel("C", "Separate execution and viewer processes", 3, 19)
    sheet.route(((50, 39), (50, 36.5), (0.7, 36.5), (0.7, 9), (4, 9)), color=BLUE)
    sheet.text(
        35,
        36.5,
        "Submit workflow",
        size=11,
        color=BLUE,
        ha="center",
        va="center",
        bbox={"facecolor": "white", "edgecolor": "none", "pad": 1},
    )
    sheet.text(11, 9, "ZMQ server", size=12, weight="bold", ha="center", color=BLUE)
    sheet.text(11, 5.5, "Catalog · compile · schedule", size=9.5, ha="center")
    sheet.arrow((20, 9), (26, 9), both=True, color=BLUE)
    sheet.chip(28, 5, "CPU")
    sheet.chip(45, 5, "GPU")
    sheet.text(42.5, 15.5, "Worker processes", size=11, ha="center", weight="bold")
    sheet.text(42.5, 2.3, "Prepared tasks ↔ progress", size=10.5, ha="center", color=BLUE)
    sheet.arrow((59, 9), (65, 9), color=TEAL)
    sheet.stack(67, 6, 6, 5)
    sheet.axis.add_patch(Rectangle((77, 6), 7, 6, edgecolor=TEAL, facecolor="white"))
    for y in (7.5, 9, 10.5):
        sheet.axis.plot([77, 84], [y, y], color=TEAL, linewidth=0.7)
    sheet.axis.plot([79.5, 79.5], [6, 12], color=TEAL, linewidth=0.7)
    sheet.asset(logos / "napari.svg", (87, 6, 5, 6))
    sheet.asset(logos / "fiji.svg", (93, 6, 5, 6))
    sheet.text(81, 2.3, "Images · ROIs · tables", size=11, ha="center")
    sheet.text(
        81, 13.3, "Separate napari / Fiji viewers", size=10.5, ha="center", color=TEAL
    )
    sheet.text(11, 2.3, "Requests ↔ status", size=10.5, ha="center", color=BLUE)
    sheet.save()


def authoring():
    sheet = FigureSheet(
        "editable_analyses", "Edit one analysis through forms, Python or MCP", 9.3
    )
    record_path = OUTPUT / "authoring_verified_roundtrip_provenance.json"
    record = json.loads(record_path.read_text())
    if not record["verified"]:
        raise ValueError("Authoring round trip has not passed native validation")
    sheet.source(record_path)
    field_edits = [
        event["arguments"]
        for event in record["events"]
        if event["tool"] == "openhcs_ui_mutate_object_state_field"
    ]
    if len(field_edits) != 1:
        raise ValueError("Expected one recorded field restoration")
    field_edit = field_edits[0]
    field_label = field_edit["field_path"].replace("_", " ").title() + ":"
    observed = [
        widget["label"]
        for event in record["events"]
        if event["tool"] == "openhcs_ui_get_widget_tree"
        for widget in event["response"]["results"][0]["payloads"][0][
            "actionable_widgets"
        ]
        if widget["class_name"] == "NoScrollDoubleSpinBox"
        and widget["context_label"].endswith(field_label)
    ]
    if not observed or observed[-1] != str(field_edit["value"]):
        raise ValueError("Recorded final field and control do not agree")

    sheet.panel("A", "Main window: the complete workflow", 3, 90)
    sheet.native_image("authoring_main_verified_capture", (3, 53, 60, 35))
    sheet.text(66, 86, "Detail from A: pipeline steps", size=10, color=MUTED)
    sheet.native_image(
        "authoring_main_verified_capture", (66, 63, 31, 20), crop=(516, 230, 1024, 320)
    )
    sheet.panel("B", "ZeroMQ server browser", 3, 49)
    sheet.native_image("authoring_server_browser_verified_capture", (3, 32, 94, 15))
    sheet.panel("C", "Function controls", 3, 29)
    sheet.panel("D", "Matching Python code", 54, 29)
    sheet.native_image(
        "authoring_function_verified_capture", (3, 6, 44, 21), crop=(25, 153, 193, 290)
    )
    sheet.native_image(
        "authoring_code_verified_capture", (54, 6, 43, 21), crop=(74, 96, 292, 222)
    )
    sheet.arrow((48, 17), (53, 17), both=True, color=PURPLE)
    sheet.text(
        50,
        3,
        "The same parameters, in the same order, with the same values",
        size=11,
        ha="center",
        color=TEAL,
        weight="bold",
    )
    sheet.save()


def viewers():
    sheet = FigureSheet(
        "inspectable_results", "Inspect images and objects in familiar viewers", 9.1
    )
    sheet.panel("A", "Fiji: an image plane and its matching ROI list", 3, 90)
    sheet.gallery_image("fiji-review.webp", (3, 53, 61, 34))
    sheet.text(68, 86, "Nine ROI entries", size=10, weight="bold")
    sheet.gallery_image(
        "fiji-review.webp", (68, 64, 29, 20), crop=(822, 112, 1235, 433)
    )
    sheet.text(68, 62, "Nuclear outline", size=10, weight="bold")
    sheet.gallery_image("fiji-review.webp", (75, 54, 15, 7), crop=(421, 497, 493, 550))
    sheet.text(
        50,
        50,
        "NeuronCyto II field 1 • recorded Fiji streaming demonstration",
        size=10,
        ha="center",
        color=MUTED,
    )
    sheet.panel("B", "napari: object selection and image coordinates", 3, 44)
    sheet.gallery_image("napari-roi-navigation-poster.webp", (3, 7, 61, 34))
    sheet.text(68, 40, "Selected object", size=10, weight="bold")
    sheet.gallery_image(
        "napari-roi-navigation-poster.webp", (75, 27, 15, 12), crop=(862, 454, 950, 538)
    )
    sheet.text(68, 25, "Selected list entry", size=10, weight="bold")
    sheet.gallery_image(
        "napari-roi-navigation-poster.webp", (68, 20, 29, 4), crop=(15, 823, 320, 849)
    )
    sheet.text(68, 17, "Channel and Z plane", size=10, weight="bold")
    sheet.gallery_image(
        "napari-roi-navigation-poster.webp", (68, 8, 29, 7), crop=(1446, 507, 1598, 548)
    )
    sheet.text(
        50,
        4,
        "Separate three-plane navigation demonstration • selected object and ROI-list entry",
        size=10,
        ha="center",
        color=MUTED,
    )
    sheet.save()


if __name__ == "__main__":
    plt.rcParams.update(
        {"font.family": "DejaVu Sans", "svg.fonttype": "none", "pdf.fonttype": 42}
    )
    architecture()
    authoring()
    viewers()
