"""Original manuscript diagrams and panels assembled from retained UI captures.

Editorial layout is explicit here. Capture identities and file hashes are read
from the published gallery authority; no UI state or scientific image is invented.
"""

from __future__ import annotations

import csv
import json
import re
from io import BytesIO
from pathlib import Path
import subprocess

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch, Rectangle
from PIL import Image, ImageOps

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

    plot_font_size = 13
    default_input_root = Path("/")

    def __init__(self, stem: str, title: str, height: float = 7.7,
                 *, input_root: Path = default_input_root):
        self.stem = stem
        self.input_root = input_root
        self.figure = plt.figure(figsize=(9, height), facecolor="white")
        self.axis = self.figure.add_axes((0, 0, 1, 1))
        self.axis.set(xlim=(0, 100), ylim=(0, 100))
        self.axis.set_axis_off()
        self.sources: dict[str, str] = {}
        self.crops: list[dict] = []
        self.display_transforms: list[dict] = []
        self.text(3, 97, title, size=16, weight="bold", va="top")

    def text(self, x, y, value, *, size=11, color=INK, **kwargs):
        return self.axis.text(x, y, value, fontsize=size, color=color, **kwargs)

    def plot_axes(self, bounds):
        """Keep numeric plot labels readable on the shared publication canvas."""
        axis = self.figure.add_axes(bounds)
        axis.tick_params(labelsize=self.plot_font_size, colors=INK)
        for label in (axis.xaxis.label, axis.yaxis.label):
            label.set(fontsize=self.plot_font_size, color=INK)
        return axis

    def panel(self, letter, title, x, y):
        self.text(x, y, letter, size=14, weight="bold", color=BLUE)
        self.text(x + 3.1, y, title, size=12, weight="bold")

    def box(self, x, y, width, height, title, detail="", *, color=BLUE, size=11):
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
            size=size,
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
                size=size - 2,
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

    def input_path(self, original: Path) -> Path:
        """Resolve paper-relative inputs or an archived original absolute path."""
        if original.is_absolute():
            return self.input_root / original.relative_to(original.anchor)
        return ROOT / original

    def asset(self, path, bounds, *, trim=False):
        """Place a mark unchanged; optionally remove transparent outer padding."""
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
        if trim:
            crop = pixels.getbbox()
            self.display_transforms.append({
                "source": str(path.relative_to(ROOT)),
                "operation": "Trim transparent outer padding; artwork unchanged",
                "crop_xyxy_pixels": crop,
            })
            pixels = pixels.crop(crop)
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

    def native_image(self, name, bounds, *, crop=None, response_path=("response",),
                     provenance_path=None):
        """Use an unmodified screenshot checked against its native MCP receipt."""
        path = OUTPUT / f"{name}.png"
        record_path = provenance_path or OUTPUT / f"{name}_provenance.json"
        envelope = json.loads(record_path.read_text())
        # Retained CLI command records wrap the native execution response;
        # direct shell receipts retain that response at the document root.
        for key in response_path:
            envelope = envelope[key]
        record = envelope["results"][0]["payloads"][0]
        if not record["captured"] or digest(path) != record["resource"]["sha256"]:
            raise ValueError(f"Native screenshot hash mismatch: {name}")
        self.source(record_path)
        self.source_image(path, bounds, crop=crop)

    def source_image(self, path, bounds, *, crop=None, invert=False):
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
        if invert:
            pixels = ImageOps.invert(pixels)
            self.display_transforms.append({
                "source": str(path.relative_to(ROOT)),
                "operation": "RGB complement (255 - channel); display only",
                "crop_xyxy_pixels": list(crop) if crop else None,
            })
        x, y, width, height = bounds
        axis = self.figure.add_axes((x / 100, y / 100, width / 100, height / 100))
        axis.imshow(pixels, interpolation="nearest")
        axis.set_axis_off()

    def crop_vertical(self, bottom, top):
        """Trim the canvas without shrinking any text or retained image axes."""
        fraction = top - bottom
        positions = [(axis, axis.get_position().bounds) for axis in self.figure.axes]
        width, height = self.figure.get_size_inches()
        self.figure.set_size_inches(width, height * fraction)
        for axis, (left, y, width, height) in positions:
            axis.set_position((left, (y - bottom) / fraction, width, height / fraction))
        self.display_transforms.append({
            "operation": "Vertical canvas crop; axis sizes and type unchanged",
            "bottom_top_fractions": [bottom, top],
        })

    def save(self, *, dpi=300):
        OUTPUT.mkdir(parents=True, exist_ok=True)
        outputs = []
        for extension in ("png", "pdf", "svg"):
            path = OUTPUT / f"{self.stem}.{extension}"
            self.figure.savefig(path, dpi=dpi)
            if extension == "svg":
                normalize_generated_svg(path)
            outputs.append(path)
        plt.close(self.figure)
        receipt = {
            "generator_sha256": digest(Path(__file__)),
            "source_sha256": self.sources,
            "input_root": str(self.input_root),
            "ui_crops": self.crops,
            "display_transforms": self.display_transforms,
            "output_sha256": {p.name: digest(p) for p in outputs},
            "interpretation": "Original explanatory layout; retained captures are not new scientific evaluations",
        }
        (OUTPUT / f"{self.stem}_provenance.json").write_text(
            json.dumps(receipt, indent=2) + "\n"
        )
        print(f"Rendered {self.stem}")


def h001_scored():
    """Matched original pixels and saved detections from the scored author."""
    from build_slas_neurite_views import BRIGHT_OBJECT_SOURCE, CroppedComparison

    from build_slas_task_only import H001_SOURCE, load_bright_object_evaluation

    sheet = FigureSheet("h001_scored_native", "", 3.4)
    sheet.source(ROOT / H001_SOURCE)
    evaluation = load_bright_object_evaluation(ROOT)
    first, final = evaluation["attempts"]
    sheet.text(3, 98, "H001: an elongated-body split repaired",
               size=16, weight="bold", va="top")
    CroppedComparison.read(sheet, BRIGHT_OBJECT_SOURCE).draw_row((3, 20, 94, 60), 86)
    sheet.text(3, 4, f"Object F1 {first['derived_f1']:.3f} → {final['derived_f1']:.3f}; "
               f"{final['score']['false_negative_objects']} reference misses remain.", size=13)
    sheet.save()


def task_only_story():
    """Main-text native evidence and scores from the same frozen author runs."""
    from build_slas_task_only import (
        BBBC039_SOURCE, H001_SOURCE, load_evaluations, plot_coverage, plot_pair,
    )

    h001, bbbc039 = load_evaluations(ROOT)
    with plt.rc_context({"font.size": 14, "axes.titlesize": 15,
                         "axes.spines.top": False, "axes.spines.right": False}):
        sheet = FigureSheet("task_only_visual", "", 9.8)
        for path in (H001_SOURCE, BBBC039_SOURCE,
                     Path("paper/figures/build_slas_task_only.py")):
            sheet.source(ROOT / path)
        sheet.text(3, 98, "Autonomous segmentation: repair and field coverage",
                   size=18, weight="bold", va="top")
        sheet.text(3, 93, "A  H001: an elongated-body split repaired",
                   size=15, weight="bold")
        from build_slas_neurite_views import BRIGHT_OBJECT_SOURCE, CroppedComparison

        CroppedComparison.read(sheet, BRIGHT_OBJECT_SOURCE).draw_row((3, 70, 94, 18), 89)
        sheet.text(50, 70, "Own image review; no reference feedback",
                   size=14, ha="center", color=MUTED)
        axes = (sheet.plot_axes((.09, .40, .35, .24)),
                sheet.plot_axes((.60, .40, .35, .24)),
                sheet.plot_axes((.09, .10, .43, .20)),
                sheet.plot_axes((.64, .10, .31, .20)))
        first, final = h001["attempts"]
        plot_pair(axes[0], first["derived_f1"], final["derived_f1"],
                  "B  H001: same whole image", "Notebook-derived reference", font_size=14)
        paired = bbbc039["first_vs_final_same_three"]
        plot_pair(axes[1], paired["first"]["micro_f1"], paired["final"]["micro_f1"],
                  "C  BBBC039: same three fields", "Independent annotations", font_size=14)
        plot_coverage(axes[2], bbbc039, font_size=sheet.plot_font_size)
        axes[2].set_title("D  Final F1 across 200 fields", fontsize=sheet.plot_font_size)
        annotated = [field["reference_count"] for field in bbbc039["instance_metrics"]]
        predicted = [field["predicted_count"] for field in bbbc039["instance_metrics"]]
        count_limit = max(*annotated, *predicted) * 1.05
        axes[3].scatter(annotated, predicted, s=13, color=TEAL, alpha=.65)
        axes[3].plot((0, count_limit), (0, count_limit), linestyle="--", color=BLUE,
                     linewidth=1.2, label="Equal counts")
        axes[3].set(xlim=(0, count_limit), ylim=(0, count_limit),
                    xlabel="Annotated nuclei", ylabel="Predicted nuclei")
        axes[3].set_title("E  BBBC039 counts", fontsize=sheet.plot_font_size)
        axes[3].legend(frameon=False, fontsize=sheet.plot_font_size, loc="upper left")
        for axis in axes:
            axis.grid(axis="y", color="#d9e0e5", linewidth=.6)
            axis.set_axisbelow(True)
        sheet.text(50, 2,
                   "All 200 fields included; counts complement, rather than replace, object matching.",
                   size=12, ha="center", color=MUTED)
        sheet.save()


class MeasurementFirstVolumeFigure(FigureSheet):
    """One source-owned layout shared by the standalone and main-paper views."""

    def draw_volume_views(self, bounds):
        from build_slas_neurite_views import (
            CentredVolumeOutline, VOLUME_FIRST_METHOD_SOURCE, VolumeROIView,
        )

        xy = VolumeROIView.read(self, VOLUME_FIRST_METHOD_SOURCE)
        xz = CentredVolumeOutline.read(self, VOLUME_FIRST_METHOD_SOURCE, view_index=1)
        yz = CentredVolumeOutline.read(self, VOLUME_FIRST_METHOD_SOURCE, view_index=2)
        x, y, width, height = bounds
        for view, heading, rectangle in (
            (xy, "XY", (x, y, width*.50, height)),
            (xz, f"XZ: Y = {xz.viewport['index']} voxels",
             (x+width*.55, y+height*.60, width*.45, height*.35)),
            (yz, f"YZ: X = {yz.viewport['index']} voxels",
             (x+width*.55, y+height*.05, width*.45, height*.35)),
        ):
            self.text(rectangle[0], rectangle[1]+rectangle[3]+2, heading,
                      size=self.plot_font_size, weight="bold")
            view.draw_overlay(rectangle)


def h002_measurement_first(*, input_root: Path = FigureSheet.default_input_root):
    """Original XY ROI geometry and orthogonal saved masks/centres."""
    evaluation_path = ROOT / "paper/supplementary/task_only_analysis/h002-fresh15-postfreeze-evaluation.json"
    evaluation = json.loads(evaluation_path.read_text())
    with plt.rc_context({"font.size": 13, "axes.spines.top": False,
                         "axes.spines.right": False}):
        sheet = MeasurementFirstVolumeFigure("h002_measurement_first", "", 7.3, input_root=input_root)
        sheet.source(evaluation_path)
        sheet.source(ROOT / "figure-collection-20261004/H002-FRESH15-INDEPENDENT-CENTRES-REVIEW.rst")
        sheet.text(3, 98, "Measurement-first autonomous 3D localisation",
                   size=17, weight="bold", va="top")
        sheet.draw_volume_views((3, 43, 94, 45))
        sheet.text(3, 36, "XY: saved nuclear ROIs, not validated cell borders.\nXZ/YZ: saved-mask outlines and in-plane centres.",
                   size=11, color=MUTED)
        axis = sheet.plot_axes((.12, .14, .39, .18))
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


def h002_independent_centres(*, input_root: Path = FigureSheet.default_input_root):
    """Original final-only XY/XZ/YZ raw voxels and unchanged saved point tables."""
    from build_slas_neurite_views import VOLUME_CENTRE_SOURCE, VolumeCentreView

    sheet = FigureSheet("h002_fresh10_native", "", 7.6, input_root=input_root)
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h002-fresh10-native-source-proof.json")
    sheet.text(3, 98, "Independent volume localisation: final-only witnesses",
               size=16, weight="bold", va="top")
    for index, plane in enumerate(("XY", "XZ", "YZ")):
        view = VolumeCentreView.read(sheet, VOLUME_CENTRE_SOURCE, view_index=index)
        y = 68-index*28
        sheet.text(3, y+25, plane, size=13, weight="bold")
        view.draw_columns((3, y, 94, 20), y+22,
                          (("Raw", view.draw_raw), ("Saved centres", view.draw_overlay)))
    sheet.text(3, 7, "22 algorithmic centres; visibility is slice-local, not a complete census.", size=12)
    sheet.text(3, 3, "Voxel-index geometry; physical calibration and multi-lobed identity remain unverified.", size=11)
    sheet.save()


def h002_fresh22_split_repair(*, input_root: Path = FigureSheet.default_input_root):
    """Same native volume plane from frozen first/final integer labels."""
    from build_slas_neurite_views import VOLUME_REPAIR_SOURCE, VolumeComparison

    sheet = FigureSheet("h002_fresh22_split_repair", "", 6.4, input_root=input_root)
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h002-fresh22-postfreeze-localisation.rst")
    view = VolumeComparison.read(sheet, VOLUME_REPAIR_SOURCE)
    sheet.text(3, 97, "Autonomous repair of a continuous-body split", size=17,
               weight="bold", va="top")
    for index, (heading, draw) in enumerate(view.label_panels):
        row, column = divmod(index, 2)
        x, y = 3+column*49, 53-row*40
        sheet.text(x, y+35, f"{chr(65+index)}  {heading}", size=13, weight="bold")
        draw((x, y, 45, 32))
    sheet.text(3, 7, "Same XY viewport, Z index 36; categorical colours are not shared IDs.",
               size=12, color=MUTED)
    sheet.text(3, 2, "Local partition repair, not proof of complete volume segmentation.",
               size=12, color=MUTED)
    sheet.save()


def nuclear_matched_repair():
    """Show retained local separation and the final faint-neighbour failure."""
    from build_slas_neurite_views import CroppedComparison, NUCLEAR_SOURCE

    sheet = FigureSheet("h003_native_repair", "", 6.6)
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h003-native-source-proof.json")
    sheet.text(3, 97, "Nuclear separation and a remaining faint merge",
               size=16, weight="bold", va="top")
    sheet.text(3, 89, "A  Two interiors become separate detections", size=13, weight="bold")
    CroppedComparison.read(sheet, NUCLEAR_SOURCE).draw_row((2, 54, 96, 28), 84)
    sheet.text(3, 48, "B  The faint pair remains merged", size=13, weight="bold")
    CroppedComparison.read(sheet, NUCLEAR_SOURCE, view_index=1).draw_final_row(
        (2, 12, 96, 28), 42)
    sheet.text(3, 6, "The lower repaired detection retains diffuse bridge support.", size=12)
    sheet.text(3, 2, "Native pixel units; colours are not identities across attempts.", size=12)
    sheet.save()


def retina_matched_repair(*, input_root: Path = FigureSheet.default_input_root):
    """Same original RBPMS plane before and after a retained retinal repair."""
    from build_slas_neurite_views import BioFormatsComparison, RETINAL_SOURCE

    sheet = FigureSheet("retina_fresh16_repair", "", 5.4, input_root=input_root)
    sheet.source(ROOT / "figure-collection-20261004/R0010-FRESH16-INDEPENDENT-FIRST-REVIEW.rst")
    sheet.text(3, 97, "Retinal body outlines: local repair and remaining ambiguity",
               size=16, weight="bold", va="top")
    for row, title in enumerate((
        "Bright neighbouring bodies remain separate",
        "Border outlines smooth; possible split remains",
    )):
        y = 53 - row * 38
        sheet.text(3, y + 35, title, size=13, weight="bold")
        BioFormatsComparison.read(sheet, RETINAL_SOURCE, view_index=row).draw_row(
            (3, y, 94, 26), y + 28)
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
            dose_axis = sheet.plot_axes((left, .52, .36, .33))
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
            dose_axis.tick_params(axis="x", labelrotation=45)
            statistics, = (row for row in tables["assay_statistics"]["rows"]
                           if row["assay_block"] == block)
            control_axis = sheet.plot_axes((left, .13, .36, .21))
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
        sheet.text(3, 98, "Nuclear detection 2 and 3: the same 200 fields",
                   size=18, weight="bold", va="top")
        scatter = sheet.plot_axes((.09, .27, .35, .55))
        pooled = sheet.plot_axes((.61, .27, .35, .55))
        for empty, color, label in (
            (False, BLUE, "Annotated fields"),
            (True, ORANGE, "Annotation-empty fields (n=3)"),
        ):
            rows = [row for row in current.values()
                    if (row["reference_count"] == 0) == empty]
            scatter.scatter([previous[key(row)]["f1"] for row in rows],
                            [row["f1"] for row in rows],
                            s=24, alpha=.75, color=color, label=label, zorder=3)
        scatter.plot((0, 1), (0, 1), "--", color=MUTED, linewidth=1)
        scatter.set(title="A  Paired field scores", xlabel="Nuclear detection 2: F1",
                    ylabel="Nuclear detection 3: F1", xlim=(-.03, 1.03), ylim=(-.03, 1.03))
        scatter.set_aspect("equal", adjustable="box")
        for offset, record, color, label in (
            (-.18, earlier, BLUE, "Analysis 2"),
            (.18, repeat, TEAL, "Analysis 3"),
        ):
            values = [record["summary"][name]
                      for name in ("precision", "recall", "micro_f1")]
            bars = pooled.bar([index + offset for index in range(3)], values,
                              width=.34, color=color, label=label)
            pooled.bar_label(bars, labels=[f"{value:.3f}" for value in values],
                             label_type="center", fontsize=sheet.plot_font_size, rotation=90, color="white")
        pooled.set(title="B  Pooled detection scores", ylabel="Score (1 is best)",
                   xticks=(0, 1, 2), xticklabels=("Precision", "Recall", "F1"),
                   ylim=(0, 1.12), yticks=(0, .2, .4, .6, .8, 1))
        pooled.legend(frameon=False, fontsize=sheet.plot_font_size, loc="upper center",
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


def submission_neurite_results(*, input_root: Path = FigureSheet.default_input_root):
    """Keep the principal drug-response results and separate laboratory tracing."""
    from build_slas_neurite_effects import NeuriteEffectFigure
    from build_slas_neurite_views import AcquisitionNeuriteView

    sheet = FigureSheet("submission_neurite_results", "", 7.1, input_root=input_root)
    sheet.source(OUTPUT / "p001_fresh13_sources/source-record.rst")
    sheet.source(ROOT / "figure-collection-20261004/P001-FRESH13-NINE-FIELD-REVIEW.rst")
    views_path = OUTPUT / "frozen_neurite_views.json"
    sheet.source(views_path)
    laboratory_view = AcquisitionNeuriteView(sheet, json.loads(views_path.read_text())["laboratory"])
    NeuriteEffectFigure.draw_panels(
        sheet, NeuriteEffectFigure.cohort_tables(
            sheet, ROOT / "paper/supplementary/personal_neurite_autonomous"),
        metrics=("mean_outgrowth",), bounds=(3, 48, 94, 49), start_letter="A",
    )
    laboratory_view.draw_columns((3, 1, 94, 36), 41, (
        ("C  Raw", laboratory_view.draw_raw),
        ("D  Labels and paths", laboratory_view.draw_result),
        ("E  Overlay", laboratory_view.draw_overlay),
    ))
    # Preserve the 1024-pixel field in the manuscript's raster embedding too.
    sheet.save(dpi=600)


def public_neurite_initial_comparison(*, input_root: Path = FigureSheet.default_input_root):
    """Retain the original public-field comparison in Supplementary Data 4."""
    from functools import partial
    from build_slas_neurite_views import FrozenNeuriteView

    sheet = FigureSheet("public_neurite_initial_comparison", "", 3.2, input_root=input_root)
    sheet.source(OUTPUT / "h004_fresh20_sources/QA-INDEX.json")
    sheet.source(ROOT / "paper/supplementary/task_only_analysis/h004-fresh20-qualified-completion.rst")
    views_path = OUTPUT / "frozen_neurite_views.json"
    sheet.source(views_path)
    public_view = FrozenNeuriteView(sheet, json.loads(views_path.read_text())["public"])
    published = OUTPUT / "neuroncyto_published_reference"
    reference_path = published / "source.json"
    reference = json.loads(reference_path.read_text())
    reference_image = published / reference["source_file"]
    if digest(reference_image) != reference["sha256"]:
        raise ValueError("Published NeuronCyto II figure source hash mismatch")
    sheet.source(reference_path)
    public_view.draw_columns((3, 1, 94, 85), 94, (
        ("A  Raw", public_view.draw_raw),
        ("B  Initial tracing", public_view.draw_result),
        ("C  NeuronCyto II", partial(sheet.source_image, reference_image,
                                     crop=tuple(reference["crop_xyxy_pixels"]))),
    ))
    sheet.save(dpi=600)



def submission_autonomous_loop():
    """Explain the guide's procedure; observed repairs belong to Figure 6."""
    sheet = FigureSheet("submission_autonomous_loop", "", 9.6)
    sheet.figure.set_size_inches(sheet.figure.get_size_inches() * .8)
    sheet.source(ROOT / "packaging/codex/openhcs/skills/use-openhcs/references/analysis-strategy.md")
    sheet.source(ROOT / "packaging/codex/openhcs/skills/use-openhcs/references/viewer-qa.md")

    # Use an existing licensed icon vocabulary; symbols are procedural, not
    # fabricated microscopy results. The observed trajectory stays separate.
    icons = ROOT / "paper/figures/assets/lucide"
    sheet.source(icons / "SOURCE.txt")
    sheet.source(icons / "LICENSE")
    sheet.text(3, 84, "Instructions guide the agent from question to analysis",
               size=12, weight="bold")
    stages = (
        (3, 63, "1  Biological brief", "clipboard-list",
         "Question\nMeasurements\nImage acquisition", BLUE),
        (36, 63, "2  Inspect inputs", "microscope",
         "Channels and scale\nBright/dim regions\nCentres / borders", BLUE),
        (69, 63, "3  Build and run", "workflow",
         "Choose methods\nSet parameters\nRun the analysis", BLUE),
        (69, 41, "4  Check the result", "scan-eye",
         "Raw and overlay\nMatched regions\nObjects and values", TEAL),
        (36, 41, "5  Repair and recheck", "wrench",
         "Find faulty step\nRevise and rerun\nInspect regions", ORANGE),
        (3, 41, "6  Finalize and deliver", "files",
         "Analysis settings\nImages and tables\nChecks and limits", TEAL),
    )
    for x, y, title, icon, detail, color in stages:
        sheet.axis.add_patch(FancyBboxPatch(
            (x, y), 28, 17, boxstyle="round,pad=0.2,rounding_size=0.65",
            facecolor=PALE, edgecolor=color, linewidth=1.2, zorder=2,
        ))
        sheet.text(x + 14, y + 14.5, title, size=11, weight="bold",
                   color=color, ha="center", va="center")
        if icon == "clipboard-list":
            sheet.asset(icons / "user-round.svg", (x+1, y+3, 6, 9))
            sheet.asset(icons / "circle-question-mark.svg", (x+7, y+8, 3, 4))
            sheet.asset(icons / "clipboard-list.svg", (x+7, y+1, 3, 5))
        elif icon == "microscope":
            sheet.source(ROOT / "website/assets/logos/README.md")
            sheet.asset(ROOT / "website/assets/logos/fiji.svg", (x+1, y+7, 9, 6))
            sheet.asset(ROOT / "website/assets/logos/napari.svg", (x+1, y+1, 9, 6))
        elif icon == "workflow":
            sheet.asset(icons / "list-tree.svg", (x+1.8, y+2, 8, 10))
        elif icon == "scan-eye":
            sheet.asset(icons / "clipboard-check.svg", (x+1.8, y+2, 8, 10))
        elif icon == "files":
            sheet.asset(icons / "circle-check-big.svg", (x+1.8, y+2, 8, 10))
        else:
            sheet.asset(icons / f"{icon}.svg", (x + 1.8, y + 2, 8, 10))
        sheet.text(x + 11, y + 7.5, detail, size=9, va="center",
                   linespacing=1.5, zorder=4)
    for start, end in (((31,71.5),(36,71.5)), ((64,71.5),(69,71.5)),
                       ((83,63),(83,58)), ((69,49.5),(64,49.5)),
                       ((36,49.5),(31,49.5))):
        sheet.arrow(start, end)
    sheet.route(((50,58),(50,60),(83,60),(83,63)), color=ORANGE, dashed=True)
    sheet.text(50, 61, "Run and inspect the revision", size=9, ha="center", color=ORANGE)
    sheet.text(50, 37, "The scientist checks images and measurements, and can edit the analysis",
               size=10.5, ha="center", weight="bold", color=TEAL)
    sheet.crop_vertical(.34, .875)
    sheet.save()


def submission_shared_workflow():
    """Show the full-width native application once, with region outlines."""
    folder = OUTPUT / "figure1_two_plate_native_20261007"
    evidence_path = folder / "capture_evidence.json"
    evidence = json.loads(evidence_path.read_text())
    capture = folder / Path(evidence["selected_png"]).name
    with Image.open(capture) as pixels:
        width_px, height_px = pixels.size
    _, _, logical_width, logical_height = evidence["logical_window_xywh"]
    sx, sy = width_px / logical_width, height_px / logical_height
    workspace_top = min(evidence["boxes_xywh"][region][1]
                        for region in ("plate_manager", "pipeline_editor"))
    crop = (0, round(workspace_top * sy), width_px, height_px)
    sheet = FigureSheet("submission_shared_workflow", "",
                        9 * (crop[3] - crop[1]) / width_px / .94)
    sheet.panel("A", "Select images, edit the analysis and follow its progress", 1, 97)
    sheet.source(evidence_path)
    sheet.native_image(str(capture.relative_to(OUTPUT).with_suffix("")),
                       (0, 0, 100, 94), response_path=(), crop=crop,
                       provenance_path=folder / evidence["selected_capture"])
    window = sheet.figure.axes[-1]
    # Derive native-pixel outlines from the recorded Qt logical rectangles.
    for region in ("plate_manager", "pipeline_editor", "zmq_servers"):
        x, y, width, height = evidence["boxes_xywh"][region]
        x, width, y, height = x * sx, width * sx, y * sy - crop[1], height * sy
        window.add_patch(Rectangle((x, y), width, height, fill=False,
                                   edgecolor=BLUE, linewidth=2))
        label = {"plate_manager": "Select a plate",
                 "pipeline_editor": "Edit analysis steps and settings",
                 "zmq_servers": "Check execution status"}[region]
        window.text(x + width - 12 if region == "zmq_servers" else x + 10,
                    y + height - 100, label, fontsize=11,
                    color=BLUE, weight="bold", va="bottom",
                    ha="right" if region == "zmq_servers" else "left",
                    bbox={"facecolor": "white", "edgecolor": BLUE, "pad": 3})
    sheet.save(dpi=600)



def architecture():
    """Use the process diagram layout with the retained integration marks."""
    from build_slas_processes import processes

    processes(stem="shared_workflow", with_logos=True)


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
