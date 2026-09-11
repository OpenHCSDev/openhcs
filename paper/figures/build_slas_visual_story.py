"""Original manuscript diagrams and panels assembled from retained UI captures.

Editorial layout is explicit here. Capture identities and file hashes are read
from the published gallery authority; no UI state or scientific image is invented.
"""

from __future__ import annotations

import json
from io import BytesIO
from pathlib import Path
import subprocess

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch, Rectangle
from PIL import Image

from build_slas_agent import ROOT, OUTPUT, digest


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
        self.axis.add_patch(FancyBboxPatch(
            (x, y), width, height, boxstyle="round,pad=0.2,rounding_size=0.65",
            linewidth=1.15, edgecolor=color, facecolor="white", zorder=2,
        ))
        self.text(x + width / 2, y + height * (0.65 if detail else 0.5), title,
                  size=11, weight="bold", ha="center", va="center", color=color)
        if detail:
            self.text(x + width / 2, y + height * 0.28, detail,
                      size=9, ha="center", va="center")

    def arrow(self, start, end, *, color=MUTED, both=False, dashed=False):
        self.axis.add_patch(FancyArrowPatch(
            start, end, arrowstyle="<->" if both else "-|>", mutation_scale=13,
            linewidth=1.4, color=color, linestyle="--" if dashed else "-",
            shrinkA=1.5, shrinkB=1.5, zorder=1,
        ))

    def route(self, points, *, color=MUTED, dashed=False):
        self.axis.plot(*zip(*points[:-1]), color=color, linewidth=1.4,
                       linestyle="--" if dashed else "-", zorder=1)
        self.arrow(points[-2], points[-1], color=color, dashed=dashed)

    def source(self, path):
        self.sources[str(path.relative_to(ROOT))] = digest(path)

    def asset(self, path, bounds):
        """Place an existing mark without altering its colors or aspect ratio."""
        self.source(path)
        if path.suffix == ".svg":
            raw = subprocess.run(
                ["rsvg-convert", "--width", "600", str(path)],
                check=True, capture_output=True,
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
            self.axis.add_patch(Rectangle(
                (x + offset, y + offset), width, height,
                edgecolor=BLUE, facecolor="#e7f1fa", linewidth=1.2,
            ))
        for dx, dy in ((0.25, 0.3), (0.65, 0.65), (0.72, 0.2)):
            self.axis.add_patch(Circle((x + width * dx, y + height * dy),
                                      width * 0.08, color=TEAL))

    def chip(self, x, y, label):
        self.axis.add_patch(Rectangle((x, y), 12, 8, edgecolor=ORANGE,
                                      facecolor="#fff7ed", linewidth=1.5))
        for dx in (2, 4, 6, 8, 10):
            self.axis.plot([x + dx, x + dx], [y - 1, y], color=ORANGE)
            self.axis.plot([x + dx, x + dx], [y + 8, y + 9], color=ORANGE)
        self.text(x + 6, y + 4, label, ha="center", va="center", weight="bold", color=ORANGE)

    def gallery_image(self, name, bounds, *, crop=None):
        record_path = GALLERY / "release-media-record.json"
        record = json.loads(record_path.read_text())
        entries = [item for capture in record["captures"]
                   for item in capture["published"] if item["path"] == name]
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
        record = json.loads(record_path.read_text())["response"]["results"][0]["payloads"][0]
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
            if not (0 <= left < right <= pixels.width and 0 <= top < bottom <= pixels.height):
                raise ValueError(f"Invalid crop for {path.name}: {crop}")
            self.crops.append({"source": str(path.relative_to(ROOT)), "xyxy_pixels": list(crop),
                               "source_size": list(pixels.size)})
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
            outputs.append(path)
        plt.close(self.figure)
        receipt = {
            "generator_sha256": digest(Path(__file__)),
            "source_sha256": self.sources,
            "ui_crops": self.crops,
            "output_sha256": {p.name: digest(p) for p in outputs},
            "interpretation": "Original explanatory layout; retained captures are not new scientific evaluations",
        }
        (OUTPUT / f"{self.stem}_provenance.json").write_text(json.dumps(receipt, indent=2) + "\n")
        print(f"Rendered {self.stem}")


def architecture():
    sheet = FigureSheet("shared_workflow", "OpenHCS: one editable workflow from images to results", 8.1)
    for source in ("docs/source/architecture/quick_start.rst",
                   "openhcs/core/pipeline_document.py", "openhcs/core/compiled_step_plan.py",
                   "openhcs/core/runtime_stores.py", "openhcs/core/source_bindings.py",
                   "openhcs/agent/capabilities.py"):
        sheet.source(ROOT / source)

    logos = ROOT / "website/assets/logos"
    sheet.source(logos / "README.md")
    sheet.panel("A", "Choose how to work", 3, 89)
    # Original desktop pictogram; upstream product marks remain unmodified.
    sheet.axis.add_patch(Rectangle((8, 77), 14, 8, edgecolor=PURPLE, facecolor=PALE, linewidth=1.5))
    for y in (79, 81, 83):
        sheet.axis.plot([10, 13, 13, 20], [y, y, y, y], color=PURPLE, linewidth=1.5)
        sheet.axis.add_patch(Circle((15, y), 0.5, color=PURPLE))
    sheet.axis.plot([11, 19], [75.5, 75.5], color=PURPLE, linewidth=2)
    sheet.asset(logos / "python.svg", (34, 77, 10, 9))
    sheet.axis.add_patch(FancyBboxPatch((57, 77), 12, 8, boxstyle="round,pad=0.2", facecolor=PALE, edgecolor=PURPLE))
    sheet.text(63, 81, "MCP", ha="center", va="center", weight="bold", color=PURPLE)
    sheet.axis.plot([59, 58, 62], [77, 75.5, 77], color=PURPLE)
    sheet.asset(logos / "cellprofiler.png", (82, 77, 10, 9))
    for x, label in ((15, "Desktop forms"), (39, "Python code"), (63, "Agent conversation"), (87, "CellProfiler import")):
        sheet.text(x, 73.5, label, size=10.5, ha="center", weight="bold")
        sheet.arrow((x, 71.5), (x, 67.5), both=x != 87, color=PURPLE)

    sheet.axis.add_patch(FancyBboxPatch((4, 39), 92, 28, boxstyle="round,pad=0.4", facecolor="#edf7f5", edgecolor=TEAL))
    sheet.text(50, 63.5, "SHARED PIPELINE  •  configuration + ordered function steps", size=12, ha="center", weight="bold", color=TEAL)
    sheet.stack(7, 48)
    for x, title in ((24, "Prepare"), (48, "Segment"), (72, "Measure")):
        sheet.box(x, 49, 19, 9, title, "Python function", color=TEAL)
    for start, end in ((19, 24), (43, 48), (67, 72)):
        sheet.arrow((start, 53.5), (end, 53.5), color=TEAL)
    sheet.text(12, 44, "Bind images", size=9.5, ha="center")
    sheet.text(59, 43, "Choose stack axes, processing groups, function chains and named results", size=9.3, ha="center")

    sheet.panel("B", "Connect data and processing tools", 3, 34)
    sheet.asset(logos / "bioformats.svg", (6, 24, 9, 7))
    sheet.text(18, 28.5, "Image folders · Bio-Formats", size=10.5, va="center")
    sheet.text(18, 24, "OME-Zarr · OMERO (experimental)", size=9.5, va="center", color=MUTED)
    for name, x in (("cupy.svg", 58), ("pytorch.svg", 70), ("jax.png", 82)):
        sheet.asset(logos / name, (x, 24, 8, 7))
    sheet.text(74, 21, "Scientific Python + custom functions", size=10, ha="center")
    sheet.route(((8, 31), (1.5, 31), (1.5, 53), (6, 53)), color=BLUE)
    sheet.route(((93, 28), (98.5, 28), (98.5, 53), (92, 53)), color=ORANGE)

    sheet.panel("C", "Compile, execute and inspect", 3, 17)
    sheet.route(((50, 39), (50, 36.5), (0.7, 36.5), (0.7, 9), (4, 9)), color=TEAL)
    sheet.text(11, 9, "Compile", size=12, weight="bold", ha="center", color=BLUE)
    sheet.text(11, 5.5, "validate + plan", size=9, ha="center")
    sheet.arrow((20, 9), (26, 9))
    sheet.chip(28, 5, "CPU")
    sheet.chip(45, 5, "GPU")
    sheet.text(42.5, 2.3, "Persistent workers", size=10, ha="center")
    sheet.arrow((59, 9), (65, 9), color=TEAL)
    sheet.stack(67, 6, 6, 5)
    sheet.axis.add_patch(Rectangle((77, 6), 7, 6, edgecolor=TEAL, facecolor="white"))
    for y in (7.5, 9, 10.5):
        sheet.axis.plot([77, 84], [y, y], color=TEAL, linewidth=0.7)
    sheet.axis.plot([79.5, 79.5], [6, 12], color=TEAL, linewidth=0.7)
    sheet.asset(logos / "fiji.svg", (88, 6, 7, 6))
    sheet.text(81, 2.3, "Images · ROIs · tables", size=10, ha="center")
    sheet.text(81, 14, "napari / Fiji + saved outputs", size=9, ha="center", color=TEAL)
    sheet.save()


def authoring():
    sheet = FigureSheet("editable_analyses", "Edit one analysis through forms, Python or MCP", 8.2)
    record_path = OUTPUT / "authoring_verified_roundtrip_provenance.json"
    record = json.loads(record_path.read_text())
    if not record["verified"]:
        raise ValueError("Authoring round trip has not passed native validation")
    sheet.source(record_path)
    field_edits = [event["arguments"] for event in record["events"]
                   if event["tool"] == "openhcs_ui_mutate_object_state_field"]
    if len(field_edits) != 1:
        raise ValueError("Expected one recorded field restoration")
    field_edit = field_edits[0]
    field_label = field_edit["field_path"].replace("_", " ").title() + ":"
    observed = [widget["label"] for event in record["events"]
                if event["tool"] == "openhcs_ui_get_widget_tree"
                for widget in event["response"]["results"][0]["payloads"][0]["actionable_widgets"]
                if widget["class_name"] == "NoScrollDoubleSpinBox"
                and widget["context_label"].endswith(field_label)]
    if not observed or observed[-1] != str(field_edit["value"]):
        raise ValueError("Recorded final field and control do not agree")

    sheet.panel("A", "Main window: the complete workflow", 3, 90)
    sheet.native_image("authoring_main_verified_capture", (3, 40, 60, 48))
    sheet.panel("B", "Recorded MCP edits", 66, 90)
    sheet.box(67, 73, 29, 12, "Apply Python code", f"Control updates to {observed[0]}", color=PURPLE)
    sheet.arrow((81.5, 72), (81.5, 67), color=PURPLE)
    sheet.box(67, 54, 29, 12, "Edit the same field", f"Code returns to {field_edit['value']}", color=TEAL)
    sheet.text(81.5, 47, "Read and edit the same\nlive session through MCP", size=10,
               ha="center", va="center", color=MUTED, linespacing=1.5)
    sheet.text(3, 37, "NeuronCyto II workflow • two function steps", size=10, color=MUTED)
    sheet.panel("C", "Function controls", 3, 33)
    sheet.panel("D", "Matching Python code", 54, 33)
    sheet.native_image("authoring_function_verified_capture", (3, 8, 44, 23),
                       crop=(15, 86, 535, 304))
    sheet.native_image("authoring_code_verified_capture", (54, 8, 43, 23),
                       crop=(65, 96, 410, 224))
    sheet.arrow((48, 19), (53, 19), both=True, color=PURPLE)
    sheet.text(50, 5, "The same parameters, in the same order, with the same values", size=11,
               ha="center", color=TEAL, weight="bold")
    sheet.save()


def viewers():
    sheet = FigureSheet("inspectable_results", "Inspect images and objects in familiar viewers", 9.1)
    sheet.panel("A", "Fiji: an image plane and its matching ROI list", 3, 90)
    sheet.gallery_image("fiji-review.webp", (3, 53, 94, 34))
    sheet.text(50, 50, "NeuronCyto II field 1 • recorded Fiji streaming demonstration", size=10, ha="center", color=MUTED)
    sheet.panel("B", "napari: object selection and image coordinates", 3, 44)
    sheet.gallery_image("napari-roi-navigation-poster.webp", (3, 7, 94, 34))
    sheet.text(50, 4, "Separate three-plane navigation demonstration • selected object and ROI-list entry", size=10, ha="center", color=MUTED)
    sheet.save()


if __name__ == "__main__":
    plt.rcParams.update({"font.family": "DejaVu Sans", "svg.fonttype": "none", "pdf.fonttype": 42})
    architecture()
    authoring()
    viewers()
