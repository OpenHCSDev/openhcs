"""Consolidate retained panels without rerunning or altering scientific results.

FigureSheet owns placement, crops and output receipts. Each reused artwork is
checked against its original output receipt; panel crops remove duplicated
headings and caption prose, never change contrast or segmentation pixels.
"""

from pathlib import Path
import json

from PIL import Image

from build_slas_visual_story import FigureSheet, OUTPUT, digest


class SupplementFigure(FigureSheet):
    def __init__(self, stem, height=10):
        super().__init__(stem, "", height)
        self.source(Path(__file__))

    def artwork(self, stem, bounds, *, crop=None):
        path = OUTPUT / f"{stem}.png"
        receipt_path = OUTPUT / f"{stem}_provenance.json"
        # Benchmark receipts are shared by all outputs in their measured mode.
        if not receipt_path.exists():
            receipt_path = path.parent / "figure2_provenance.json"
        receipt = json.loads(receipt_path.read_text())
        expected = receipt["output_sha256"][path.name]
        if digest(path) != expected:
            raise ValueError(f"Retained artwork differs from its receipt: {path}")
        self.source(receipt_path)
        if crop is not None:
            with Image.open(path) as image:
                width, height = image.size
            crop = tuple(round(value * length / 100) for value, length in
                         zip(crop, (width, height, width, height)))
        self.source_image(path, bounds, crop=crop)

    def heading(self, text, y):
        self.text(3, y, text, size=14, weight="bold", va="top")


def infrastructure():
    sheet = SupplementFigure("supp_workflow_infrastructure", 10.3)
    sheet.heading("A  Array axes and processing groups", 99)
    sheet.artwork("runtime_composition", (2, 71, 96, 25), crop=(2, 10, 98, 34))
    sheet.heading("B  Preparation: inputs, storage and execution tasks", 69)
    sheet.artwork("compiler_preparation", (2, 53, 96, 13), crop=(2, 34, 98, 42))
    sheet.artwork("compiler_preparation", (2, 40, 96, 11), crop=(2, 84, 98, 96))
    sheet.heading("C  Typed function declaration", 38)
    sheet.artwork("custom_function_extension", (2, 21, 96, 14), crop=(2, 13, 98, 32))
    sheet.heading("D  The same parameters in the editor and MCP", 19)
    sheet.artwork("custom_function_extension", (2, 1, 96, 16), crop=(2, 68, 98, 94))
    sheet.save()


def translocation():
    sheet = SupplementFigure("supp_translocation", 10.4)
    sheet.heading("A–D  Final full-plate response and eligible-cell fraction", 99)
    sheet.artwork("translocation_fresh23", (2, 39, 96, 57), crop=(1, 12, 99, 88))
    sheet.heading("E–F  Independently authored prospective held-out wells", 37)
    sheet.text(13, 34, "E  Wortmannin", size=12, weight="bold")
    sheet.text(61, 34, "F  LY294002", size=12, weight="bold")
    sheet.artwork("independent_agent_validation", (2, 1, 96, 31), crop=(0, 55, 100, 100))
    sheet.save()


def nuclear_instances():
    sheet = SupplementFigure("supp_nuclear_instances", 10.3)
    sheet.heading("A–B  Independent BBBC039 authors: the same 200 fields", 99)
    sheet.artwork("bbbc039_independent_repeat", (2, 64, 96, 32), crop=(0, 10, 100, 92))
    sheet.heading("C–D  Prospective held-out nuclei and cell-boundary assays", 62)
    sheet.artwork("independent_agent_validation", (2, 32, 96, 27), crop=(0, 3, 100, 52))
    sheet.heading("E–G  H001 elongated-body repair: raw, first and final", 30)
    sheet.artwork("h001_scored_native", (2, 1, 96, 26), crop=(2, 65, 98, 92))
    sheet.save()


def volume():
    sheet = SupplementFigure("supp_volume", 10.3)
    sheet.heading("A–C  One frozen volume: XY, XZ and YZ outlines", 99)
    sheet.artwork("h002_measurement_first", (2, 58, 47, 38), crop=(3, 10, 50, 59))
    sheet.artwork("h002_measurement_first", (51, 78, 47, 18), crop=(55, 12, 97, 31))
    sheet.artwork("h002_measurement_first", (51, 58, 47, 18), crop=(55, 38, 97, 56))
    sheet.heading("D–G  Independent author: a continuous-body split repaired", 56)
    # Reflow the four image panels into one row, without their old titles.
    for column, crop in enumerate(((3, 18, 48, 47), (52, 18, 97, 47),
                                   (3, 58, 48, 87), (52, 58, 97, 87))):
        sheet.artwork("h002_fresh22_split_repair", (2 + column * 24, 35, 23, 18), crop=crop)
    sheet.heading("H–J  Separate author: body centres in XY, XZ and YZ", 33)
    for column, crop in enumerate(((52, 10, 98, 42), (52, 47, 98, 70), (52, 75, 98, 99))):
        sheet.artwork("h002_fresh10_native", (2 + column*32, 1, 31, 28), crop=crop)
    sheet.save()


def retina():
    sheet = SupplementFigure("supp_retina", 10.3)
    sheet.heading("A–B  Final whole-field retinal detections", 99)
    sheet.artwork("retinal_fresh_native", (2, 59, 96, 37), crop=(1, 6, 99, 39))
    sheet.heading("C–F  The same final result: neighbouring bodies and repair", 57)
    for column, crop in enumerate(((1, 46, 99, 68), (1, 76, 99, 99))):
        sheet.artwork("retinal_fresh_native", (2 + column * 48, 35, 47, 19), crop=crop)
    sheet.heading("G–I  Independent autonomous repair at neighbouring somata", 33)
    sheet.artwork("retina_fresh16_repair", (2, 17, 96, 13), crop=(1, 24, 99, 46))
    sheet.heading("J–L  Same author: acquisition-border review", 16)
    sheet.artwork("retina_fresh16_repair", (2, 0, 96, 13), crop=(1, 62, 99, 85))
    sheet.save()


def paired_channels():
    sheet = SupplementFigure("supp_paired_channels", 10.3)
    for heading, stem, crop, bounds, y in (
        ("A–C  Nuclear split repaired: raw, first and final", "h003_native_repair", (1, 8, 99, 42), (2, 70, 96, 26), 99),
        ("D–F  A remaining faint-pair merge: raw, labels and combined", "h003_native_repair", (1, 50, 99, 85), (2, 40, 96, 26), 69),
        ("G–I  Independent author: seeded actin bodies", "h003_fresh19_matched", (1, 43, 99, 62), (2, 20, 96, 16), 39),
        ("J–L  Negative witness: seed without supported body growth", "h003_fresh19_matched", (1, 70, 99, 89), (2, 0, 96, 16), 19),
    ):
        sheet.heading(heading, y)
        sheet.artwork(stem, bounds, crop=crop)
    sheet.save()


def neurite_morphology():
    sheet = SupplementFigure("supp_neurite_morphology", 10.3)
    sheet.heading("A–B  NeuronCyto II: raw image and main-shaft result", 99)
    sheet.artwork("h004_main_shafts", (2, 66, 96, 30), crop=(1, 18, 99, 90))
    sheet.heading("C–E  Laboratory mosaic: sampled tile overlap", 64)
    sheet.artwork("p001_stitched_dev13_native", (2, 38, 96, 23), crop=(1, 23, 99, 45))
    sheet.heading("F–H  Field core: raw, bodies/paths and combined", 36)
    sheet.artwork("p001_stitched_dev13_native", (2, 10, 96, 23), crop=(1, 63, 99, 84))
    sheet.text(3, 5, "Public shaft analysis and assisted laboratory mosaic are separate trials.", size=13)
    sheet.save()


def scaling():
    sheet = SupplementFigure("supp_matched_scaling", 10.3)
    for x, y, title, stem in (
        (2, 51, "A  Nine assignments: execution", "matched_latestmain_nine_20261006/primary-execution/measured_execution_seconds"),
        (51, 51, "B  Nine assignments: total", "matched_latestmain_nine_20261006/primary-total/measured_total_seconds"),
        (2, 3, "C  Sixteen 3D assignments: execution", "matched_lastconsumer_20261006/primary-execution/measured_execution_seconds"),
        (51, 3, "D  Sixteen 3D assignments: total", "matched_lastconsumer_20261006/primary-total/measured_total_seconds"),
    ):
        sheet.text(x, y + 45, title, size=12, weight="bold")
        sheet.artwork(stem, (x, y, 47, 43), crop=(0, 4, 71, 100))
    sheet.text(3, 1, "Black: stock CellProfiler, one process. Teal: OpenHCS, one worker. Orange: three / four workers.", size=10)
    sheet.save()


if __name__ == "__main__":
    infrastructure()
    translocation()
    nuclear_instances()
    volume()
    retina()
    paired_channels()
    neurite_morphology()
    scaling()
