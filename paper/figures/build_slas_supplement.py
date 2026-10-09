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
    sheet.heading("I  Array grouping, named results and scheduling", 99)
    sheet.artwork("runtime_composition", (2, 26, 96, 70), crop=(1, 6, 99, 100))
    sheet.heading("II  Prepared execution bundle", 24)
    sheet.artwork("compiler_preparation", (2, 2, 96, 19), crop=(2, 84, 98, 96))
    sheet.save()


def translocation():
    sheet = SupplementFigure("supp_translocation", 7.4)
    sheet.heading("A–B  Full-plate eligible-cell fractions", 99)
    sheet.text(13, 92, "A  LY294002", size=12, weight="bold")
    sheet.text(61, 92, "B  Wortmannin", size=12, weight="bold")
    sheet.artwork("translocation_fresh23", (2, 53, 96, 36), crop=(1, 59, 99, 88))
    sheet.heading("C–D  Independent prospective held-out endpoints", 51.5)
    sheet.text(13, 45.5, "C  Wortmannin", size=12, weight="bold")
    sheet.text(61, 45.5, "D  LY294002", size=12, weight="bold")
    sheet.artwork("independent_agent_validation", (2, 1, 96, 44), crop=(0, 55, 100, 100))
    sheet.save()


def nuclear_instances():
    sheet = SupplementFigure("supp_nuclear_instances", 7.4)
    sheet.heading("I  Independent BBBC039 authors: the same 200 fields", 99)
    sheet.artwork("bbbc039_independent_repeat", (2, 51, 96, 45), crop=(0, 10, 100, 92))
    sheet.heading("II  Prospective held-out nuclei and cell-boundary assays", 49)
    sheet.artwork("independent_agent_validation", (2, 1, 96, 44), crop=(0, 3, 100, 52))
    sheet.save()


def morphology_checks():
    """Independent checks and residual failures, not repeated main overviews."""
    sheet = SupplementFigure("supp_morphology_checks", 8.4)
    sheet.heading("A–C  Separate volume author: centres in XY, XZ and YZ", 99)
    for column, crop in enumerate(((52, 10, 98, 42), (52, 47, 98, 70), (52, 75, 98, 99))):
        sheet.artwork("h002_fresh10_native", (2 + column*32, 76, 31, 20), crop=crop)
    sheet.heading("D–F  Retinal acquisition border: raw, first and final", 74)
    sheet.artwork("retina_fresh16_repair", (2, 52, 96, 19), crop=(1, 62, 99, 85))
    sheet.heading("G–I  DNA: a faint pair remains merged", 50)
    sheet.artwork("h003_native_repair", (2, 26, 96, 21), crop=(1, 50, 99, 85))
    sheet.heading("J–L  Actin: a seed without supported body growth", 24)
    sheet.artwork("h003_fresh19_matched", (2, 1, 96, 20), crop=(1, 70, 99, 89))
    sheet.save()


def treatment_endpoints():
    """Additional endpoints from the existing well tables, not new analysis."""
    from build_slas_neurite_effects import NeuriteEffectFigure

    for stem, metrics in (
        ("supp_neurite_autonomous_endpoints", ("cell_count", "total_outgrowth",
                                             "branches_per_cell", "mean_process_length")),
        ("supp_neurite_autonomous_endpoints_continued", ("median_process_length", "total_branches",
                                                       "total_processes", "branches_per_process")),
    ):
        autonomous = SupplementFigure(stem, 10.4)
        autonomous.heading("Additional responses from three independent blind authors", 99)
        NeuriteEffectFigure.draw_panels(
            autonomous, NeuriteEffectFigure.cohort_tables(
                autonomous, OUTPUT.parents[1] / "supplementary/personal_neurite_autonomous"),
            metrics=metrics,
        )
        autonomous.text(3, 6, "Dots: two technical wells per author/method; whiskers: between-well SD.", size=10)
        autonomous.text(3, 3, "Curve-specific DMSO normalization; algorithm comparison, not manual tracing truth.", size=10)
        autonomous.save()

    sheet = SupplementFigure("supp_neurite_treatment_endpoints", 11.4)
    sheet.heading("Additional morphology responses after assisted repair", 99)
    NeuriteEffectFigure.draw_panels(
        sheet, OUTPUT.parents[1] / "supplementary/personal_neurite_repaired_morphometry",
        metrics=("cell_count", "total_outgrowth", "branches_per_cell",
                 "mean_process_length", "median_process_length"),
    )
    sheet.text(3, 6, "Dots: two technical wells. Whiskers: between-well SD, not confidence intervals.", size=10)
    sheet.text(3, 3, "Each drug curve uses its own zero-dose DMSO mean; neither method is ground truth.", size=10)
    sheet.save()


def scaling():
    sheet = SupplementFigure("supp_worker_comparisons", 10.3)
    # Keep each original clock, axis and revision label; do not pool captures.
    sheet.artwork("supp_matched_worker_speedups", (1, 66, 98, 33), crop=(0, 2, 100, 48))
    sheet.artwork("supp_matched_worker_speedups", (1, 33, 98, 33), crop=(0, 52, 100, 98))
    sheet.artwork("supp_matched_worker_speedups_continued_2", (1, 0, 98, 33), crop=(0, 3, 100, 97))
    sheet.save()


def benchmark_publication():
    """Keep worker speedups and coverage in main; assignment detail in supplement."""
    pages = (
        ("submission_benchmark_schedule", (
            ("A", "reference_core_summary_log"),
        )),
        ("supp_benchmark_assignments", (
            ("", "reference_assignments_summary_log"),
        )),
        ("submission_benchmark_coverage", (
            ("B", "reference_module_coverage"),
        )),
    )
    for stem, panels in pages:
        height_inches = 3.3 if stem == "supp_benchmark_assignments" else 4.6
        sheet = SupplementFigure(stem, height_inches)
        for letter, artwork in panels:
            y, height = 1, 93
            if letter:
                sheet.text(1, y + height + 2, letter, size=14, weight="bold", va="top")
            sheet.artwork(f"benchmark-publication/reference-layout/{artwork}", (1, y, 98, height))
        sheet.save(dpi=400)



if __name__ == "__main__":
    infrastructure()
    translocation()
    nuclear_instances()
    morphology_checks()
    treatment_endpoints()
    scaling()
