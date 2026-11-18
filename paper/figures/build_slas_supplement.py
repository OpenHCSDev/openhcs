"""Consolidate retained panels without rerunning or altering scientific results.

FigureSheet owns placement, crops and output receipts. Each reused artwork is
checked against its original output receipt; panel crops remove duplicated
headings and caption prose, never change contrast or segmentation pixels.
"""

from pathlib import Path
import json

from PIL import Image

from build_slas_visual_story import FigureSheet, OUTPUT, digest
from build_slas_neurite_views import BodySeparationView, VOLUME_REPAIR_SOURCE
from build_slas_neurite_effects import NeuriteEffectFigure
from compare_personal_neurite import endpoint_declarations


class SupplementFigure(FigureSheet):
    def __init__(self, stem, height=10, *, input_root=FigureSheet.default_input_root):
        super().__init__(stem, "", height, input_root=input_root)
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

    @classmethod
    def render_artwork(cls, stem, artwork, *, height=4.6):
        """A single retained chart needs no inherited multi-panel lettering."""
        sheet = cls(stem, height)
        sheet.artwork(artwork, (1, 1, 98, 93))
        sheet.save(dpi=400)


class VolumeResultsFigure(SupplementFigure):
    """Matched retinal and volume repairs, separate from final-only views."""

    def draw_panels(self):
        self.text(2, 45.5, "C  Retinal repair", size=14, weight="bold")
        for column, (heading, left) in enumerate((
            ("Raw", 3), ("First result", 34.96), ("Final result", 66.92),
        )):
            x = 2 + column * 32
            self.text(x, 42, heading, size=self.plot_font_size, weight="bold")
            self.artwork("retina_fresh16_repair", (x, 26, 30.7, 14.5),
                         crop=(left, 22.2, left + 30.08, 45.8))
        self.text(2, 23.5, "D  3D body separation", size=14, weight="bold")
        self.text(98, 23.5, "Z = 36 voxels", size=self.plot_font_size, ha="right")
        view = BodySeparationView.read(self, VOLUME_REPAIR_SOURCE)
        view.draw_columns((2, 1, 96, 17.5), 20, view.label_panels)


def infrastructure():
    sheet = SupplementFigure("supp_workflow_infrastructure", 10.3)
    sheet.heading("I  Array grouping, named results and scheduling", 99)
    sheet.artwork("runtime_composition", (2, 26, 96, 70), crop=(1, 6, 99, 100))
    sheet.heading("II  Prepared execution bundle", 24)
    sheet.artwork("compiler_preparation", (2, 2, 96, 19), crop=(2, 84, 98, 96))
    sheet.save()


def translocation():
    from build_slas_bbbc013_fresh23 import AssaySeries, EligibilityFraction, SOURCE

    sheet = SupplementFigure("supp_translocation", 7.4)
    sheet.heading("A–B  Protein translocation 2: cells with measurable cytoplasm", 99)
    EligibilityFraction().draw_series(sheet, AssaySeries.load(SOURCE),
                                     bottom=0.64, height=0.22, panel_y=92)
    sheet.heading("C–D  Protein translocation 1: held-out wells", 51.5)
    sheet.text(13, 45.5, "C  Wortmannin", size=12, weight="bold")
    sheet.text(61, 45.5, "D  LY294002", size=12, weight="bold")
    sheet.artwork("independent_agent_validation", (2, 1, 96, 44), crop=(0, 55, 100, 100))
    sheet.save()


def nuclear_instances():
    sheet = SupplementFigure("supp_nuclear_instances", 9)
    sheet.heading("Nuclear detection 2 and 3: the same 200 fields", 99)
    sheet.artwork("bbbc039_independent_repeat", (2, 59, 96, 36), crop=(0, 10, 100, 100))
    sheet.heading("Nuclear detection 1 and cell-boundary analysis 1: held-out fields", 58)
    sheet.text(13, 53, "C  Nuclear detections", size=12, weight="bold")
    sheet.text(60, 53, "D  Cell boundaries", size=12, weight="bold")
    sheet.artwork("independent_agent_validation", (2, 16, 96, 36), crop=(0, 7, 100, 52))
    sheet.text(18, 14.5, "E  3D localization: partial-reference diagnostic",
               size=13, weight="bold", va="top")
    localisation_diagnostic(sheet, bounds=(.16, .06, .72, .065))
    sheet.save()


def morphology_checks(*, input_root=FigureSheet.default_input_root):
    """Reflow the verified original fields without selecting or rendering new views."""
    sheet = SupplementFigure("supp_morphology_checks", 6.4, input_root=input_root)
    layout_path = OUTPUT / "retained_morphology/layout.json"
    sheet.source(layout_path)
    layout = json.loads(layout_path.read_text())
    artwork = layout["source_artwork"]
    sheet.artwork(artwork, (0, 33, 100, 67), crop=layout["upper_band_percent"])
    sheet.text(2, 32, "G–I  DNA: a faint pair\nremains merged",
               size=12, weight="bold", va="top")
    sheet.text(52, 32, "J–L  Actin: a seed without\nsupported body growth",
               size=12, weight="bold", va="top")
    for column, field in enumerate(layout["lower_full_fields"]):
        x = 2 + column * 16
        sheet.text(x, 22.5, field["label"], size=12, weight="bold")
        sheet.artwork(artwork, (x, .5, 14.5, 22), crop=field["crop_percent"])
    sheet.save()


def final_volume_views(*, input_root=FigureSheet.default_input_root):
    """Retain the final-only localisation views beside supplementary checks."""
    sheet = SupplementFigure("supp_nuclear_localisation", 4.2, input_root=input_root)
    sheet.heading("M–O  Nuclear localization 1: final XY, XZ and YZ views", 98)
    sheet.artwork("h002_measurement_first", (1, 2, 98, 89),
                  crop=(1, 7.5, 99, 58))
    sheet.save()


def localisation_diagnostic(sheet, *, bounds=(0.17, 0.23, 0.73, 0.55)):
    """Draw the retained partial-reference curve on its receiving figure."""
    from build_slas_visual_story import MUTED, TEAL

    source = OUTPUT.parents[1] / "supplementary/task_only_analysis/h002-fresh15-postfreeze-evaluation.json"
    sheet.source(source)
    evaluation = json.loads(source.read_text())
    scores = evaluation["scores"]
    thresholds = sorted(map(int, scores))
    errors = [scores[str(threshold)]["mean_localisation_error_voxels"] for threshold in thresholds]
    axis = sheet.plot_axes(bounds)
    axis.plot(thresholds, errors, "o-", color=TEAL)
    for threshold, error in zip(thresholds, errors, strict=True):
        axis.annotate(f"{scores[str(threshold)]['true_positives']} matches", (threshold, error),
                      xytext=(10, -10), textcoords="offset points", ha="center", va="top",
                      fontsize=sheet.plot_font_size)
    axis.axvline(evaluation["primary_threshold_voxels"], color=MUTED, linestyle="--", linewidth=0.8)
    axis.set(xlabel="Matching distance (voxels)", ylabel="Mean centre\nerror\n(voxels)",
             ylim=(0, 6.1), xticks=thresholds)
    axis.spines[["top", "right"]].set_visible(False)
    axis.grid(axis="y", color="#e7ebef", linewidth=0.6)
    axis.set_axisbelow(True)


def autonomous_treatment_endpoints():
    """Put every additional endpoint and both correlation maps on one canvas."""
    autonomous = SupplementFigure("supp_neurite_autonomous_endpoints", 10)
    autonomous.figure.set_size_inches(10, 10)
    autonomous.plot_font_size = 12
    autonomous.heading("Fixed-code re-evaluation of three frozen blind analyses", 99)
    tables = NeuriteEffectFigure.cohort_tables(autonomous)
    metrics = tuple(metric for metric in endpoint_declarations()
                    if metric not in NeuriteEffectFigure.primary_metrics)
    NeuriteEffectFigure.draw_panels(
        autonomous, tables, metrics=metrics, bounds=(0, 28, 100, 72),
        metric_columns=2, label_width=15,
        legend_offset=(.25, -.725), legend_rows=2,
    )
    autonomous.panel("O–P", "Correlations with MetaXpress", 3, 28)
    counts = NeuriteEffectFigure.draw_correlations(
        autonomous, tables, bounds=(.36, .015, .54, .195),
        heading_y=28, font_size=13, label_rotation=0, label_alignment="center",
        column_label_width=8,
    )
    if len(counts) != 1:
        raise ValueError("Correlations require the same matched wells for all analyses")
    autonomous.save(dpi=400)


def treatment_endpoints():
    """Render the cohort pages and the separately retained assisted comparison."""

    autonomous_treatment_endpoints()
    sheet = SupplementFigure("supp_neurite_treatment_endpoints", 10.4)
    sheet.heading("Additional morphology responses after assisted repair", 99)
    NeuriteEffectFigure.draw_panels(
        sheet, OUTPUT.parents[1] / "supplementary/personal_neurite_repaired_morphometry",
        metrics=("cell_count", "total_outgrowth", "branches_per_cell",
                 "mean_process_length", "median_process_length"),
        start_letter="Q",
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
    """Rebuild retained publication charts without repeating the plotting code."""
    from build_slas_benchmark_reference import submission_benchmark_schedule
    SupplementFigure.render_artwork(
        "submission_benchmark_speed",
        "benchmark-publication/measured_benchmark_publication_log",
    )
    submission_benchmark_schedule()
    SupplementFigure.render_artwork(
        "submission_benchmark_coverage",
        "benchmark-publication/reference-layout/reference_module_coverage",
    )
    SupplementFigure.render_artwork(
        "supp_benchmark_assignments",
        "benchmark-publication/reference-layout/reference_assignments_summary_log",
        height=3.3,
    )



if __name__ == "__main__":
    infrastructure()
    translocation()
    nuclear_instances()
    morphology_checks()
    final_volume_views()
    diagnostic = SupplementFigure("supp_localisation_diagnostic", 3.3)
    diagnostic.heading("M  Nuclear localization: a partial-reference diagnostic", 98)
    localisation_diagnostic(diagnostic)
    diagnostic.save(dpi=400)
    treatment_endpoints()
    scaling()
