"""Consolidate retained panels without rerunning or altering scientific results.

FigureSheet owns placement, crops and output receipts. Each reused artwork is
checked against its original output receipt; panel crops remove duplicated
headings and caption prose, never change contrast or segmentation pixels.
"""

from pathlib import Path
import json

from build_slas_visual_story import FigureSheet, MUTED, OUTPUT, TEAL, bbbc039_repeat
from build_slas_independent_validation import SCORE_PATHS, load_score, plot_cell_boundaries, plot_nuclear_instances, plot_translocation
from build_slas_neurite_views import BodySeparationView, VOLUME_REPAIR_SOURCE
from build_slas_neurite_effects import NeuriteEffectFigure
from compare_personal_neurite import endpoint_declarations
from build_slas_runtime import runtime


class SupplementFigure(FigureSheet):
    def __init__(self, stem, height=10, *, input_root=FigureSheet.default_input_root):
        super().__init__(stem, "", height, input_root=input_root)
        self.source(Path(__file__))

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
        self.panel('C', 'Retinal repair', 2, 45.5, title_size=14)
        for column, (heading, left) in enumerate((('Raw', 3), ('First result', 34.96), ('Final result', 66.92))):
            x = 2 + column * 32
            self.text(x, 42, heading, size=self.plot_font_size, weight='bold')
            self.artwork('retina_fresh16_repair', (x, 26, 30.7, 14.5), crop=(left, 22.2, left + 30.08, 45.8))
        self.panel('D', '3D body separation', 2, 23.5, title_size=14)
        self.text(98, 23.5, 'Z = 36 voxels', size=self.plot_font_size, ha='right')
        view = BodySeparationView.read(self, VOLUME_REPAIR_SOURCE)
        view.draw_columns((2, 1, 96, 17.5), 20, view.label_panels)


def infrastructure():
    sheet = SupplementFigure('supp_workflow_infrastructure', 10.3)
    sheet.panel('I', 'Array grouping, named results and scheduling', 3, 99, title_size=14, va='top')
    runtime_bounds = (2, 26, 96, 70)
    runtime_crop = (1, 6, 99, 100)
    composition = runtime()
    composition.fit_panel_letters_to(sheet, runtime_bounds, crop=runtime_crop)
    composition.save()
    sheet.artwork('runtime_composition', runtime_bounds, crop=runtime_crop)
    sheet.panel('II', 'Prepared execution bundle', 3, 24, title_size=14, va='top')
    sheet.artwork('compiler_preparation', (2, 2, 96, 19), crop=(2, 84, 98, 96))
    sheet.save()


def translocation():
    from build_slas_bbbc013_fresh23 import AssaySeries, EligibilityFraction, SOURCE

    sheet = SupplementFigure("supp_translocation", 7.4)
    sheet.panel("A–B", "Protein translocation 2: cells with measurable cytoplasm", 3, 99, title_size=14, va="top")
    EligibilityFraction().draw_series(sheet, AssaySeries.load(SOURCE), bottom=.64, height=.22, panel_y=92)
    sheet.panel("C–D", "Protein translocation 1: held-out wells", 3, 51.5, title_size=14, va="top")
    score = load_score(SCORE_PATHS[2], "BBBC013")
    sheet.source(SCORE_PATHS[2])
    sheet.source(Path(plot_translocation.__code__.co_filename))
    for column, (letter, treatment) in enumerate(zip(("C", "D"), score["metrics"]["treatments"], strict=True)):
        left = .105 + column * .49
        sheet.panel(letter, treatment["treatment"], left * 100, 45.5)
        axis = sheet.plot_axes((left, .08, .365, .30))
        plot_translocation(axis, treatment, "")
        axis.set_title("")
        axis.spines[["top", "right"]].set_visible(False)
        axis.grid(axis="y", color="#d9e0e5", linewidth=.6)
        axis.set_axisbelow(True)
    sheet.save()


def nuclear_instances():
    """Draw retained scores on equal-width axes, with summaries outside the data."""
    sheet = SupplementFigure("supp_nuclear_instances", 9.4)
    sheet.heading("Nuclear detection 2 and 3: the same 200 fields", 99)
    scatter = sheet.plot_axes((.09, .70, .35, .20))
    pooled = sheet.plot_axes((.61, .70, .35, .20))
    counts = bbbc039_repeat(sheet, scatter, pooled)
    scatter.set(xticks=(0, .25, .5, .75, 1), yticks=(0, .25, .5, .75, 1))
    sheet.panel("A", "Paired field scores", 9, 94)
    sheet.panel("B", "Pooled detection scores", 61, 94)
    sheet.text(50, 59.7,
               f"{counts['improved_vs612']} fields improved; "
               f"{counts['regressed_vs612']} lower; "
               f"{counts['unchanged_vs612']} unchanged",
               size=12, ha="center", color=MUTED)
    nuclei = sheet.plot_axes((.09, .32, .35, .17))
    boundaries = sheet.plot_axes((.61, .32, .35, .17))
    for path in SCORE_PATHS[:2]:
        sheet.source(path)
    sheet.source(Path(plot_nuclear_instances.__code__.co_filename))
    plot_nuclear_instances(nuclei, load_score(SCORE_PATHS[0], "BBBC039"),
                           summary_position=(0, 1.06), font_size=sheet.plot_font_size)
    plot_cell_boundaries(boundaries, load_score(SCORE_PATHS[1], "BBBC007"),
                         summary_position=(0, 1.06), font_size=sheet.plot_font_size)
    sheet.panel("C", "Held-out nuclear detection 1", 9, 57)
    sheet.panel("D", "Cell-boundary analysis 1", 61, 57)
    boundaries.tick_params(axis="x", labelsize=sheet.plot_font_size - 2)
    for axis in (nuclei, boundaries):
        axis.set_title("")
        axis.spines[["top", "right"]].set_visible(False)
        axis.grid(axis="y", color="#d9e0e5", linewidth=.6)
        axis.set_axisbelow(True)
    sheet.panel("E", "3D localization: partial-reference diagnostic", 16, 23)
    localisation_diagnostic(sheet, bounds=(.16, .065, .78, .15))
    sheet.save()


def morphology_checks(*, input_root=FigureSheet.default_input_root):
    """Keep all twelve original fields, separating their editable headings."""
    sheet = SupplementFigure("supp_morphology_checks", 6.4, input_root=input_root)
    layout_path = OUTPUT / "retained_morphology/layout.json"
    sheet.source(layout_path)
    layout = json.loads(layout_path.read_text())
    artwork = layout["source_artwork"]
    sheet.panel("A–C", "Independent volume analysis: centres in XY, XZ and YZ", 3, 99, va="top")
    for column, field in enumerate(layout["upper_full_fields"][:3]):
        sheet.artwork(artwork, (2 + column * 33, 68, 30, 27), crop=field["crop_percent"])
    sheet.panel("D–F", "Retinal acquisition border: raw, first and final", 3, 65, va="top")
    for column, field in enumerate(layout["upper_full_fields"][3:]):
        x = 2 + column * 33
        sheet.text(x, 60, field["label"], size=12, weight="bold")
        sheet.artwork(artwork, (x, 37, 30, 21), crop=field["crop_percent"])
    sheet.panel("G–I", "DNA: a faint pair\nremains merged", 2, 33, va="top")
    sheet.panel("J–L", "Actin: a seed without\nsupported body growth", 52, 33, va="top")
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
