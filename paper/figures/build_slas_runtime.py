"""Source-backed explanatory runtime figure, not an experimental result."""

import json
from pathlib import Path

from build_slas_visual_story import (
    BLUE, MUTED, ORANGE, PURPLE, TEAL, FigureSheet, ROOT, OUTPUT, digest,
)


def runtime():
    sheet = FigureSheet("runtime_composition", "Compose functions, array views and data routes", 9.3)
    for source in (
        "openhcs/core/config.py",
        "openhcs/core/callable_contract.py",
        "openhcs/core/runtime_stores.py",
        "openhcs/core/artifacts.py",
        "docs/source/concepts/function_patterns.rst",
        "docs/source/architecture/processing_semantics.rst",
        "docs/source/architecture/artifact_contract_system.rst",
    ):
        sheet.source(ROOT / source)

    sheet.panel("A", "Choose array axes and processing groups", 3, 91)
    sheet.text(5, 87, "Example acquisition: wells × time × channels × Z × Y × X", size=10)
    sheet.stack(6, 77, 9, 6)
    sheet.text(12, 74, "Source images", size=10, ha="center")
    sheet.arrow((20, 80), (28, 80), color=BLUE)
    sheet.stack(31, 81, 7, 3)
    sheet.stack(31, 73, 7, 3)
    sheet.text(43, 83, "Channel 1: Z stack", size=10, va="center")
    sheet.text(43, 75, "Channel 2: Z stack", size=10, va="center")
    sheet.text(5, 69, "variable_components = [Z_INDEX]", size=10, color=BLUE, family="monospace")
    sheet.text(5, 66, "Z varies within each array.", size=10, color=MUTED)
    sheet.text(55, 69, "group_by = CHANNEL", size=10, color=TEAL, family="monospace")
    sheet.text(55, 66, "Channel identity selects a group.", size=10, color=MUTED)
    sheet.text(73, 80, "Function behavior:\nper-plane, whole-stack\nor stack reduction", size=10, color=PURPLE,
               va="center", linespacing=1.5)

    sheet.panel("B", "Assign function chains to groups", 3, 61)
    for y, label, color in ((52, "Channel 1", BLUE), (44, "Channel 2", TEAL)):
        sheet.text(4, y + 3, label, size=10, weight="bold", color=color)
        sheet.arrow((19, y + 3), (24, y + 3), color=color)
    for x, y, title, color in (
        (24, 52, "Normalize", BLUE), (51, 52, "Segment", BLUE),
        (24, 44, "Denoise", TEAL), (51, 44, "Enhance", TEAL),
    ):
        sheet.box(x, y, 20, 5.5, title, "function + parameters", color=color)
    for y, color in ((54.75, BLUE), (46.75, TEAL)):
        sheet.arrow((44, y), (51, y), color=color)
        sheet.arrow((71, y), (78, y), color=color)
        sheet.text(87, y, "Next step", size=10, ha="center", va="center", color=color)
    sheet.text(5, 40, "Dictionary: a chain for each group     List: a shared chain     Function: one operation", size=9.5, color=MUTED)

    sheet.panel("C", "Carry named results alongside the image flow", 3, 35)
    for x, title, detail in ((7, "Segment", "step 1"), (39, "Normalize", "step 2"), (71, "Measure", "step 3")):
        sheet.box(x, 25, 20, 6, title, detail, color=TEAL)
    sheet.arrow((27, 28), (39, 28), color=TEAL)
    sheet.arrow((59, 28), (71, 28), color=TEAL)
    sheet.route(((17, 25), (17, 21), (81, 21), (81, 25)), color=PURPLE, dashed=True)
    sheet.text(49, 22, "Named labels → declared input", size=10, color=PURPLE, ha="center")
    sheet.text(5, 18, "Artifact routing is independent of saving images, labels or tables to disk.", size=10, color=MUTED)

    sheet.panel("D", "Run the pipeline across timepoints and wells", 3, 13)
    for y, label in ((7, "Well A"), (2, "Well B")):
        sheet.text(5, y + 1.5, label, size=10, weight="bold", color=ORANGE)
        sheet.box(19, y, 24, 3.7, "t₁: all steps", color=ORANGE)
        sheet.box(51, y, 24, 3.7, "t₂: all steps", color=ORANGE)
        sheet.arrow((43, y + 1.85), (51, y + 1.85), color=ORANGE)
    sheet.text(86, 7, "CPU / GPU\nworkers", size=11, weight="bold", ha="center", va="center", color=ORANGE)
    sheet.save()
    path = OUTPUT / "runtime_composition_provenance.json"
    receipt = json.loads(path.read_text())
    receipt["generator_sha256"] = digest(Path(__file__))
    receipt["source_sha256"]["paper/figures/build_slas_visual_story.py"] = digest(
        ROOT / "paper/figures/build_slas_visual_story.py"
    )
    receipt["interpretation"] = (
        "Illustrative configuration and callable roles, not an executed biological workflow. "
        "Panels B and C show separate composition examples: group-specific chains and "
        "an artifact routed between steps within a compatible execution group. Sequential "
        "timepoints run the entire pipeline; wells can execute in parallel and Z remains "
        "the variable component. Backend "
        "compatibility belongs to each callable contract."
    )
    path.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    runtime()
