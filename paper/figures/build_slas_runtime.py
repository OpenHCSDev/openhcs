"""Source-backed explanatory runtime figure, not an experimental result."""

import json
from pathlib import Path

from build_slas_visual_story import (
    BLUE,
    MUTED,
    ORANGE,
    PURPLE,
    TEAL,
    FigureSheet,
    ROOT,
    OUTPUT,
    digest,
)


def runtime():
    sheet = FigureSheet(
        "runtime_composition", "Compose functions, array views and data routes", 9.3
    )
    for source in (
        "openhcs/core/config.py",
        "openhcs/core/callable_contract.py",
        "openhcs/core/runtime_stores.py",
        "openhcs/core/artifacts/kinds.py",
        "openhcs/core/dataset_sources/source.py",
        "openhcs/formats/pattern/pattern_discovery.py",
        "openhcs/processing/backends/assemblers/assemble_stack_cpu.py",
        "docs/source/concepts/function_patterns.rst",
        "docs/source/architecture/processing_semantics.rst",
        "docs/source/architecture/artifact_contract_system.rst",
    ):
        sheet.source(ROOT / source)

    sheet.panel("A", "Collect images along a chosen stack axis", 3, 91)
    sheet.text(
        5, 87,
        "Stack axis: site, Z, channel or time; each image has Y × X pixels.",
        size=11,
    )
    sheet.stack(6, 77, 12, 5)
    sheet.text(13, 74.5, "Site × Y × X", size=11, ha="center", color=BLUE)
    sheet.arrow((23, 80.5), (33, 80.5), color=BLUE)
    sheet.box(33, 77, 24, 7, "Stitch", color=BLUE)
    sheet.text(45, 74.5, "+ tile positions", size=11, ha="center", color=BLUE)
    sheet.arrow((57, 80.5), (70, 80.5), color=BLUE)
    sheet.box(70, 77, 23, 7, "Mosaic", color=BLUE)
    sheet.text(
        5, 71.5, "For each stack, other acquisition coordinates stay fixed.",
        size=11, color=MUTED,
    )
    sheet.text(5, 66, "Choose Z instead:", size=11, va="center")
    sheet.arrow((26, 66), (34, 66), color=BLUE)
    sheet.stack(35, 64.5, 8, 3)
    sheet.text(49, 66, "Z × Y × X volume", size=11, va="center", color=BLUE)

    sheet.panel("B", "Assign function chains to groups", 3, 61)
    for y, label, color in ((52, "Channel 1", BLUE), (44, "Channel 2", TEAL)):
        sheet.text(4, y + 3, label, size=10, weight="bold", color=color)
        sheet.arrow((19, y + 3), (24, y + 3), color=color)
    for x, y, title, color in (
        (24, 52, "Normalize", BLUE),
        (51, 52, "Segment", BLUE),
        (24, 44, "Denoise", TEAL),
        (51, 44, "Enhance", TEAL),
    ):
        sheet.box(x, y, 20, 5.5, title, "function + parameters", color=color)
    for y, color in ((54.75, BLUE), (46.75, TEAL)):
        sheet.arrow((44, y), (51, y), color=color)
        sheet.arrow((71, y), (78, y), color=color)
        sheet.text(87, y, "Next step", size=10, ha="center", va="center", color=color)
    sheet.text(
        5,
        40,
        "Dictionary: a chain for each group     List: a shared chain     Function: one operation",
        size=9.5,
        color=MUTED,
    )

    sheet.panel("C", "Carry named results alongside the image flow", 3, 35)
    for x, title, detail in (
        (7, "Segment", "step 1"),
        (39, "Normalize", "step 2"),
        (71, "Measure", "step 3"),
    ):
        sheet.box(x, 25, 20, 6, title, detail, color=TEAL)
    sheet.arrow((27, 28), (39, 28), color=TEAL)
    sheet.arrow((59, 28), (71, 28), color=TEAL)
    sheet.route(((17, 25), (17, 21), (81, 21), (81, 25)), color=PURPLE, dashed=True)
    sheet.text(
        49, 22, "Named labels → declared input", size=10, color=PURPLE, ha="center"
    )
    sheet.text(
        5,
        18,
        "Artifact routing is independent of saving images, labels or tables to disk.",
        size=10,
        color=MUTED,
    )

    sheet.panel("D", "Run the pipeline across timepoints and wells", 3, 13)
    for y, label in ((7, "Well A"), (2, "Well B")):
        sheet.text(5, y + 1.5, label, size=10, weight="bold", color=ORANGE)
        sheet.box(19, y, 24, 3.7, "t₁: all steps", color=ORANGE)
        sheet.box(51, y, 24, 3.7, "t₂: all steps", color=ORANGE)
        sheet.arrow((43, y + 1.85), (51, y + 1.85), color=ORANGE)
    sheet.text(
        86,
        7,
        "CPU / GPU\nworkers",
        size=11,
        weight="bold",
        ha="center",
        va="center",
        color=ORANGE,
    )
    sheet.save()
    path = OUTPUT / "runtime_composition_provenance.json"
    receipt = json.loads(path.read_text())
    receipt["generator_sha256"] = digest(Path(__file__))
    receipt["source_sha256"]["paper/figures/build_slas_visual_story.py"] = digest(
        ROOT / "paper/figures/build_slas_visual_story.py"
    )
    receipt["interpretation"] = (
        "Illustrative configuration and callable roles, not an executed biological workflow. "
        "Panel A contrasts a site stack supplied with tile positions for stitching and "
        "a Z stack forming a volume. Other acquisition coordinates stay fixed within "
        "each stack; processing groups do not define its stack axis. Panels B and C "
        "show separate composition examples: group-specific chains and an artifact "
        "routed between steps within a compatible execution group. Sequential "
        "timepoints run the entire pipeline; wells can execute in parallel. Backend "
        "compatibility belongs to each callable contract."
    )
    path.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    runtime()
