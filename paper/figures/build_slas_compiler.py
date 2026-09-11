"""Render source-backed compiler preparation as an explanatory manuscript figure.

The five panels group responsibilities for readers; they are not a second
declaration of compiler passes. Symbol locations and source hashes accompany
the figure so that the explanation can be checked against its implementation.
"""

from __future__ import annotations

import ast
import json
from pathlib import Path

from matplotlib.patches import Circle, Rectangle

from build_slas_visual_story import (
    BLUE, INK, MUTED, ORANGE, PALE, PURPLE, TEAL,
    FigureSheet, OUTPUT, ROOT, digest,
)


CAPTION = (
    "Compiler preparation turns an authored image-analysis workflow into an "
    "execution plan. A, inherited settings and step parameters are resolved for "
    "the submitted pipeline. B, source metadata identifies image groups, and "
    "declared inputs link functions to images and named results from earlier "
    "steps. C, the compiler plans which results remain in memory or are saved, "
    "and separates contexts for ordered components such as time. D, function "
    "parameters, processing groups and array-backend requirements are checked "
    "before compatible devices are assigned. E, frozen contexts, prepared "
    "functions and worker assignments form the execution bundle. The schematic "
    "groups related compiler responsibilities rather than enumerating every "
    "internal pass. Image stacks and segmentation outputs are illustrative; "
    "analysis functions run during execution."
)


LABEL_SOURCES = {
    "A: Resolve the submitted workflow": {
        "openhcs/core/pipeline/compiler.py": (
            "PipelineCompiler._register_and_resolve_pipeline_once",
            "PipelineCompiler._capture_pipeline_config",
            "PipelineCompiler.compile_pipelines",
        ),
    },
    "B: Match images and connect step inputs": {
        "openhcs/core/pipeline/compiler.py": (
            "PipelineCompiler.initialize_step_plans_for_context",
            "PipelineCompiler._supplement_step_plans",
        ),
        "openhcs/core/pipeline/path_planner.py": (
            "PipelinePathPlanner.prepare_pipeline_paths",
        ),
    },
    "C: Plan storage and ordered processing": {
        "openhcs/core/pipeline/compiler.py": (
            "PipelineCompiler._compile_axis_value",
            "PipelineCompiler._compile_sequential_axis_contexts",
            "PipelineCompiler._compile_single_axis_context",
            "PipelineCompiler.declare_zarr_stores",
            "PipelineCompiler.plan_materialization_flags",
            "PipelineCompiler.analyze_pipeline_sequential_mode",
        ),
    },
    "D: Check requirements and assign devices": {
        "openhcs/core/pipeline/compiler.py": (
            "PipelineCompiler._run_post_plan_compile_stages",
            "PipelineCompiler.validate_memory_contracts",
            "PipelineCompiler.validate_source_workspace_projection",
        ),
        "openhcs/core/pipeline/framework_device_assignment.py": (
            "assign_framework_devices",
        ),
        "openhcs/core/pipeline/funcstep_contract_validator.py": (
            "FuncStepContractValidator.validate_pipeline",
        ),
    },
    "E: Prepare execution tasks": {
        "openhcs/core/pipeline/compiler.py": (
            "PipelineCompiler.compile_pipelines",
            "PipelineCompiler._calculate_worker_assignments",
        ),
        "openhcs/core/context/processing_context.py": (
            "ProcessingContext.freeze",
        ),
        "openhcs/core/compiled_execution.py": (
            "CompiledExecutionBundle",
        ),
    },
}


def symbol_locations(path: Path, symbols: tuple[str, ...]) -> dict[str, int]:
    """Require the cited nominal symbols to exist in the current source."""
    locations = {}

    def visit(body, prefix=""):
        for node in body:
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
                name = f"{prefix}{node.name}"
                locations[name] = node.lineno
                visit(node.body, f"{name}.")

    visit(ast.parse(path.read_text()).body)
    return {symbol: locations[symbol] for symbol in symbols}


def compiler():
    sheet = FigureSheet("compiler_preparation", "From an editable workflow to prepared execution", 9.0)
    source_mapping = {}
    for label, sources in LABEL_SOURCES.items():
        source_mapping[label] = {}
        for source, symbols in sources.items():
            path = ROOT / source
            sheet.source(path)
            source_mapping[label][source] = symbol_locations(path, symbols)

    rows = (
        ("A", "Resolve the submitted workflow", 87, BLUE),
        ("B", "Match images and connect step inputs", 70, TEAL),
        ("C", "Plan storage and ordered processing", 53, PURPLE),
        ("D", "Check requirements and assign devices", 36, ORANGE),
        ("E", "Prepare execution tasks", 19, BLUE),
    )
    for letter, title, y, color in rows:
        sheet.axis.add_patch(Rectangle((3, y - 12), 94, 16,
                                       facecolor=PALE, edgecolor="none", zorder=0))
        sheet.text(5, y + .3, letter, size=15, color=color, weight="bold")
        sheet.text(9, y + .3, title, size=14, color=INK, weight="bold")
        if letter != "E":
            sheet.arrow((50, y - 12), (50, y - 13), color=MUTED)

    # A: a visible change from inherited settings to concrete submitted values.
    sheet.text(7, 81, "Pipeline settings\n+ step parameters", size=12, va="center")
    sheet.arrow((34, 81), (43, 81), color=BLUE)
    sheet.text(47, 81, "Resolved settings for every step\nSelected wells and image locations", size=12, va="center")

    # B: image metadata and artifact declarations contribute different inputs.
    sheet.stack(7, 59.5, 7, 4)
    sheet.text(18, 62, "Channel + Z\nimage groups", size=11.5, va="center")
    sheet.arrow((39, 62), (44, 62), color=TEAL)
    sheet.box(45, 59, 19, 6, "Segment", color=TEAL)
    sheet.arrow((64, 62), (75, 62), color=PURPLE)
    sheet.text(69.5, 64.1, "labels", size=11, color=PURPLE, ha="center")
    sheet.box(76, 59, 18, 6, "Measure", color=TEAL)

    # C: persistence is a plan; the functions have not generated outputs yet.
    sheet.text(7, 47, "Results:\nkeep in memory / save", size=12, va="center", color=PURPLE)
    sheet.text(47, 47, "If time is sequential:", size=11.5, va="center")
    sheet.box(47, 41.8, 20, 3.8, "t₁: all steps", color=PURPLE)
    sheet.arrow((67, 43.7), (73, 43.7), color=PURPLE)
    sheet.box(73, 41.8, 20, 3.8, "t₂: all steps", color=PURPLE)

    # D: checks are named in ordinary workflow vocabulary, not class names.
    for x, label in ((7, "Parameters"), (29, "Image groups"), (53, "Array backends")):
        sheet.axis.add_patch(Circle((x, 29.5), .8, facecolor=ORANGE, edgecolor="none"))
        sheet.text(x + 2, 29.5, label, size=11.5, va="center")
    sheet.text(7, 25.3, "Declared requirements", size=11.5, color=MUTED)
    sheet.arrow((48, 26.1), (67, 26.1), color=ORANGE)
    sheet.text(72, 26.1, "CPU / GPU\nassignment", size=11.5, color=ORANGE, va="center")

    # E: the output is prepared execution state rather than transformed images.
    for x, title in ((7, "Frozen plans"), (38, "Prepared functions"), (72, "Worker map")):
        sheet.box(x, 9, 23, 6, title, color=BLUE)
    sheet.text(50, 5, "Execution bundle → run the analysis", size=13, weight="bold", color=BLUE, ha="center")
    sheet.save()

    path = OUTPUT / "compiler_preparation_provenance.json"
    receipt = json.loads(path.read_text())
    receipt.update(
        generator_sha256=digest(Path(__file__)),
        caption=CAPTION,
        label_source_symbols=source_mapping,
        interpretation=(
            "Original explanatory diagram, not an executed analysis or a trace. "
            "Panels group responsibilities from PipelineCompiler.compile_pipelines. "
            "Initial path and artifact planning precedes materialization planning; "
            "post-plan stages validate memory contracts and source metadata, assign "
            "framework devices, resolve remaining configuration and freeze contexts. "
            "Sequential mode is first inspected using a temporary initialized context "
            "and may cause each ordered component combination to be planned separately. "
            "Worker assignments and prepared functions are assembled after context "
            "compilation. Source-backend compatibility is also checked before axis "
            "fanout; panel D does not claim all validation occurs in one pass. "
            "Segment-to-measure labels illustrate declared artifact dependencies."
        ),
    )
    receipt["source_sha256"]["paper/figures/build_slas_visual_story.py"] = digest(
        ROOT / "paper/figures/build_slas_visual_story.py"
    )
    path.write_text(json.dumps(receipt, indent=2) + "\n")


if __name__ == "__main__":
    compiler()
