"""Show one actual custom declaration reaching the selector, form and MCP.

Requires native captures and registration/detail receipts from the same isolated
authoring session. This illustration does not execute an image-analysis job.
"""

from __future__ import annotations

import ast
import json
from pathlib import Path
import textwrap

from matplotlib.patches import Rectangle

from build_slas_visual_story import (
    BLUE,
    MUTED,
    PALE,
    PURPLE,
    TEAL,
    FigureSheet,
    OUTPUT,
    ROOT,
    digest,
)


def extension(*, main_panel=False):
    sheet = FigureSheet(
        "submission_custom_function" if main_panel else "custom_function_extension",
        "" if main_panel else "One function declaration reaches the whole workflow",
        5.2 if main_panel else 7.6,
    )
    source_path = OUTPUT / "custom_signal_example.py"
    tree = ast.parse(source_path.read_text())
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef)]
    if len(functions) != 1:
        raise ValueError("The extension figure requires one function declaration")
    function = functions[0]
    registration_path = OUTPUT / "custom_extension_registration.json"
    detail_path = OUTPUT / "custom_extension_description.json"
    registration = json.loads(registration_path.read_text())["response"]["results"][0][
        "payloads"
    ][0]
    detail = json.loads(detail_path.read_text())["response"]["results"][0]["payloads"][
        0
    ]
    if registration["registered_count"] != 1 or registration["errors"]:
        raise ValueError("Custom-function registration did not succeed")
    entry = registration["functions"][0]
    if (
        entry["name"] != function.name
        or detail["entry"]["function_id"] != entry["function_id"]
    ):
        raise ValueError(
            "Source, registration and MCP description identify different functions"
        )
    parameter_names = tuple(arg.arg for arg in function.args.args[1:])
    parameters = {parameter["name"]: parameter for parameter in detail["parameters"]}
    source_defaults = dict(
        zip(parameter_names, map(ast.literal_eval, function.args.defaults))
    )
    for name in parameter_names:
        if ast.literal_eval(parameters[name]["default_repr"]) != source_defaults[name]:
            raise ValueError(f"MCP default differs from the declaration for {name}")

    # Preserve the docstring in the main panel: it supplies agent descriptions.
    function.body = function.body if main_panel else [
        node
        for node in function.body
        if not (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)
        )
    ]
    imports = [
        node for node in tree.body if isinstance(node, (ast.Import, ast.ImportFrom))
    ]
    excerpt = (
        "\n".join(ast.unparse(node) for node in imports)
        + "\n\n"
        + ast.unparse(function)
    )
    if main_panel:
        # Reflow the actual signature and quote only the relevant docstring
        # lines; the full registered source remains the evidence owner.
        declared = ast.unparse(function)
        decorator, signature, *_ = declared.splitlines()
        signature = signature.replace("(", "(\n    ", 1).replace(", ", ",\n    ").replace("):", ",\n):")
        doc = ast.get_docstring(function).splitlines()
        descriptions = [line.strip() for line in doc
                        if line.strip().startswith(("gain:", "offset:"))]
        quoted = [doc[0], "", *descriptions]
        doc_excerpt = "\n".join(textwrap.fill(line, width=34) if line else "" for line in quoted)
        excerpt = ("\n".join(ast.unparse(node) for node in imports) + "\n\n" + decorator + "\n"
                   + signature + '\n    """' + doc_excerpt.replace("\n", "\n    ")
                   + '\n    """\n    ' + ast.unparse(function.body[-1]))
    for path in (
        source_path,
        registration_path,
        detail_path,
        ROOT / "paper/figures/build_slas_extension.py",
    ):
        sheet.source(path)
    evidence_path = OUTPUT / "custom_extension_evidence.json"
    evidence = json.loads(evidence_path.read_text())
    sheet.source(evidence_path)
    if digest(source_path) != evidence["custom_source"]["sha256"]:
        raise ValueError("Custom source differs from the captured registration")
    for receipt in evidence["receipts"].values():
        path = OUTPUT / Path(receipt["path"]).name
        if digest(path) != receipt["sha256"]:
            raise ValueError(f"Native interaction receipt changed: {path.name}")
        sheet.source(path)
    # Capture-specific patched source identities are retained in the evidence
    # record; these references describe the unchanged declaration owners.
    for path in (
        "openhcs/processing/custom_functions/manager.py",
        "openhcs/agent/services/function_catalog_service.py",
        "openhcs/core/steps/function_step.py",
    ):
        sheet.source(ROOT / path)

    if main_panel:
        sheet.text(3, 96, "VIII", size=14, weight="bold", color=BLUE)
        sheet.text(11, 96, "Lab Python becomes an editable analysis step", size=12, weight="bold")
        # The actual declaration, including its array-backend decorator, is
        # the source of the shown defaults and descriptions, not a mock API.
        sheet.axis.add_patch(Rectangle((3, 13), 52, 75, color=PALE))
        sheet.text(5, 84, excerpt, size=11.5, family="DejaVu Sans Mono",
                   va="top", linespacing=1.15)
        sheet.text(5, 17, "Docstring excerpt; full registered source retained", size=9, color=MUTED)
        sheet.arrow((56, 51), (61, 51), color=BLUE)
        sheet.text(58.5, 63, "Register\nsource", size=9, ha="center")
        sheet.text(64, 84, "Generated form controls", size=12, weight="bold")
        sheet.native_image("custom_extension_parameters_capture",
                           (64, 50, 33, 29), crop=(15, 337, 310, 445))
        sheet.text(64, 43, "Agent-facing catalog description", size=11, weight="bold")
        for index, name in enumerate(parameter_names):
            parameter = parameters[name]
            y = 34 - index * 12
            sheet.text(64, y, f"{name}: {parameter['annotation']} = {parameter['default_repr']}",
                       size=9, family="DejaVu Sans Mono", color=TEAL)
            sheet.text(64, y-5, parameter["description"], size=9, color=MUTED)
        sheet.text(50, 4, "One registered source • no function-specific form or MCP tool",
                   size=11, ha="center", color=MUTED)
        sheet.save()
        return

    sheet.panel("A", "Register a function with typed parameters", 3, 90)
    sheet.axis.add_patch(Rectangle((3, 67), 94, 20, color=PALE))
    sheet.text(
        5, 84.5, excerpt, size=11, family="DejaVu Sans Mono", va="top", linespacing=1.5
    )
    sheet.text(
        5,
        64,
        "Source excerpt; parameter descriptions come from its docstring",
        size=9,
        color=MUTED,
    )
    sheet.arrow((50, 62), (50, 58), color=BLUE)
    sheet.panel("B", "Select the registered function in the existing editor", 3, 55)
    sheet.native_image(
        "custom_extension_selector_capture", (3, 46, 94, 7), crop=(402, 586, 892, 618)
    )
    sheet.text(
        50,
        43,
        "Selected catalog entry (native UI detail)",
        size=9,
        ha="center",
        color=MUTED,
    )
    sheet.arrow((50, 41), (27, 38), color=TEAL)
    sheet.arrow((50, 41), (76, 38), color=PURPLE)
    sheet.panel("C", "Generated parameter controls", 3, 35)
    sheet.native_image(
        "custom_extension_parameters_capture", (3, 12, 47, 20), crop=(15, 337, 310, 445)
    )
    sheet.panel("D", "The same parameters through MCP", 54, 35)
    sheet.text(
        56, 30, entry["function_id"], size=8.5, family="DejaVu Sans Mono", color=PURPLE
    )
    for index, name in enumerate(parameter_names):
        parameter = parameters[name]
        y = 24 - index * 8
        sheet.text(
            56,
            y,
            f"{name}: {parameter['annotation']} = {parameter['default_repr']}",
            size=10,
            color=TEAL,
            family="DejaVu Sans Mono",
        )
        sheet.text(56, y - 3, parameter["description"], size=8.5, color=MUTED)
    sheet.text(
        50,
        6,
        "Use the registered function in ordinary pipeline steps",
        size=11,
        color=TEAL,
        weight="bold",
        ha="center",
    )
    sheet.save()


if __name__ == "__main__":
    extension()
