"""Show one actual custom declaration reaching the selector, form and MCP.

Requires native captures and registration/detail receipts from the same isolated
authoring session. This illustration does not execute an image-analysis job.
"""

from __future__ import annotations

import ast
import io
import json
import keyword
from pathlib import Path
import textwrap
import tokenize

from matplotlib.patches import Rectangle
from matplotlib.font_manager import FontProperties
from matplotlib.textpath import TextPath

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


def python_excerpt(sheet, x, y, source, *, size=10.5):
    """Draw actual Python tokens as editable vector text, not a raster."""
    lines = source.splitlines()
    colors = [["#253346"] * len(line) for line in lines]
    for token in tokenize.generate_tokens(io.StringIO(source).readline):
        color = (
            BLUE if token.type == tokenize.NAME and keyword.iskeyword(token.string)
            else TEAL if token.type == tokenize.STRING
            else PURPLE if token.type == tokenize.NUMBER
            else MUTED if token.type == tokenize.COMMENT
            else None
        )
        if color is None:
            continue
        for row in range(token.start[0] - 1, min(token.end[0], len(lines))):
            start = token.start[1] if row == token.start[0] - 1 else 0
            end = token.end[1] if row == token.end[0] - 1 else len(lines[row])
            colors[row][start:end] = [color] * (end - start)
    font = FontProperties(family="DejaVu Sans Mono", size=size)
    # Include the advance, rather than glyph ink width, to retain indentation.
    advance = (TextPath((0, 0), "MM", prop=font).get_extents().width
               - TextPath((0, 0), "M", prop=font).get_extents().width)
    dx = advance / (sheet.figure.get_figwidth() * 72) * 100
    dy = size * 1.18 / (sheet.figure.get_figheight() * 72) * 100
    for row, line in enumerate(lines):
        start = 0
        while start < len(line):
            end = start + 1
            while end < len(line) and colors[row][end] == colors[row][start]:
                end += 1
            sheet.text(x + start * dx, y - row * dy, line[start:end],
                       size=size, color=colors[row][start], family="DejaVu Sans Mono",
                       va="top", parse_math=False)
            start = end


def extension(*, main_panel=False):
    sheet = FigureSheet(
        "submission_custom_function" if main_panel else "custom_function_extension",
        "" if main_panel else "One function declaration reaches the whole workflow",
        6.2 if main_panel else 7.6,
    )
    source_path = OUTPUT / "custom_signal_example.py"
    tree = ast.parse(source_path.read_text())
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef)]
    if len(functions) != 1:
        raise ValueError("The extension figure requires one function declaration")
    function = functions[0]
    registration_path = OUTPUT / ("custom_extension_fixed_openhcs_register_custom_function.json"
                                  if main_panel else "custom_extension_registration.json")
    detail_path = OUTPUT / ("custom_extension_live_function_detail.json"
                            if main_panel else "custom_extension_description.json")
    registration_response = json.loads(registration_path.read_text())
    detail_response = json.loads(detail_path.read_text())
    if not main_panel:
        registration_response = registration_response["response"]
        detail_response = detail_response["response"]
    registration = registration_response["results"][0][
        "payloads"
    ][0]
    detail = detail_response["results"][0]["payloads"][
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
        code_path = OUTPUT / "custom_extension_live_code_document.json"
        code = json.loads(code_path.read_text())["results"][0]["payloads"][0]
        code_tree = ast.parse(code["source"])
        pattern = next(node.value for node in code_tree.body
                       if isinstance(node, ast.Assign)
                       and any(isinstance(target, ast.Name) and target.id == "pattern"
                               for target in node.targets))
        if ast.literal_eval(pattern.elts[0].args[0]) != entry["function_id"]:
            raise ValueError("Live code identifies a different function")
        live_parameters = ast.literal_eval(pattern.elts[1])
        if any(live_parameters[name] != value for name, value in source_defaults.items()):
            raise ValueError("Live code parameters differ from the shown declaration")
        sheet.source(code_path)
        live_evidence_path = OUTPUT / "custom_extension_live_evidence.json"
        live_evidence = json.loads(live_evidence_path.read_text())
        if digest(source_path) != live_evidence["function_source_sha256"]:
            raise ValueError("Current function source differs from the native authoring record")
        sheet.source(live_evidence_path)
        sheet.text(3, 96, "II", size=14, weight="bold", color=BLUE)
        sheet.text(11, 96, "Function definition → generated form ↔ live code", size=12, weight="bold")
        # The actual declaration, including its array-backend decorator, is
        # the source of the shown defaults and descriptions, not a mock API.
        sheet.axis.add_patch(Rectangle((3, 24), 44, 65, color=PALE))
        python_excerpt(sheet, 5, 85, excerpt)
        sheet.text(5, 26, "Docstring excerpt; registered source retained", size=8.5, color=MUTED)
        sheet.arrow((48, 70), (52, 70), color=BLUE)
        sheet.text(50, 78, "Register", size=8, ha="center", rotation=90)
        sheet.text(53, 87, "Generated form controls", size=12, weight="bold")
        sheet.native_image("custom_extension_live_parameters_capture",
                           (53, 57, 44, 26), crop=(20, 113, 310, 224), response_path=())
        sheet.text(53, 54, "The same function and parameters", size=10, color=MUTED)
        sheet.text(53, 49, "Live editable Python", size=12, weight="bold")
        sheet.native_image("custom_extension_live_code_capture", (53, 25, 44, 23.3),
                           crop=(70, 38, 500, 194), response_path=())
        sheet.text(53, 23, "Native form and code • OpenHCS 0.8.7", size=9, color=PURPLE)
        sheet.text(3, 20, "The same declaration also supplies the agent-facing catalog", size=11, weight="bold")
        for index, name in enumerate(parameter_names):
            parameter = parameters[name]
            x = 3 + index * 48
            sheet.text(x, 14, f"{name}: {parameter['annotation']} = {parameter['default_repr']}",
                       size=10, family="DejaVu Sans Mono", color=TEAL)
            sheet.text(x, 10, parameter["description"], size=10, color=MUTED)
        sheet.text(50, 4, "Declaration-derived controls and catalog • editable Python uses the same workflow",
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
