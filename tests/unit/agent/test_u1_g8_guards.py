"""U1/G8 guards: authoring surfaces ask the axis family by role, not by member."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OPENHCS = ROOT / "openhcs"


def _modules(*parts: str) -> list[Path]:
    return sorted((OPENHCS.joinpath(*parts)).rglob("*.py"))


def test_agent_dto_and_mcp_have_no_well_filter_alias() -> None:
    offenders = [
        str(path.relative_to(ROOT))
        for path in (*_modules("agent", "dto"), *_modules("mcp"))
        if "well_filter" in path.read_text() or "well-filter" in path.read_text()
    ]
    assert offenders == []


def test_agent_dtos_declare_no_well_or_microscope_type_field() -> None:
    offenders = []
    for path in _modules("agent", "dto"):
        for node in ast.walk(ast.parse(path.read_text())):
            if not isinstance(node, ast.ClassDef):
                continue
            for statement in node.body:
                if (
                    isinstance(statement, ast.AnnAssign)
                    and isinstance(statement.target, ast.Name)
                    and statement.target.id in {"well", "microscope_type"}
                ):
                    offenders.append(f"{path.relative_to(ROOT)}:{node.name}.{statement.target.id}")
    assert offenders == []


def test_gui_restates_no_plate_grid_default_or_row_letter_decode() -> None:
    offenders = []
    for path in _modules("pyqt_gui"):
        tree = ast.parse(path.read_text())
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Tuple)
                and [getattr(element, "value", None) for element in node.elts] == [8, 12]
            ):
                offenders.append(f"{path.relative_to(ROOT)}:{node.lineno} (8, 12)")
            if (
                isinstance(node, ast.BinOp)
                and isinstance(node.op, (ast.Pow, ast.Mult))
                and any(
                    isinstance(side, ast.Constant) and side.value == 26
                    for side in (node.left, node.right)
                )
            ):
                offenders.append(f"{path.relative_to(ROOT)}:{node.lineno} base-26 decode")
    assert offenders == []


def test_grid_placement_is_declared_only_by_grid_addressed_axes() -> None:
    offenders = []
    for path in _modules():
        tree = ast.parse(path.read_text())
        for node in ast.walk(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            declares = {
                statement.name
                for statement in node.body
                if isinstance(statement, ast.FunctionDef)
            } & {"grid_coordinates", "grid_position", "row_label"}
            bases = {
                base.id if isinstance(base, ast.Name) else getattr(base, "attr", "")
                for base in node.bases
            }
            if declares and node.name != "GridAddressed" and "GridAddressed" not in bases:
                offenders.append(f"{path.relative_to(ROOT)}:{node.name}")
    assert offenders == []
