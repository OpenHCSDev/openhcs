"""K2 guards: the artifacts package owns one concept per module.

These checks keep the split from regrowing a monolith or a re-export shim, keep
kinds asking payloads instead of switching on their types, and keep the main
image flow a declared target instead of a ``None`` output plan.
"""

from __future__ import annotations

import ast
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
PACKAGE = ROOT / "openhcs" / "core" / "artifacts"
PACKAGE_MODULES = sorted(path for path in PACKAGE.glob("*.py") if path.name != "__init__.py")
SEARCHED_TREES = ("openhcs", "tests", "benchmark", "scripts", "docs", "paper")
SKIPPED_PARTS = {"results", "validation", "refactor", "archive", "__pycache__"}

# Owned payload types a kind must never switch on: the payload answers instead.
OWNED_PAYLOAD_TYPES = frozenset(
    {
        "RuntimeSliceAlignedValueSet",
        "RuntimeSliceAlignedValues",
        "RuntimeValue",
        "MeasurementTable",
        "ColumnarRows",
        "ImagePayload",
        "SourceProjectedImageOutput",
        "ObjectLabelValue",
        "ObjectLabelSet",
        "SpatialGrid",
        "SpatialGraph",
        "ObjectRelationship",
    }
)


def _tree(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _searched_sources() -> list[Path]:
    paths = []
    for tree in SEARCHED_TREES:
        for path in (ROOT / tree).rglob("*"):
            if path.suffix not in {".py", ".rst", ".md"}:
                continue
            if SKIPPED_PARTS.intersection(path.relative_to(ROOT).parts):
                continue
            paths.append(path)
    return paths


def test_artifacts_is_a_package_without_reexports() -> None:
    assert not (ROOT / "openhcs" / "core" / "artifacts.py").exists()
    init = _tree(PACKAGE / "__init__.py")
    assert [type(node) for node in init.body] == [ast.Expr], (
        "openhcs/core/artifacts/__init__.py may hold only its docstring"
    )


def test_no_source_imports_the_package_as_a_module() -> None:
    pattern = re.compile(r"from openhcs\.core\.artifacts import|import openhcs\.core\.artifacts\b")
    offenders = [
        str(path.relative_to(ROOT))
        for path in _searched_sources()
        if path.name != Path(__file__).name and pattern.search(path.read_text(encoding="utf-8"))
    ]
    assert offenders == []


def test_relation_requirements_are_declared_in_class_bodies() -> None:
    names = {"target_plan_type", "target_artifact_type", "source_plan_type", "source_artifact_type"}
    offenders = []
    for path in (ROOT / "openhcs").rglob("*.py"):
        for node in ast.walk(_tree(path)):
            if isinstance(node, ast.Assign):
                for target in node.targets:
                    if isinstance(target, ast.Attribute) and target.attr in names:
                        offenders.append(f"{path.relative_to(ROOT)}:{node.lineno}")
    assert offenders == []


def test_kinds_ask_payloads_instead_of_switching_on_their_types() -> None:
    tree = _tree(PACKAGE / "kinds.py")
    offenders = []
    for node in ast.walk(tree):
        match node:
            case ast.Call(func=ast.Name(id="isinstance"), args=[_, kind]):
                named = {
                    item.id
                    for item in ast.walk(kind)
                    if isinstance(item, ast.Name)
                }
                if named & OWNED_PAYLOAD_TYPES:
                    offenders.append(f"isinstance at {node.lineno}")
            case ast.Call(func=ast.Name(id="enumerate"), args=[ast.Attribute(attr="values")]):
                offenders.append(f"hand-written slice loop at {node.lineno}")
    assert offenders == []


@pytest.mark.parametrize(
    "relative",
    (
        *(str(path.relative_to(ROOT)) for path in PACKAGE_MODULES),
        "openhcs/core/steps/function_runtime.py",
        "openhcs/core/steps/function_artifact_materialization.py",
        *(
            str(path.relative_to(ROOT))
            for path in (ROOT / "openhcs" / "processing" / "materialization").glob("*.py")
        ),
    ),
)
def test_output_plan_absence_is_not_a_mode(relative: str) -> None:
    text = (ROOT / relative).read_text(encoding="utf-8")
    assert not re.search(r"output_plan is (not )?None|output_plan: [A-Za-z_.]+ \| None", text)


def test_deleted_enums_stay_deleted() -> None:
    pattern = re.compile(r"\b(ArtifactPayloadShape|ArtifactViewerStreaming)\b")
    offenders = [
        str(path.relative_to(ROOT))
        for path in _searched_sources()
        if path.suffix == ".py"
        and path.name != Path(__file__).name
        and pattern.search(path.read_text(encoding="utf-8"))
    ]
    assert offenders == []


def _foreign_absence_probes(tree: ast.Module) -> list[int]:
    """Mirror the structural ratchet: ``x.attr is None`` / ``not x.attr``, x not self."""

    def foreign(owner: ast.AST) -> bool:
        return not (isinstance(owner, ast.Name) and owner.id == "self")

    lines = []
    for node in ast.walk(tree):
        match node:
            case ast.Compare(
                left=ast.Attribute(value=owner),
                ops=[ast.Is() | ast.IsNot()],
                comparators=[ast.Constant(value=None)],
            ) if foreign(owner):
                lines.append(node.lineno)
            case ast.UnaryOp(op=ast.Not(), operand=ast.Attribute(value=owner)) if foreign(owner):
                lines.append(node.lineno)
            case ast.BoolOp(values=values) if len(values) >= 4:
                lines.append(node.lineno)
    return lines


@pytest.mark.parametrize("path", PACKAGE_MODULES, ids=lambda path: path.name)
def test_package_modules_carry_no_ratchet_debt(path: Path) -> None:
    assert _foreign_absence_probes(_tree(path)) == []
