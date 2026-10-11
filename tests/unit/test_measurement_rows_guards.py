"""K3 guards: measurement row kinds are families, and comparison tooling is not product."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PRODUCT = ROOT / "openhcs"

REMOVED_ENUMS = frozenset(
    {
        "ObjectFeatureArrayDomain",
        "ObjectFeatureMissingValue",
        "RuntimeMeasurementQualifierValueMode",
        "RuntimeMeasurementSourceNameEncoding",
    }
)
FAMILY_MODULES = (
    "openhcs/core/measurement_dialect.py",
    "openhcs/core/measurement_row_qualifiers.py",
    "openhcs/core/runtime_measurements.py",
)
COMPARISON_MODULES = (
    "openhcs.core.equivalence.measurement_rows",
    "openhcs.core.equivalence.measurement_facts",
)


def _product_trees():
    for path in sorted(PRODUCT.rglob("*.py")):
        yield path, ast.parse(path.read_text(), filename=str(path))


def test_removed_measurement_enums_stay_removed() -> None:
    found = sorted(
        f"{path.relative_to(ROOT)}:{node.lineno} {node.name}"
        for path, tree in _product_trees()
        for node in ast.walk(tree)
        if isinstance(node, ast.ClassDef) and node.name in REMOVED_ENUMS
    )
    assert not found


def test_measurement_families_do_not_restate_an_enum() -> None:
    for relative in FAMILY_MODULES:
        source = (ROOT / relative).read_text()
        assert "EnumKeyedStrategyMixin" not in source, relative


def test_product_does_not_import_comparison_row_tooling() -> None:
    found = sorted(
        f"{path.relative_to(ROOT)}:{node.lineno}"
        for path, tree in _product_trees()
        for node in ast.walk(tree)
        if (
            isinstance(node, ast.ImportFrom)
            and node.module in COMPARISON_MODULES
        )
        or (
            isinstance(node, ast.Import)
            and any(alias.name in COMPARISON_MODULES for alias in node.names)
        )
    )
    assert not found
    for module in COMPARISON_MODULES:
        assert not (ROOT / (module.replace(".", "/") + ".py")).exists(), module


def test_required_keys_has_no_none_mode_in_product() -> None:
    found = []
    for path, tree in _product_trees():
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Compare)
                and any(isinstance(op, (ast.Is, ast.IsNot)) for op in node.ops)
                and "required_key" in ast.unparse(node.left)
            ):
                found.append(f"{path.relative_to(ROOT)}:{node.lineno}")
    assert not found


def test_measurement_cells_have_one_payload_walker() -> None:
    tree = ast.parse((ROOT / "openhcs/core/equivalence/cells.py").read_text())
    recursive = sorted(
        node.name
        for node in tree.body
        if isinstance(node, ast.FunctionDef)
        and ("payload" in node.name or "hash" in node.name)
        and any(
            isinstance(call, ast.Call)
            and isinstance(call.func, ast.Name)
            and call.func.id == node.name
            for call in ast.walk(node)
        )
    )
    assert recursive == ["measurement_table_cell_payload"]
