"""C5 guards: one backend-selection family, keys derived from declarations."""

import ast
from pathlib import Path

import openhcs
PRODUCT_ROOT = Path(openhcs.__file__).parent
BACKEND_MODULE = PRODUCT_ROOT / "processing/backends/cellprofiler/_backend.py"
DELETED_NAMES = (
    "AnalysisBackendProvider",
    "AnalysisBackendStrategyMixin",
    "analysis_backend_key",
    "as_regionprops_table_subset",
    "CellProfilerBackendAuthority",
    "LegacyFastNumpyShapeMeasurementBackendStrategy",
)


def _product_modules() -> tuple[tuple[Path, ast.Module], ...]:
    return tuple(
        (path, ast.parse(path.read_text(encoding="utf-8")))
        for path in sorted(PRODUCT_ROOT.rglob("*.py"))
    )


def _class_assignments(tree: ast.Module):
    for node in ast.walk(tree):
        if not isinstance(node, ast.ClassDef):
            continue
        for statement in node.body:
            targets = (
                statement.targets
                if isinstance(statement, ast.Assign)
                else (statement.target,)
                if isinstance(statement, ast.AnnAssign) and statement.value
                else ()
            )
            for target in targets:
                if isinstance(target, ast.Name):
                    yield node, target.id, statement.value


def test_backend_keys_and_registry_declarations_are_never_written_by_hand() -> None:
    violations = []
    for path, tree in _product_modules():
        for cls, name, value in _class_assignments(tree):
            if path == BACKEND_MODULE:
                continue
            if name == "backend_key":
                violations.append(f"{path}:{cls.lineno} {cls.name}.backend_key")
            if (
                name == "__registry_key__"
                and isinstance(value, ast.Constant)
                and value.value == "backend_key"
            ):
                violations.append(f"{path}:{cls.lineno} {cls.name}.__registry_key__")
    assert violations == []


def test_backends_declare_provider_classes_not_choice_members() -> None:
    violations = [
        f"{path}:{cls.lineno} {cls.name}"
        for path, tree in _product_modules()
        for cls, name, value in _class_assignments(tree)
        if name == "backend_provider"
        and isinstance(value, ast.Attribute)
        and isinstance(value.value, ast.Name)
        and value.value.id == "CellProfilerBackendProvider"
    ]
    assert violations == []


def test_provider_choice_list_is_not_a_hand_written_enum() -> None:
    tree = ast.parse(BACKEND_MODULE.read_text(encoding="utf-8"))
    assert not [
        node
        for node in ast.walk(tree)
        if isinstance(node, ast.ClassDef) and node.name == "CellProfilerBackendProvider"
    ]


def test_parallel_selection_mechanisms_stay_deleted() -> None:
    found = [
        f"{path}: {name}"
        for path, tree in _product_modules()
        for name in DELETED_NAMES
        if any(
            (isinstance(node, ast.Name) and node.id == name)
            or (isinstance(node, ast.Attribute) and node.attr == name)
            or (isinstance(node, (ast.ClassDef, ast.FunctionDef)) and node.name == name)
            or (isinstance(node, ast.alias) and node.name == name)
            for node in ast.walk(tree)
        )
    ]
    assert found == []
