"""L6 guards: generic source generation lives in pycodify and ObjectState."""

from __future__ import annotations

import ast
from pathlib import Path

ROOT = Path(__file__).parents[2]
OPENHCS = ROOT / "openhcs"

# Value families pycodify (Enum, Path, type, PythonSourceLiteral) and
# objectstate.codegen (lazy dataclasses) format; OpenHCS adds no formatter for them.
LIBRARY_FORMATTED = {
    "Enum",
    "Path",
    "PythonSourceLiteral",
    "LazyDataclass",
    "LazyResolutionDataclass",
}


def _python_files():
    return sorted(OPENHCS.rglob("*.py"))


def test_deleted_codegen_copies_stay_deleted():
    assert not (OPENHCS / "core/python_source_literal.py").exists()
    assert not (OPENHCS / "serialization/source_path_factoring.py").exists()


def test_no_openhcs_formatter_claims_a_library_value_family():
    violations = []
    for path in _python_files():
        tree = ast.parse(path.read_text(encoding="utf-8"))
        for node in ast.walk(tree):
            if not (isinstance(node, ast.FunctionDef) and node.name == "can_format"):
                continue
            for call in ast.walk(node):
                if not isinstance(call, ast.Call):
                    continue
                callee = ast.unparse(call.func)
                if callee == "inspect.isclass":
                    violations.append((path, call.lineno, callee))
                if callee == "isinstance" and len(call.args) == 2:
                    claimed = {
                        ast.unparse(name).rpartition(".")[2]
                        for name in ast.walk(call.args[1])
                        if isinstance(name, (ast.Name, ast.Attribute))
                    }
                    if claimed & LIBRARY_FORMATTED:
                        violations.append((path, call.lineno, sorted(claimed)))
    assert violations == []


def test_no_qualified_name_or_lazy_field_restatements():
    forbidden = ("__qualname__.partition", "_explicitly_set_fields")
    violations = [
        (path, needle)
        for path in _python_files()
        for needle in forbidden
        if needle in path.read_text(encoding="utf-8")
    ]
    assert violations == []


def test_objectstate_names_no_application_field():
    source_root = ROOT / "external/ObjectState/src"
    violations = [
        path
        for path in sorted(source_root.rglob("*"))
        if path.is_file()
        and path.suffix in {".py", ".rst", ".md"}
        and "well_filter" in path.read_text(encoding="utf-8")
    ]
    assert violations == []
