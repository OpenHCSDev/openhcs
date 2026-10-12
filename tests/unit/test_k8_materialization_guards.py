"""K8 guards: materialization is kernel code and values reach JSON one way.

- The materialization package lives in ``openhcs/core``; nothing names the old
  ``processing`` location.
- ``python_introspect.to_jsonable`` is the one value-to-JSON encoder: no other
  ``singledispatch`` function covers containers, numpy arrays and numpy
  scalars together (the signature of a value-to-JSON converter), and
  the two deleted converters stay deleted.
- Result file kinds are the ``ResultFileFormat`` family, not an enum.
"""

from __future__ import annotations

import ast
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOTS = ("openhcs", "tests", "benchmark", "scripts")
OLD_PACKAGE = ".".join(("openhcs", "processing", "materialization"))
DELETED_CONVERTERS = {"json_payload_value", "_json_value", "JsonPayloadAuthority"}
CONTAINER_TYPES = {"dict", "list", "tuple", "Mapping"}
NUMPY_VALUE_TYPES = {"ndarray", "generic"}


def _sources(*roots: str):
    for root in roots:
        for path in sorted((ROOT / root).rglob("*.py")):
            if "results" in path.relative_to(ROOT).parts:
                continue
            yield path


@lru_cache(maxsize=None)
def _tree(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"))


def _name(node: ast.expr) -> str | None:
    if isinstance(node, ast.Attribute):
        return node.attr
    if isinstance(node, ast.Name):
        return node.id
    return None


def test_materialization_package_is_in_core():
    assert not (ROOT / "openhcs" / "processing" / "materialization").exists()
    assert (ROOT / "openhcs" / "core" / "materialization" / "__init__.py").is_file()
    offenders = [
        str(path.relative_to(ROOT))
        for path in _sources(*SOURCE_ROOTS)
        if OLD_PACKAGE in path.read_text(encoding="utf-8")
    ]
    assert not offenders, offenders


def _registered_types_by_dispatcher(tree: ast.Module) -> dict[str, set[str]]:
    registered: dict[str, set[str]] = {}
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        function = node.func
        if not (isinstance(function, ast.Attribute) and function.attr == "register"):
            continue
        dispatcher = _name(function.value)
        if dispatcher is None or not node.args:
            continue
        type_name = _name(node.args[0])
        if type_name is not None:
            registered.setdefault(dispatcher, set()).add(type_name)
    return registered


def test_to_jsonable_is_the_only_value_to_json_dispatcher():
    offenders = []
    for path in _sources("openhcs", "benchmark", "scripts"):
        tree = _tree(path)
        for node in ast.walk(tree):
            if (
                isinstance(node, (ast.FunctionDef, ast.ClassDef))
                and node.name in DELETED_CONVERTERS
            ):
                offenders.append(f"{path.relative_to(ROOT)}: {node.name}")
        for dispatcher, types in _registered_types_by_dispatcher(tree).items():
            if dispatcher == "to_jsonable":
                continue
            if types & CONTAINER_TYPES and NUMPY_VALUE_TYPES <= types:
                offenders.append(f"{path.relative_to(ROOT)}: {dispatcher}")
    assert not offenders, offenders


def test_result_file_kinds_are_a_family():
    from openhcs.core.result_file_formats import ResultFileFormat

    enum_definitions = [
        str(path.relative_to(ROOT))
        for path in _sources("openhcs")
        for node in ast.walk(_tree(path))
        if isinstance(node, ast.ClassDef) and node.name == "FileFormat"
    ]
    assert not enum_definitions, enum_definitions
    members = dict(ResultFileFormat.__registry__)
    assert set(members) == {"TIFF", "NUMPY", "TEXT", "JSON", "CSV", "ROI"}
    for name, member in members.items():
        assert member.name == name
        for suffix in member.suffixes:
            assert ResultFileFormat.for_suffix_of(Path(f"result{suffix}")) is member
    assert [name for name, member in members.items() if member.streams_rois] == ["ROI"]
