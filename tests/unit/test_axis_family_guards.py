"""G1 guards: the axis family is the only axis identity, and the kernel names no member."""

from __future__ import annotations

import ast
from pathlib import Path

import openhcs
from openhcs.core.axes import AxisFamily
from openhcs.domains.microscopy.axes import Microscopy

REPO_ROOT = Path(openhcs.__file__).resolve().parents[1]

DELETED_NAMES = frozenset(
    {
        "AllComponents",
        "VariableComponents",
        "SequentialComponents",
        "StreamingComponents",
        "GroupBy",
        "get_openhcs_config",
        "_ComponentTemplate",
        "ComponentConfiguration",
        "ComponentConfigurationFactory",
        "MULTIPROCESSING_AXIS",
        "DEFAULT_GROUP_BY",
        "DEFAULT_VARIABLE_COMPONENTS",
        "get_default_group_by",
        "get_default_variable_components",
        "get_multiprocessing_axis",
        "convert_enum_by_value",
    }
)

# Domain modules may name microscopy members. P moves them under openhcs/domains/.
DOMAIN_MODULE_PREFIXES = (
    "openhcs/domains/",
    "openhcs/microscopes/",
    "openhcs/processing/presets/",
    "openhcs/demo/",
    "openhcs/mcp/installed_demo.py",
    "openhcs/processing/backends/analysis/consolidate_analysis_results.py",
    "openhcs/processing/backends/experimental_analysis/",
    "openhcs/formats/experimental_analysis.py",
)
# The product package root is the microscopy distribution's entry point.
DOMAIN_ENTRY_POINT = "openhcs/__init__.py"


def _python_files(*roots: str) -> list[Path]:
    files: list[Path] = []
    for root in roots:
        base = REPO_ROOT / root
        files.extend(
            path for path in base.rglob("*.py") if "benchmark/results" not in path.as_posix()
        )
    return files


def _relative(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _identifiers(tree: ast.AST) -> set[str]:
    names: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            names.add(node.id)
        elif isinstance(node, ast.Attribute):
            names.add(node.attr)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.alias):
            names.add(node.asname or node.name.rsplit(".", 1)[-1])
    return names


def test_deleted_component_enums_and_factory_do_not_exist() -> None:
    offenders = {
        _relative(path): sorted(DELETED_NAMES & _identifiers(ast.parse(path.read_text())))
        for path in _python_files("openhcs", "tests", "benchmark", "scripts")
        if path.name != Path(__file__).name
    }
    assert {path: names for path, names in offenders.items() if names} == {}
    assert not (REPO_ROOT / "openhcs/core/components/framework.py").exists()


def test_kernel_modules_name_no_microscopy_member() -> None:
    member_names = {axis.__name__ for axis in Microscopy.axes} | {Microscopy.__name__}
    offenders: dict[str, list[str]] = {}
    for path in _python_files("openhcs"):
        relative = _relative(path)
        if relative.startswith(DOMAIN_MODULE_PREFIXES) or relative == DOMAIN_ENTRY_POINT:
            continue
        tree = ast.parse(path.read_text())
        found: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and (node.module or "").startswith(
                "openhcs.domains"
            ):
                found.add(f"import {node.module}")
            elif isinstance(node, ast.Import):
                found.update(
                    f"import {alias.name}"
                    for alias in node.names
                    if alias.name.startswith("openhcs.domains")
                )
            elif isinstance(node, ast.Attribute) and node.attr in member_names:
                found.add(f".{node.attr}")
            elif isinstance(node, ast.Name) and node.id == Microscopy.__name__:
                found.add(node.id)
            elif (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and node.value.startswith("openhcs.domains")
            ):
                found.add(repr(node.value))
        if found:
            offenders[relative] = sorted(found)
    assert offenders == {}


def test_product_entry_point_activates_microscopy() -> None:
    assert AxisFamily.active() is Microscopy
