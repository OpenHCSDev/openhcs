"""Guards for the product boundary: research tools and vestigial packages stay out."""

from __future__ import annotations

import ast
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[2]
PRODUCT_ROOT = PROJECT_ROOT / "openhcs"

REMOVED_MODULES = (
    "openhcs.agent.blind_recipe_audit",
    "openhcs.components",
    "openhcs.core.components.multiprocessing",
    "openhcs.introspection",
    "openhcs.mcp.memory_diagnostic",
    "openhcs.mcp.memory_diagnostic_launch",
    "openhcs.mcp.recorded_evidence",
    "openhcs.utils.pipeline_migration",
    "openhcs.validation",
)
NON_PRODUCT_PACKAGES = ("benchmark", "scripts")


def _module_paths(module: str) -> tuple[Path, Path]:
    relative = Path(*module.split("."))
    return (
        PROJECT_ROOT / relative.with_suffix(".py"),
        PROJECT_ROOT / relative / "__init__.py",
    )


def _imported_modules(tree: ast.AST):
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                yield node.lineno, alias.name
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            yield node.lineno, node.module
            for alias in node.names:
                yield node.lineno, f"{node.module}.{alias.name}"
        elif (
            isinstance(node, ast.Constant)
            and isinstance(node.value, str)
            and "." in node.value
        ):
            # Dotted launches by module name (runpy, ``-m``, importlib) count too.
            yield node.lineno, node.value


def _within(module: str, package: str) -> bool:
    return module == package or module.startswith(f"{package}.")


@pytest.mark.parametrize("module", REMOVED_MODULES)
def test_removed_module_is_absent(module: str) -> None:
    assert not any(path.exists() for path in _module_paths(module)), module


def test_product_never_reaches_removed_or_non_product_modules() -> None:
    forbidden = (*REMOVED_MODULES, *NON_PRODUCT_PACKAGES)
    violations = [
        f"{path.relative_to(PROJECT_ROOT)}:{lineno}: {module}"
        for path in sorted(PRODUCT_ROOT.rglob("*.py"))
        for lineno, module in _imported_modules(ast.parse(path.read_text()))
        if any(_within(module, package) for package in forbidden)
    ]
    assert violations == []
