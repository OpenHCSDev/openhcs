"""Structural guards: the processing package holds only live modules.

A module under ``openhcs/processing`` is live when the function registry admits
it (it declares a memory-decorated callable), when an ``AutoRegisterMeta``
family discovers it, when it is a pipeline document, or when live code imports
it. Liveness is derived from the registry's own declaration predicate and the
discovery packages that families declare; nothing here lists modules by name.
"""

from __future__ import annotations

import ast
from dataclasses import dataclass
from functools import cached_property
from pathlib import Path

from arraybridge.types import VALID_MEMORY_TYPES

import openhcs
from openhcs.processing.backends.lib_registry.openhcs_registry import (
    _source_declares_allowed_memory_type,
)

_OPENHCS_ROOT = Path(openhcs.__file__).parent
_PROCESSING_PACKAGE = "openhcs.processing"
_ALL_MEMORY_TYPES = frozenset(VALID_MEMORY_TYPES)


@dataclass(frozen=True)
class _SourceModule:
    name: str
    path: Path

    @cached_property
    def tree(self) -> ast.Module:
        return ast.parse(self.path.read_text(encoding="utf-8"), filename=str(self.path))

    @property
    def is_package(self) -> bool:
        return self.path.name == "__init__.py"

    def _absolute(self, node: ast.ImportFrom) -> str:
        if not node.level:
            return node.module or ""
        parts = self.name.split(".")
        if not self.is_package:
            parts = parts[:-1]
        parts = parts[: len(parts) - (node.level - 1)]
        return ".".join([*parts, *([node.module] if node.module else [])])

    @cached_property
    def referenced_modules(self) -> frozenset[str]:
        """Every dotted name this module imports or names as an import string."""

        names: set[str] = set()
        for node in ast.walk(self.tree):
            if isinstance(node, ast.Import):
                names.update(alias.name for alias in node.names)
            elif isinstance(node, ast.ImportFrom):
                base = self._absolute(node)
                names.add(base)
                names.update(f"{base}.{alias.name}" for alias in node.names)
            elif (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and node.value.startswith("openhcs.")
            ):
                names.add(node.value)
        return frozenset(
            ".".join(parts[:index])
            for name in names
            for parts in (name.split("."),)
            for index in range(1, len(parts) + 1)
        )

    @cached_property
    def declares_registered_function(self) -> bool:
        return _source_declares_allowed_memory_type(
            self.path.read_text(encoding="utf-8"),
            str(self.path),
            _ALL_MEMORY_TYPES,
        )

    @cached_property
    def declares_class(self) -> bool:
        return any(isinstance(node, ast.ClassDef) for node in self.tree.body)

    @cached_property
    def is_pipeline_document(self) -> bool:
        """Pipeline files bind ``pipeline_steps`` at module level and load by path."""

        return any(
            isinstance(bound, ast.Name) and bound.id == "pipeline_steps"
            for node in self.tree.body
            if isinstance(node, (ast.Assign, ast.AnnAssign))
            for target in (
                node.targets if isinstance(node, ast.Assign) else (node.target,)
            )
            for bound in (target.elts if isinstance(target, ast.Tuple) else (target,))
        )

    @cached_property
    def declared_discovery_packages(self) -> frozenset[str]:
        constants = {
            target.id: node.value.value
            for node in self.tree.body
            if isinstance(node, ast.Assign)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)
            for target in node.targets
            if isinstance(target, ast.Name)
        }
        packages: set[str] = set()
        for node in ast.walk(self.tree):
            if not isinstance(node, ast.keyword) or node.arg != "discovery_package":
                continue
            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                packages.add(node.value.value)
            elif isinstance(node.value, ast.Name) and node.value.id in constants:
                packages.add(constants[node.value.id])
        return frozenset(packages)


def _openhcs_modules() -> dict[str, _SourceModule]:
    modules: dict[str, _SourceModule] = {}
    for path in _OPENHCS_ROOT.rglob("*.py"):
        parts = list(path.relative_to(_OPENHCS_ROOT.parent).with_suffix("").parts)
        if parts[-1] == "__init__":
            parts.pop()
        name = ".".join(parts)
        modules[name] = _SourceModule(name, path)
    return modules


def _in_package(module_name: str, package: str) -> bool:
    return module_name == package or module_name.startswith(f"{package}.")


def test_every_processing_module_is_registered_discovered_or_imported() -> None:
    modules = _openhcs_modules()
    discovery_packages = frozenset(
        package
        for module in modules.values()
        for package in module.declared_discovery_packages
    )

    def is_root(module: _SourceModule) -> bool:
        return (
            not _in_package(module.name, _PROCESSING_PACKAGE)
            or module.declares_registered_function
            or module.is_pipeline_document
            or (
                module.declares_class
                and any(
                    _in_package(module.name, package) for package in discovery_packages
                )
            )
        )

    live: set[str] = set()
    pending = [name for name, module in modules.items() if is_root(module)]
    while pending:
        name = pending.pop()
        if name in live:
            continue
        live.add(name)
        pending.extend(
            referenced
            for referenced in modules[name].referenced_modules
            if referenced in modules and referenced not in live
        )

    dead = sorted(
        name
        for name in modules
        if _in_package(name, _PROCESSING_PACKAGE) and name not in live
    )
    assert dead == []


def test_materialization_format_roster_does_not_exist() -> None:
    offenders = sorted(
        f"{module.name}:{node.lineno}"
        for module in _openhcs_modules().values()
        for node in ast.walk(module.tree)
        if (isinstance(node, ast.ClassDef) and node.name == "MaterializationFormat")
        or (isinstance(node, ast.Name) and node.id == "MaterializationFormat")
        or (isinstance(node, ast.alias) and node.name == "MaterializationFormat")
    )
    assert offenders == []


def test_processing_package_reexports_nothing() -> None:
    """Registry lookups and memory decorators each have one import path."""

    package = _openhcs_modules()[_PROCESSING_PACKAGE]
    assert [
        ast.dump(node)
        for node in package.tree.body
        if not (
            isinstance(node, ast.Expr)
            and isinstance(node.value, ast.Constant)
            and isinstance(node.value.value, str)
        )
    ] == []
