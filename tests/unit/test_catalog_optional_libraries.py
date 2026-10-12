"""The catalogue is complete for the installed frameworks when another is absent."""

from __future__ import annotations

import ast
import importlib.metadata
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
from packaging.requirements import Requirement
from packaging.utils import canonicalize_name

from openhcs.constants import MemoryType
from openhcs.core import lazy_gpu_imports
from openhcs.processing.backends.lib_registry import openhcs_registry

REPOSITORY_ROOT = Path(__file__).resolve().parents[2]
OPTIONAL_FRAMEWORKS = tuple(
    memory_type for memory_type in MemoryType if memory_type is not MemoryType.NUMPY
)
FRAMEWORK_BY_IMPORT_ROOT = {
    memory_type.import_name: memory_type for memory_type in OPTIONAL_FRAMEWORKS
}
OPTIONAL_IMPORT_FUNCTIONS = frozenset(
    {"optional_import_or_none", "optional_import_placeholder"}
)

DISCOVERY_WITH_BLOCKED_IMPORTS = """
import collections, importlib.abc, json, sys

blocked = frozenset(sys.argv[1:])


class AbsentLibrary(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path, target=None):
        if name.partition(".")[0] in blocked:
            raise ModuleNotFoundError(f"No module named {name!r}", name=name)
        return None


sys.meta_path.insert(0, AbsentLibrary())

from openhcs.processing.backends.lib_registry import openhcs_registry

try:
    functions = openhcs_registry.OpenHCSRegistry().discover_functions()
except ImportError as error:
    print(json.dumps({"import_error": (error.name or "").partition(".")[0]}))
else:
    counts = collections.Counter(
        memory_type.value
        for metadata in functions.values()
        for memory_type in openhcs_registry._catalog_memory_types(metadata.func) or ()
    )
    print(json.dumps({"counts": counts}))
"""


def _discover(tmp_path: Path, *blocked_import_roots: str) -> dict:
    """Run catalogue discovery in a fresh interpreter with libraries made absent."""

    environment = {
        key: value
        for key, value in os.environ.items()
        if key not in {"OPENHCS_CPU_ONLY", "DISPLAY", "WAYLAND_DISPLAY"}
    }
    environment["PYTHONPATH"] = str(REPOSITORY_ROOT)
    environment["XDG_DATA_HOME"] = str(tmp_path / "xdg")
    environment["QT_QPA_PLATFORM"] = "offscreen"
    completed = subprocess.run(
        [sys.executable, "-c", DISCOVERY_WITH_BLOCKED_IMPORTS, *blocked_import_roots],
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr[-4000:]
    return json.loads(completed.stdout.strip().splitlines()[-1])


def _distributions_required_here() -> frozenset[str]:
    """Distributions the OpenHCS requirements install here without any extra."""

    required: set[str] = set()
    pending = [("openhcs", frozenset({""}))]
    while pending:
        name, extras = pending.pop()
        try:
            requirements = importlib.metadata.requires(name) or ()
        except importlib.metadata.PackageNotFoundError:
            continue
        for requirement in map(Requirement, requirements):
            if requirement.marker is not None and not any(
                requirement.marker.evaluate({"extra": extra}) for extra in extras
            ):
                continue
            canonical = canonicalize_name(requirement.name)
            if canonical not in required:
                required.add(canonical)
                pending.append((canonical, frozenset({"", *requirement.extras})))
    return frozenset(required)


def _required_here(memory_type: MemoryType) -> bool:
    """Whether the package metadata makes this framework part of the installation."""

    distributions = importlib.metadata.packages_distributions().get(
        memory_type.import_name, ()
    )
    required = _distributions_required_here()
    return any(canonicalize_name(name) in required for name in distributions)


@pytest.fixture(scope="module")
def counts_with_nothing_blocked(tmp_path_factory) -> dict[str, int]:
    return _discover(tmp_path_factory.mktemp("catalog-baseline"))["counts"]


@pytest.mark.parametrize(
    "absent", OPTIONAL_FRAMEWORKS, ids=lambda memory_type: memory_type.value
)
def test_catalog_keeps_every_other_installed_framework_when_one_is_absent(
    absent: MemoryType,
    counts_with_nothing_blocked: dict[str, int],
    tmp_path: Path,
) -> None:
    installed = frozenset(
        memory_type for memory_type in MemoryType if memory_type.is_installed()
    )
    assert counts_with_nothing_blocked.keys() == {
        memory_type.value for memory_type in installed
    }

    outcome = _discover(tmp_path, absent.import_name)

    if absent in installed and _required_here(absent):
        # The package metadata installs it here, so its absence is a broken
        # installation and discovery says which import failed.
        assert outcome == {"import_error": absent.import_name}
        return
    assert outcome["counts"] == {
        memory_type.value: counts_with_nothing_blocked[memory_type.value]
        for memory_type in installed - {absent}
    }
    assert all(count > 0 for count in outcome["counts"].values())


def _module_level_statements(body: list[ast.stmt]):
    """Statements that run at import, through ``if`` and ``try`` blocks."""

    for statement in body:
        yield statement
        if isinstance(statement, ast.If):
            yield from _module_level_statements(statement.body)
            yield from _module_level_statements(statement.orelse)
        elif isinstance(statement, ast.Try):
            yield from _module_level_statements(statement.body)
            for handler in statement.handlers:
                yield from _module_level_statements(handler.body)
            yield from _module_level_statements(statement.orelse)


def _frameworks_bound_at_module_level(module_ast: ast.Module) -> frozenset[str]:
    """Frameworks a module imports or binds an optional import of, outside functions."""

    def framework(dotted_name: str) -> set[str]:
        memory_type = FRAMEWORK_BY_IMPORT_ROOT.get(dotted_name.partition(".")[0])
        return set() if memory_type is None else {memory_type.value}

    bound: set[str] = set()
    for statement in _module_level_statements(module_ast.body):
        if isinstance(statement, ast.Import):
            for imported in statement.names:
                bound |= framework(imported.name)
        elif isinstance(statement, ast.ImportFrom) and statement.module:
            if statement.module == lazy_gpu_imports.__name__:
                bound |= {
                    vars(lazy_gpu_imports)[imported.name]._memory_type.value
                    for imported in statement.names
                }
            elif not statement.level:
                bound |= framework(statement.module)
        elif isinstance(statement, (ast.Assign, ast.AnnAssign)) and statement.value:
            for node in ast.walk(statement.value):
                if (
                    isinstance(node, ast.Call)
                    and openhcs_registry._dotted_expression_name(node.func)
                    in OPTIONAL_IMPORT_FUNCTIONS
                ):
                    bound |= {
                        name
                        for argument in node.args
                        if isinstance(argument, ast.Constant)
                        and isinstance(argument.value, str)
                        for name in framework(argument.value)
                    }
    return frozenset(bound)


def _declared_memory_types(module_ast: ast.Module) -> frozenset[str]:
    import_bindings = openhcs_registry._module_import_bindings(module_ast)
    return frozenset(
        memory_type
        for node in ast.walk(module_ast)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
        for decorator in node.decorator_list
        for memory_type in (
            openhcs_registry._memory_type_from_decorator(decorator, import_bindings),
        )
        if memory_type is not None
    )


def test_catalog_modules_bind_only_the_frameworks_they_declare() -> None:
    """The memory-type decorator is the one statement of a module's framework need.

    A module the catalogue imports because framework A is installed must not
    reach for framework B at import or in a signature: B may be absent.
    """

    undeclared = {}
    declaring_modules = 0
    for module_name in openhcs_registry.OpenHCSRegistry()._get_openhcs_modules():
        module_source = openhcs_registry._module_source(module_name)
        if module_source is None:
            continue
        module_ast = openhcs_registry._parsed_source(*module_source)
        declared = _declared_memory_types(module_ast)
        if not declared:
            continue
        declaring_modules += 1
        extra = _frameworks_bound_at_module_level(module_ast) - declared
        if extra:
            undeclared[module_name] = sorted(extra)

    assert declaring_modules > 0
    assert undeclared == {}
