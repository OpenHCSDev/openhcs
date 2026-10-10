"""Surface L2 guards: python-introspect is the one codec and module-surface helper."""

from __future__ import annotations

import ast
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
MOVED_MODULES = ("openhcs.serialization.json", "openhcs.core.public_api")
DELETED_CODECS = {"AgentDtoJsonCodec", "DebugJsonCodec"}
# A dynamic module type (P1) and a loader of user functions from disk, neither a lazy export.
NON_EXPORT_MODULE_HOOKS = {
    "openhcs/processing/backends/cellprofiler/__init__.py",
    "openhcs/processing/custom_functions/__init__.py",
}


def tracked_python_files() -> list[Path]:
    listed = subprocess.run(
        ["git", "ls-files", "*.py"], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.split()
    return [REPO / name for name in listed if not name.startswith("external/")]


def parsed(path: Path) -> ast.Module | None:
    try:
        return ast.parse(path.read_text(encoding="utf-8"))
    except (SyntaxError, UnicodeDecodeError):
        return None


def imported_modules(tree: ast.Module) -> set[str]:
    modules: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module and not node.level:
            modules.add(node.module)
        elif isinstance(node, ast.Import):
            modules.update(alias.name for alias in node.names)
    return modules


def test_moved_modules_are_gone_and_unimported():
    for module in MOVED_MODULES:
        assert not (REPO / (module.replace(".", "/") + ".py")).exists(), module
    offenders = []
    for path in tracked_python_files():
        tree = parsed(path)
        if tree is not None and imported_modules(tree) & set(MOVED_MODULES):
            offenders.append(str(path.relative_to(REPO)))
    assert offenders == []


def test_no_local_dataclass_codecs():
    offenders = [
        f"{path.relative_to(REPO)}:{node.name}"
        for path in (REPO / "openhcs").rglob("*.py")
        if (tree := parsed(path)) is not None
        for node in ast.walk(tree)
        if isinstance(node, ast.ClassDef) and node.name in DELETED_CODECS
    ]
    assert offenders == []


def test_package_lazy_exports_use_python_introspect():
    offenders = []
    for root in ("openhcs", "benchmark"):
        for path in (REPO / root).rglob("__init__.py"):
            relative = str(path.relative_to(REPO))
            if relative in NON_EXPORT_MODULE_HOOKS or (tree := parsed(path)) is None:
                continue
            offenders.extend(
                f"{relative}:{node.name}"
                for node in tree.body
                if isinstance(node, ast.FunctionDef) and node.name in {"__getattr__", "__dir__"}
            )
    assert offenders == []
