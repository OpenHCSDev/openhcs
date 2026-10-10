"""L1 guards: strategy mixins and cache families are owned by metaclass-registry."""

import ast
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MOVED_MODULES = frozenset(
    {"openhcs.core.registry_strategies", "openhcs.core.process_local_cache"}
)
DEAD_CLASS_ATTRIBUTES = frozenset({"__enum_label_attr__", "stable_key_axis"})


def _python_files(*roots: str):
    for root in roots:
        for path in (REPO_ROOT / root).rglob("*.py"):
            if "benchmark/results" not in path.as_posix():
                yield path, ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _imported_modules(tree: ast.AST):
    for node in ast.walk(tree):
        if isinstance(node, ast.ImportFrom) and node.module is not None:
            yield node.module
            for alias in node.names:
                yield f"{node.module}.{alias.name}"
        elif isinstance(node, ast.Import):
            yield from (alias.name for alias in node.names)


def _assigned_names(node: ast.ClassDef):
    for statement in node.body:
        if isinstance(statement, ast.Assign):
            for target in statement.targets:
                if isinstance(target, ast.Name):
                    yield target.id
        elif isinstance(statement, ast.AnnAssign) and isinstance(statement.target, ast.Name):
            yield statement.target.id


def test_moved_registry_modules_are_gone_and_never_imported():
    for module in MOVED_MODULES:
        assert not (REPO_ROOT / (module.replace(".", "/") + ".py")).exists(), module
    offenders = sorted(
        f"{path.relative_to(REPO_ROOT)} imports {module}"
        for path, tree in _python_files("openhcs", "benchmark", "tests", "scripts")
        for module in _imported_modules(tree)
        if module in MOVED_MODULES
    )
    assert offenders == []


def test_strategy_and_cache_declarations_carry_no_dead_or_restated_keys():
    offenders = []
    for path, tree in _python_files("openhcs"):
        for node in ast.walk(tree):
            if not isinstance(node, ast.ClassDef):
                continue
            names = set(_assigned_names(node))
            location = f"{path.relative_to(REPO_ROOT)}:{node.lineno} {node.name}"
            offenders.extend(f"{location} declares {name}" for name in names & DEAD_CLASS_ATTRIBUTES)
            bases = {ast.unparse(base).split("[")[0].split(".")[-1] for base in node.bases}
            if bases & {"ProcessLocalBoundedCache", "IdentityBoundProcessCache"} and (
                "registry_key" in names
            ):
                offenders.append(f"{location} restates cache membership as registry_key")
    assert offenders == []
