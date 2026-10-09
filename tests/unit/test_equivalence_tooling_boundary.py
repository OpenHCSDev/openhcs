"""Guards keeping native-CellProfiler comparison tooling out of the product package."""

import ast
from pathlib import Path

PROJECT_ROOT = Path(__file__).parents[2]
PRODUCT_ROOT = PROJECT_ROOT / "openhcs"
EQUIVALENCE_PACKAGE = "openhcs.core.equivalence"


def _product_modules() -> dict[str, tuple[Path, bool]]:
    modules = {}
    for path in PRODUCT_ROOT.rglob("*.py"):
        parts = list(path.relative_to(PROJECT_ROOT).with_suffix("").parts)
        is_package = parts[-1] == "__init__"
        if is_package:
            parts.pop()
        modules[".".join(parts)] = (path, is_package)
    return modules


def _is_type_checking_guard(node: ast.AST) -> bool:
    return isinstance(node, ast.If) and (
        (isinstance(node.test, ast.Name) and node.test.id == "TYPE_CHECKING")
        or (
            isinstance(node.test, ast.Attribute)
            and node.test.attr == "TYPE_CHECKING"
        )
    )


def _runtime_imports(node: ast.AST):
    """Yield module- and function-level imports outside ``if TYPE_CHECKING:``."""
    for child in ast.iter_child_nodes(node):
        if _is_type_checking_guard(child):
            for orelse in child.orelse:
                yield from _runtime_imports_of(orelse)
            continue
        yield from _runtime_imports_of(child)


def _runtime_imports_of(node: ast.AST):
    if isinstance(node, (ast.Import, ast.ImportFrom)):
        yield node
    yield from _runtime_imports(node)


def _absolute_base(module: str, is_package: bool, node: ast.ImportFrom) -> str:
    if node.level == 0:
        return node.module or ""
    parts = module.split(".") if is_package else module.split(".")[:-1]
    parts = parts[: len(parts) - (node.level - 1)]
    return ".".join([*parts, *([node.module] if node.module else [])])


def _imported_modules(
    module: str,
    is_package: bool,
    tree: ast.AST,
    modules: dict[str, tuple[Path, bool]],
) -> set[str]:
    targets: set[str] = set()
    for node in _runtime_imports(tree):
        if isinstance(node, ast.Import):
            names = [alias.name for alias in node.names]
        else:
            base = _absolute_base(module, is_package, node)
            names = [f"{base}.{alias.name}" for alias in node.names] + [base]
        for name in names:
            while name and name not in modules:
                name = name.rpartition(".")[0]
            parts = name.split(".")
            targets.update(
                ".".join(parts[:index]) for index in range(1, len(parts) + 1)
            )
    return targets & modules.keys()


def test_product_modules_do_not_import_benchmark_tooling() -> None:
    offenders = []
    for path in PRODUCT_ROOT.rglob("*.py"):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                names = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom) and node.level == 0:
                names = [node.module or ""]
            else:
                continue
            offenders.extend(
                f"{path.relative_to(PROJECT_ROOT)}:{node.lineno} {name}"
                for name in names
                if name == "benchmark" or name.startswith("benchmark.")
            )
    assert offenders == []


def test_runtime_equivalence_comparison_module_is_not_a_product_module() -> None:
    assert not (PRODUCT_ROOT / "core/runtime_equivalence.py").exists()


def test_equivalence_package_root_is_not_a_reexport_facade() -> None:
    init = PRODUCT_ROOT / "core/equivalence/__init__.py"
    tree = ast.parse(init.read_text(encoding="utf-8"))

    assert not any(
        isinstance(node, (ast.Import, ast.ImportFrom)) for node in ast.walk(tree)
    )


def test_every_equivalence_module_is_reachable_from_product_code() -> None:
    modules = _product_modules()
    edges = {
        module: _imported_modules(
            module,
            is_package,
            ast.parse(path.read_text(encoding="utf-8"), filename=str(path)),
            modules,
        )
        for module, (path, is_package) in modules.items()
    }

    def in_package(module: str) -> bool:
        return module == EQUIVALENCE_PACKAGE or module.startswith(
            f"{EQUIVALENCE_PACKAGE}."
        )

    reached = {module for module in modules if not in_package(module)}
    frontier = list(reached)
    while frontier:
        for target in edges[frontier.pop()]:
            if target not in reached:
                reached.add(target)
                frontier.append(target)

    unreached = sorted(
        module for module in modules if in_package(module) and module not in reached
    )
    assert unreached == []
