"""CI runs pytest with ``--import-mode=importlib`` against the installed wheel
(``scripts/run_installed_tests.py``). In that mode a test directory is not on
``sys.path``, so a test module can reach shared helpers only through the
``tests`` package, never by a sibling module's bare name."""

from __future__ import annotations

import ast
from pathlib import Path

TESTS_ROOT = Path(__file__).resolve().parents[1]


def _test_tree_module_names() -> frozenset[str]:
    return frozenset(path.stem for path in TESTS_ROOT.rglob("*.py")) - {"__init__"}


def test_test_modules_import_helpers_through_the_tests_package() -> None:
    local_names = _test_tree_module_names()
    offenders: list[str] = []
    for path in sorted(TESTS_ROOT.rglob("*.py")):
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for node in ast.walk(tree):
            if isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                names = (node.module,)
            elif isinstance(node, ast.Import):
                names = tuple(alias.name for alias in node.names)
            else:
                continue
            for name in names:
                if name.split(".")[0] in local_names:
                    offenders.append(
                        f"{path.relative_to(TESTS_ROOT.parent)}:{node.lineno}: {name}"
                    )
    assert not offenders, (
        "Import test helpers as tests.<path>.<module>; bare sibling imports "
        "fail under --import-mode=importlib:\n" + "\n".join(offenders)
    )
