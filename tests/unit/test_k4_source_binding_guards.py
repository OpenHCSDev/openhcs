"""K4 guards: one source-binding config class, typed pairing, one path identity."""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from pathlib import Path

import pytest
from pycodify import Assignment, generate_python_source

from openhcs.core.source_binding_selection import SourceBoundAnchorPatternPolicy
from openhcs.core.source_binding_workspace import SourceSetAssembler
from openhcs.core.source_bindings import (
    PairByMetadata,
    PairByOrder,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceSetPairing,
)
from openhcs.core.source_path_identity import (
    source_path_identity,
    source_path_posix,
    source_paths_equal,
)

ROOT = Path(__file__).resolve().parents[2]
OPENHCS = ROOT / "openhcs"
SOURCE_MODULES = (
    *sorted((OPENHCS / "core").glob("source_*.py")),
    OPENHCS / "core" / "runtime_source_binding_cache.py",
)


def _tree(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def test_config_never_rebinds_another_modules_class():
    """Configs are decorated where they are defined: no rebinding, no monkeypatch."""

    tree = _tree(OPENHCS / "core" / "config.py")
    rebinds = [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Call)
        and isinstance(node.func.func, ast.Name)
        and node.func.func.id == "global_pipeline_config"
        and any(isinstance(arg, ast.Attribute) for arg in node.args)
    ]
    attribute_assignments = [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.Assign)
        and any(isinstance(target, ast.Attribute) for target in node.targets)
    ]
    assert rebinds == [] and attribute_assignments == []


def test_source_bindings_module_declares_no_config_class():
    tree = _tree(OPENHCS / "core" / "source_bindings.py")
    defined = {
        node.name for node in tree.body if isinstance(node, ast.ClassDef)
    } | {
        target.id
        for node in tree.body
        if isinstance(node, ast.Assign)
        for target in node.targets
        if isinstance(target, ast.Name)
    }
    assert not defined & {
        "SourceBindingsConfig",
        "StepSourceBindingsConfig",
        "EMPTY_SOURCE_BINDINGS",
    }


def test_step_source_bindings_has_one_class_whatever_the_import_order():
    script = "\n".join(
        [
            "from openhcs.core import source_bindings",
            "before = dict(vars(source_bindings))",
            "from openhcs.core import invocation_artifacts",
            "from openhcs.core.config import StepSourceBindingsConfig, EMPTY_SOURCE_BINDINGS",
            "assert dict(vars(source_bindings)) == before",
            "assert invocation_artifacts.StepSourceBindingsConfig is StepSourceBindingsConfig",
            "assert type(EMPTY_SOURCE_BINDINGS) is StepSourceBindingsConfig",
        ]
    )
    result = subprocess.run(
        [sys.executable, "-c", script], capture_output=True, text=True, check=False
    )
    assert result.returncode == 0, result.stderr


def test_pairing_is_a_family_and_never_absent():
    pattern = re.compile(
        r"SourceBindingMatchMethod|SourceBindingMatchPlan|match_plan is (not )?None"
    )
    offenders = [
        str(path.relative_to(ROOT))
        for path in OPENHCS.rglob("*.py")
        if pattern.search(path.read_text(encoding="utf-8"))
    ]
    assert offenders == []


@pytest.mark.parametrize(
    "family", (SourceSetAssembler, SourceBoundAnchorPatternPolicy), ids=lambda f: f.__name__
)
def test_every_pairing_has_its_strategies(family):
    for pairing in SourceSetPairing.__registry__.values():
        assert family.strategy_types_for_nominal_type(pairing), (family, pairing)


def test_pairing_names_decode_case_insensitively():
    assert SourceSetPairing.named("Order") is PairByOrder
    assert SourceSetPairing.named(" Metadata ") is PairByMetadata
    keys = (SourceBindingMatchDimension((SourceBindingMatchField("DNA", "well"),)),)
    assert PairByOrder.keyed_by(keys) == PairByOrder()
    assert PairByMetadata.keyed_by(keys) == PairByMetadata(dimensions=keys)


def test_source_modules_compare_paths_only_by_identity():
    """No resolve()/as_posix()/backslash rewriting decides path equality or spelling."""

    offenders = []
    for path in SOURCE_MODULES:
        if path.name == "source_path_identity.py":
            continue
        tree = _tree(path)
        for node in ast.walk(tree):
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr == "as_posix"
            ):
                offenders.append((path.name, node.lineno, "as_posix"))
            if isinstance(node, ast.Compare) and any(
                isinstance(operand, ast.Call)
                and isinstance(operand.func, ast.Attribute)
                and operand.func.attr == "resolve"
                for operand in (node.left, *node.comparators)
            ):
                offenders.append((path.name, node.lineno, "resolve-compare"))
        if '.replace("\\\\", "/")' in path.read_text(encoding="utf-8"):
            offenders.append((path.name, 0, "backslash-replace"))
    assert offenders == []


SPELLINGS = (
    "/data/screen/plate/a/../b.tif",
    "/data/screen/plate/./c//d.tif",
    "/data/screen/plate/b.tif",
    "/data/screen/other/../plate/c/d.tif",
    "/data/elsewhere/x.tif",
)


def test_saved_paths_load_back_with_the_identity_they_were_saved_with():
    """pycodify factors and normalizes saved paths; identity survives the round trip."""

    saved = [Path(spelling) for spelling in SPELLINGS]
    source = generate_python_source(Assignment("paths", saved))
    namespace: dict[str, object] = {}
    exec(compile(source, "<saved>", "exec"), namespace)
    loaded = namespace["paths"]

    assert "path_root = Path(" in source
    assert len(loaded) == len(saved)
    for original, reloaded in zip(saved, loaded, strict=True):
        assert source_paths_equal(original, reloaded), (original, reloaded)
        assert source_path_identity(reloaded) == source_path_identity(original)


def test_path_identity_is_lexical_and_idempotent():
    assert source_paths_equal("/data/screen/plate/a/../b.tif", "/data/screen/plate/b.tif")
    assert source_paths_equal("plate/./c//d.tif", "plate/c/d.tif")
    assert not source_paths_equal("../plate/b.tif", "plate/b.tif")
    assert source_path_posix("plate/a/../b.tif") == "plate/b.tif"
    for spelling in SPELLINGS:
        identity = source_path_identity(spelling)
        assert source_path_identity(identity) == identity
