"""G6 guards: the viewers stay blind to OpenHCS's domain and keep one mechanism each."""

from __future__ import annotations

import ast
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
OPENHCS = ROOT / "openhcs"
RUNTIME = OPENHCS / "runtime"
VIEWER_MODULES = tuple(
    sorted(
        {
            *RUNTIME.glob("*viewer*.py"),
            *RUNTIME.glob("napari_*.py"),
            *RUNTIME.glob("fiji_*.py"),
            *(OPENHCS / "napari_roi_manager").rglob("*.py"),
        }
    )
)
FIRST_PARTY_SOURCES = tuple((ROOT / "external").glob("*/src"))


def _python_files(*roots: Path) -> tuple[Path, ...]:
    return tuple(
        path
        for root in roots
        for path in ([root] if root.is_file() else root.rglob("*.py"))
        if "__pycache__" not in path.parts
    )


def _names(path: Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    found: set[str] = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Name):
            found.add(node.id)
        elif isinstance(node, ast.Attribute):
            found.add(node.attr)
        elif isinstance(node, (ast.ClassDef, ast.FunctionDef)):
            found.add(node.name)
        elif isinstance(node, ast.alias):
            found.add(node.name.rsplit(".", 1)[-1])
    return found


def _strings(path: Path) -> set[str]:
    tree = ast.parse(path.read_text(encoding="utf-8"))
    return {
        node.value
        for node in ast.walk(tree)
        if isinstance(node, ast.Constant) and isinstance(node.value, str)
    }


@pytest.mark.parametrize(
    "module",
    ("openhcs.runtime.napari_viewer_server", "openhcs.runtime.fiji_viewer_server"),
)
def test_viewer_server_imports_no_domain_orchestration_or_config(module) -> None:
    pytest.importorskip("napari")
    code = (
        "import importlib, json, sys\n"
        f"importlib.import_module({module!r})\n"
        "print(json.dumps(sorted(name for name in sys.modules if name.startswith('openhcs'))))\n"
    )
    env = {**os.environ, "PYTHONPATH": os.pathsep.join([str(ROOT), *sys.path])}
    result = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, env=env, check=True,
    )
    loaded = json.loads(result.stdout.strip().splitlines()[-1])
    forbidden = tuple(
        name
        for name in loaded
        if name.startswith(("openhcs.microscopes", "openhcs.core.orchestrator"))
        or name == "openhcs.core.config"
    )
    assert forbidden == ()


def test_viewer_modules_never_consult_the_process_axis_family() -> None:
    offenders = [
        path.relative_to(ROOT).as_posix()
        for path in VIEWER_MODULES
        if "AxisFamily" in _names(path)
    ]
    assert offenders == []


def test_flat_viewer_mode_enum_and_label_tables_are_gone() -> None:
    deleted = {
        "ViewerComponentMode",
        "ViewerComponentModeGroups",
        "viewer_component_mode_value",
        "ViewerAxisLabelStrategy",
        "role_modes_from_wire",
        "mode_field_for_axis",
        "NapariDisplayWireField",
        "FijiDisplayWireField",
    }
    offenders = {
        path.relative_to(ROOT).as_posix(): sorted(deleted & _names(path))
        for path in _python_files(OPENHCS, *FIRST_PARTY_SOURCES)
        if deleted & _names(path)
    }
    assert offenders == {}


def test_one_control_action_family_for_every_viewer() -> None:
    deleted = {
        "NapariControlMessageAction",
        "NapariUnknownControlMessageAction",
        "FijiControlMessagePlan",
        "FijiControlMessageAuthority",
        "FijiControlRequestContext",
        "FijiControlMessageResponse",
    }
    offenders = {
        path.relative_to(ROOT).as_posix(): sorted(
            name
            for name in _names(path)
            if name in deleted or (name.startswith("FijiUnsupported") and "Control" in name)
        )
        for path in VIEWER_MODULES
    }
    assert {path: names for path, names in offenders.items() if names} == {}
    fiji_literals = _strings(RUNTIME / "fiji_viewer_server.py")
    assert fiji_literals.isdisjoint({"shutdown", "force_shutdown", "clear_state"})


def test_viewer_identity_has_one_declaration_per_viewer() -> None:
    offenders = [
        path.relative_to(ROOT).as_posix()
        for path in _python_files(OPENHCS)
        if {"ViewerDeclarationABC", "NapariViewerDeclaration", "FijiViewerDeclaration",
            "viewer_type_declaration", "from_wire_value", "from_config_key"} & _names(path)
    ]
    assert offenders == []


def test_viewer_dtos_do_not_import_the_execution_dtos() -> None:
    tree = ast.parse((OPENHCS / "agent/dto/viewer.py").read_text(encoding="utf-8"))
    imported = {
        node.module
        for node in ast.walk(tree)
        if isinstance(node, ast.ImportFrom) and node.module is not None
    }
    assert "openhcs.agent.dto.execution" not in imported
