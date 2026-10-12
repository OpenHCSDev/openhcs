"""U4 guards: headless code needs no GUI toolkit, and OpenHCS keeps only its own declarations.

The toolkit-neutral tier (forms model, help, code documents, the running-UI
bridge DTOs, contracts, client and server) lives in formbridge; pyqt-reactive
holds the Qt window introspection; OpenHCS declares its application, identities,
surfaces and operations.
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[2]
PRODUCTION = REPOSITORY / "openhcs"
FORMBRIDGE = REPOSITORY / "external" / "formbridge" / "src" / "formbridge"
QT_BRIDGE = REPOSITORY / "external" / "pyqt-reactive" / "src" / "pyqt_reactive" / "bridge"
TOOLKITS = ("PyQt6", "PyQt5", "PySide6", "PySide2", "qtpy")


def test_headless_mcp_and_every_formbridge_module_load_no_toolkit() -> None:
    script = f"""
import builtins
import importlib
import pkgutil
import sys

toolkits = {TOOLKITS!r}
original_import = builtins.__import__

def reject_toolkit(name, globals=None, locals=None, fromlist=(), level=0):
    if level == 0 and name.split(".")[0] in toolkits:
        raise AssertionError(f"headless import loaded {{name}}")
    return original_import(name, globals, locals, fromlist, level)

builtins.__import__ = reject_toolkit
import openhcs  # a source checkout puts its external/ libraries on sys.path
import formbridge
for module in pkgutil.walk_packages(formbridge.__path__, "formbridge."):
    importlib.import_module(module.name)
from openhcs.mcp.server import build_server
import openhcs.mcp.http
build_server()
loaded = sorted(name for name in sys.modules if name.split(".")[0] in toolkits)
assert not loaded, loaded
"""
    completed = subprocess.run(
        [sys.executable, "-c", script],
        cwd=REPOSITORY,
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert completed.returncode == 0, completed.stderr[-4000:]


def _top_level_classes(root: Path) -> dict[str, Path]:
    classes = {}
    for path in root.rglob("*.py"):
        for node in ast.parse(path.read_text(encoding="utf-8")).body:
            if isinstance(node, ast.ClassDef):
                classes[node.name] = path
    return classes


def test_openhcs_defines_no_class_the_libraries_own() -> None:
    library = {**_top_level_classes(FORMBRIDGE), **_top_level_classes(QT_BRIDGE)}
    restated = sorted(
        f"{path.relative_to(REPOSITORY)}: {name}"
        for name, path in _top_level_classes(PRODUCTION).items()
        if name in library
    )
    assert restated == []


def test_libraries_name_no_openhcs_module() -> None:
    offenders = sorted(
        f"{path.relative_to(REPOSITORY)}:{node.lineno}"
        for root in (FORMBRIDGE, QT_BRIDGE)
        for path in root.rglob("*.py")
        for node in ast.walk(ast.parse(path.read_text(encoding="utf-8")))
        if isinstance(node, ast.ImportFrom | ast.Import)
        and any(
            (alias.name if isinstance(node, ast.Import) else node.module or "")
            .split(".")[0]
            == "openhcs"
            for alias in node.names
        )
    )
    assert offenders == []


def test_bridge_constants_and_identity_enums_stay_deleted() -> None:
    deleted = (
        "UI_BRIDGE_PROTOCOL_VERSION",
        "UiBridgeDescriptorEnvironment",
        "_identity_enum",
        "UiCodeDocumentId",
        "UiStateSurfaceId",
        "UiWidgetId",
        "enum_member_name",
        "_current_function_spec",
    )
    offenders = sorted(
        f"{path.relative_to(REPOSITORY)}: {name}"
        for root in (PRODUCTION, FORMBRIDGE, QT_BRIDGE)
        for path in root.rglob("*.py")
        for name in deleted
        if re.search(rf"\b{name}\b", path.read_text(encoding="utf-8"))
    )
    assert offenders == []


def test_moved_modules_do_not_exist_in_openhcs() -> None:
    moved = (
        "core/selection.py",
        "agent/runtime_platform.py",
        "agent/services/ui_bridge_transport.py",
        "agent/services/object_state_field_projection.py",
        "pyqt_gui/services/ui_bridge_contracts.py",
        "pyqt_gui/services/ui_bridge_registry.py",
        "pyqt_gui/services/ui_bridge_server.py",
        "pyqt_gui/services/ui_bridge_object_state.py",
        "pyqt_gui/services/ui_bridge_object_state_scope_policy.py",
    )
    assert [path for path in moved if (PRODUCTION / path).exists()] == []
