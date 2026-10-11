"""Guards keeping generic Qt and ObjectState machinery in the libraries (U3 + L4)."""

from __future__ import annotations

import ast
from enum import Enum
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[3]
PRODUCT = REPO / "openhcs"
PYQT_REACTIVE = REPO / "external" / "pyqt-reactive" / "src" / "pyqt_reactive"
OBJECTSTATE = REPO / "external" / "ObjectState" / "src" / "objectstate"
FORMBRIDGE = REPO / "external" / "formbridge" / "src" / "formbridge"

MOVED_MODULES = (
    "core/path_cache.py",
    "core/field_label.py",
    "pyqt_gui/widgets/shared/time_travel_widget.py",
    "pyqt_gui/windows/snapshot_browser_window.py",
    "pyqt_gui/services/time_travel_navigation.py",
    "pyqt_gui/windows/config_edit_session.py",
    "pyqt_gui/services/config_window_code_document.py",
    "ui/shared/code_editor_form_updater.py",
    "pyqt_gui/widgets/shared/services/gui_event_bus_broadcast.py",
    "pyqt_gui/widgets/shared/plate_view_widget.py",
)

LIBRARY_NAMES = frozenset(
    {
        "GlobalEventBus",
        "GuiEventBusBroadcaster",
        "get_event_bus",
        "UnifiedPathCache",
        "FieldLabel",
        "CellEditor",
        "DataclassFieldColumns",
        "EditableTableController",
        "EditableTableLayout",
        "StructuredSelectorDialog",
        "MainWindowDockFloatController",
        "MainWindowDockPane",
        "MainWindowDockLayoutStore",
        "MainWindowShortcutLifecycle",
        "TimeTravelShortcutEventFilter",
        "MainWindowTimeTravelWorkflow",
        "TimeTravelWidget",
        "SnapshotBrowserWindow",
        "AspectRatioContainer",
        "PlateGridModel",
        "PlateViewWidget",
        "ConfigEditSession",
        "ConfigCodeDocumentDriver",
        "CodeEditorFormUpdater",
        "ExternalCodeEditorPreference",
        "ObjectStateFieldProvenanceEffect",
    }
)

SCOPE_SEPARATOR_EXEMPTIONS = frozenset(
    {
        ("openhcs/core/orchestrator/orchestrator.py", "local::"),
        ("openhcs/mcp/http_auth.py", "::1"),
        (
            "openhcs/agent/services/config_reference_service.py",
            "::(?:\\s+(?P<config_name>\\S+))?\\s*$",
        ),
    }
)


def _python_files(root: Path):
    return sorted(path for path in root.rglob("*.py") if "__pycache__" not in path.parts)


def _tree(path: Path) -> ast.Module:
    return ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def _docstring_nodes(tree: ast.Module) -> set[int]:
    return {
        id(node.body[0].value)
        for node in ast.walk(tree)
        if isinstance(node, (ast.Module, ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        and node.body
        and isinstance(node.body[0], ast.Expr)
        and isinstance(node.body[0].value, ast.Constant)
    }


def test_moved_modules_are_gone() -> None:
    assert [path for path in MOVED_MODULES if (PRODUCT / path).exists()] == []


def test_openhcs_defines_no_library_machinery() -> None:
    found = sorted(
        f"{path.relative_to(REPO)}:{node.lineno} {node.name}"
        for path in _python_files(PRODUCT)
        for node in ast.walk(_tree(path))
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        and node.name in LIBRARY_NAMES
    )
    assert found == []


@pytest.mark.parametrize(
    "root", (PRODUCT, PYQT_REACTIVE, FORMBRIDGE, OBJECTSTATE), ids=lambda p: p.name
)
def test_scope_ids_are_built_through_scope_key(root: Path) -> None:
    """No hand-written '::' scope grammar outside objectstate.scope_key."""

    offenders = []
    for path in _python_files(root):
        if path == OBJECTSTATE / "scope_key.py":
            continue
        tree = _tree(path)
        docstrings = _docstring_nodes(tree)
        relative = str(path.relative_to(REPO))
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and node.id == "SCOPE_SEGMENT_SEPARATOR":
                offenders.append(f"{relative}:{node.lineno} SCOPE_SEGMENT_SEPARATOR")
            if (
                isinstance(node, ast.Constant)
                and isinstance(node.value, str)
                and id(node) not in docstrings
                and (node.value.startswith("::") or node.value.endswith("::"))
                and (relative, node.value) not in SCOPE_SEPARATOR_EXEMPTIONS
            ):
                offenders.append(f"{relative}:{node.lineno} {node.value!r}")
    assert offenders == []


def test_xdg_paths_carry_no_legacy_migration() -> None:
    names = {
        node.name
        for node in ast.walk(_tree(PRODUCT / "core" / "xdg_paths.py"))
        if isinstance(node, (ast.FunctionDef, ast.ClassDef))
    }
    assert {name for name in names if "legacy" in name or name.startswith("migrate")} == set()


def test_library_families_are_classes_not_enums() -> None:
    import formbridge.core.path_cache as path_cache
    import pyqt_reactive.services.time_travel_navigation as time_travel_navigation
    import pyqt_reactive.widgets.enhanced_path_widget as enhanced_path_widget
    import pyqt_reactive.widgets.grid_selector as grid_selector

    enums = [
        f"{module.__name__}.{name}"
        for module in (path_cache, enhanced_path_widget, grid_selector, time_travel_navigation)
        for name, value in vars(module).items()
        if isinstance(value, type) and issubclass(value, Enum) and value.__module__ == module.__name__
    ]
    assert enums == []


def test_external_editor_switch_is_named_once() -> None:
    readers = sorted(
        str(path.relative_to(REPO))
        for path in (
            *_python_files(PRODUCT),
            *_python_files(PYQT_REACTIVE),
            *_python_files(FORMBRIDGE),
        )
        if "OPENHCS_USE_EXTERNAL_EDITOR" in path.read_text(encoding="utf-8")
    )
    assert readers == ["openhcs/pyqt_gui/services/reactor_providers.py"]


def test_field_markers_come_from_objectstate_inspection() -> None:
    offenders = sorted(
        f"{path.relative_to(REPO)}:{node.lineno}"
        for path in _python_files(PRODUCT / "pyqt_gui")
        for node in ast.walk(_tree(path))
        if isinstance(node, ast.Call)
        and isinstance(node.func, ast.Attribute)
        and node.func.attr == "append"
        and node.args
        and isinstance(node.args[0], ast.Constant)
        and node.args[0].value in {"*", "_"}
    )
    assert offenders == []
