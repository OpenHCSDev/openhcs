"""Guards for U5: dead and misplaced desktop GUI code stays deleted."""

from __future__ import annotations

import ast
import re
from functools import cache
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parents[2]
PRODUCT_ROOT = PROJECT_ROOT / "openhcs"

REMOVED_MODULES = (
    "openhcs.pyqt_gui.dialogs.metadata_viewer_dialog",
    "openhcs.pyqt_gui.utils",
    "openhcs.ui.shared.pattern_data_manager",
    "openhcs.pyqt_gui.services.history_migration",
    # Moved into openhcs.desktop.
    "openhcs.desktop_installation",
    "openhcs.desktop_deployment",
    "openhcs.pyqt_gui.services.desktop_update",
    "openhcs.pyqt_gui.services.desktop_update_worker",
    "openhcs.pyqt_gui.services.desktop_restart",
    "openhcs.pyqt_gui.services.desktop_restart_worker",
    "openhcs.pyqt_gui.services.zmq_version_restart",
)
REMOVED_CLASSES = frozenset(
    {
        "MetadataViewerDialog",
        "PatternDataManager",
        "DesktopHistoryUpgrade",
        "PipelineEditorWorkflowSurface",
        "PlateManagerWorkflowSurface",
        "SignalConnectionSurface",
        "SignalEmissionSurface",
        "ConfigChangeSurface",
        "ExternalEditorProcess",
        "DesktopDeploymentAuthority",
    }
)
REMOVED_MEMBERS = {
    "PyQtServiceAdapter": frozenset(
        {
            "show_dialog",
            "run_system_command",
            "open_external_editor",
            "get_current_style_sheet",
            "get_theme_manager",
            "apply_color_scheme",
            "switch_to_dark_theme",
            "switch_to_light_theme",
            "load_theme_from_config",
            "save_current_theme",
            "register_theme_change_callback",
        }
    ),
    "GlobalEventBus": frozenset(
        {
            "step_changed",
            "emit_step_changed",
            "register_window",
            "unregister_window",
            "_registered_windows",
        }
    ),
}
MAIN_WINDOW_SERVICE_ALIASES = frozenset(
    {
        "window_services",
        "widget_services",
        "theme_manager_services",
        "window_color_scheme_services",
        "theme_file_services",
        "config_services",
    }
)
REMOVED_COMMENT = re.compile(r"#.*\bREMOVED\b")


def _module_paths(module: str) -> tuple[Path, Path]:
    relative = Path(*module.split("."))
    return (
        PROJECT_ROOT / relative.with_suffix(".py"),
        PROJECT_ROOT / relative / "__init__.py",
    )


@cache
def _product_trees() -> tuple[tuple[Path, ast.Module], ...]:
    return tuple(
        (path, ast.parse(path.read_text(encoding="utf-8"), filename=str(path)))
        for path in sorted(PRODUCT_ROOT.rglob("*.py"))
    )


def _imported_modules(tree: ast.AST):
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                yield node.lineno, alias.name
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            yield node.lineno, node.module
        elif isinstance(node, ast.Constant) and isinstance(node.value, str):
            yield node.lineno, node.value


@pytest.mark.parametrize("module", REMOVED_MODULES)
def test_removed_module_is_absent(module: str) -> None:
    assert not any(path.exists() for path in _module_paths(module)), module


def test_no_product_module_names_a_removed_module() -> None:
    offenders = [
        f"{path.relative_to(PROJECT_ROOT)}:{line}: {name}"
        for path, tree in _product_trees()
        for line, name in _imported_modules(tree)
        if any(name == m or name.startswith(f"{m}.") for m in REMOVED_MODULES)
        or name.startswith("objectstate.history_migration")
    ]
    assert offenders == []


def test_removed_classes_stay_undefined() -> None:
    offenders = [
        f"{path.relative_to(PROJECT_ROOT)}:{node.lineno}: {node.name}"
        for path, tree in _product_trees()
        for node in ast.walk(tree)
        if isinstance(node, ast.ClassDef) and node.name in REMOVED_CLASSES
    ]
    assert offenders == []


def _bound_class_members(node: ast.ClassDef) -> set[str]:
    names: set[str] = set()
    for statement in node.body:
        if isinstance(statement, (ast.FunctionDef, ast.AsyncFunctionDef)):
            names.add(statement.name)
        elif isinstance(statement, ast.Assign):
            names.update(t.id for t in statement.targets if isinstance(t, ast.Name))
        elif isinstance(statement, ast.AnnAssign) and isinstance(
            statement.target, ast.Name
        ):
            names.add(statement.target.id)
    for sub in ast.walk(node):
        if isinstance(sub, ast.Attribute) and isinstance(sub.ctx, ast.Store):
            if isinstance(sub.value, ast.Name) and sub.value.id == "self":
                names.add(sub.attr)
    return names


def test_service_adapter_and_event_bus_define_no_removed_members() -> None:
    found = {
        node.name: _bound_class_members(node) & REMOVED_MEMBERS[node.name]
        for _path, tree in _product_trees()
        for node in ast.walk(tree)
        if isinstance(node, ast.ClassDef) and node.name in REMOVED_MEMBERS
    }
    assert set(found) == set(REMOVED_MEMBERS)
    assert all(not members for members in found.values()), found


def test_main_window_holds_one_service_adapter() -> None:
    tree = ast.parse((PRODUCT_ROOT / "pyqt_gui" / "main.py").read_text("utf-8"))
    offenders = [
        f"main.py:{node.lineno}: {node.attr}"
        for node in ast.walk(tree)
        if isinstance(node, ast.Attribute) and node.attr in MAIN_WINDOW_SERVICE_ALIASES
    ]
    assert offenders == []


def _module_bound_names(tree: ast.Module) -> set[str]:
    names: set[str] = set()
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            names.update((a.asname or a.name).split(".")[0] for a in node.names)
        elif isinstance(node, ast.Assign):
            names.update(t.id for t in node.targets if isinstance(t, ast.Name))
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names.add(node.target.id)
    return names


def test_ui_package_rosters_name_only_bound_names() -> None:
    offenders = []
    for root in (PRODUCT_ROOT / "pyqt_gui", PRODUCT_ROOT / "ui"):
        for path in sorted(root.rglob("__init__.py")):
            tree = ast.parse(path.read_text(encoding="utf-8"))
            bound = _module_bound_names(tree)
            for node in tree.body:
                if not (
                    isinstance(node, ast.Assign)
                    and any(
                        isinstance(t, ast.Name) and t.id == "__all__"
                        for t in node.targets
                    )
                ):
                    continue
                if not isinstance(node.value, (ast.List, ast.Tuple)):
                    continue  # derived, e.g. lazy_exports(...)
                if not node.value.elts:
                    offenders.append(f"{path.relative_to(PROJECT_ROOT)}: empty __all__")
                offenders.extend(
                    f"{path.relative_to(PROJECT_ROOT)}: {element.value}"
                    for element in node.value.elts
                    if isinstance(element, ast.Constant) and element.value not in bound
                )
    assert offenders == []


def test_no_removed_comments_in_product_code() -> None:
    offenders = [
        f"{path.relative_to(PROJECT_ROOT)}:{number}"
        for path, _tree in _product_trees()
        for number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        )
        if line.lstrip().startswith("#") and REMOVED_COMMENT.search(line)
    ]
    assert offenders == []
