"""U6c guards: the image browser declares; pyqt-reactive browses."""

from __future__ import annotations

import ast
from pathlib import Path

from openhcs.domains.microscopy.axes import Microscopy

MODULE = Path(__file__).resolve().parents[2] / "openhcs/pyqt_gui/widgets/image_browser.py"
TREE = ast.parse(MODULE.read_text(encoding="utf-8"))

GENERIC_QT_WIDGETS = {"QTreeWidget", "QTreeWidgetItem", "QDialog", "QLineEdit", "QTableWidget"}

DELETED_NAMES = {
    "ImageBrowserItem",
    "ImageBrowserViewerControls",
    "ImageBrowserMetadataDisplayResolver",
    "ImageBrowserFilterController",
    "ImageBrowserFileFocusController",
    "StreamingViewerField",
    "streaming_viewer_fields",
    "active_grid_axis",
    "require_grid_axis",
}


def _widget_class() -> ast.ClassDef:
    (widget,) = (
        node
        for node in TREE.body
        if isinstance(node, ast.ClassDef) and node.name == "ImageBrowserWidget"
    )
    return widget


def test_module_names_no_microscopy_axis() -> None:
    strings = {
        node.value
        for node in ast.walk(TREE)
        if isinstance(node, ast.Constant) and isinstance(node.value, str)
    }
    assert strings.isdisjoint(Microscopy.names())
    imported = {
        alias.name
        for node in ast.walk(TREE)
        if isinstance(node, ast.ImportFrom)
        for alias in node.names
        if (node.module or "").startswith("openhcs.domains")
    }
    assert imported == set()


def test_widget_has_no_none_mode() -> None:
    widget = _widget_class()
    none_tests = [
        node.lineno
        for node in ast.walk(widget)
        if isinstance(node, ast.Compare)
        and any(isinstance(op, ast.Is | ast.IsNot) for op in node.ops)
        and any(
            isinstance(comparator, ast.Constant) and comparator.value is None
            for comparator in node.comparators
        )
    ]
    none_attributes = [
        node.lineno
        for node in ast.walk(widget)
        if isinstance(node, ast.Assign)
        and isinstance(node.value, ast.Constant)
        and node.value.value is None
        and any(isinstance(target, ast.Attribute) for target in node.targets)
    ]
    assert none_tests == []
    assert none_attributes == []


def test_widget_methods_take_no_optional_dataset() -> None:
    """The missing dataset is ``NoDataset``, not an ``orchestrator`` that may be None."""

    names = {node.id for node in ast.walk(_widget_class()) if isinstance(node, ast.Name)}
    attributes = {
        node.attr for node in ast.walk(_widget_class()) if isinstance(node, ast.Attribute)
    }
    assert "orchestrator" not in names | attributes


def test_generic_qt_machinery_is_not_built_here() -> None:
    imported = {
        alias.name
        for node in ast.walk(TREE)
        if isinstance(node, ast.ImportFrom)
        for alias in node.names
    }
    assert imported.isdisjoint(GENERIC_QT_WIDGETS)


def test_deleted_names_stay_deleted() -> None:
    defined = {
        node.name
        for node in ast.walk(TREE)
        if isinstance(node, ast.ClassDef | ast.FunctionDef)
    }
    assert defined.isdisjoint(DELETED_NAMES)
    widget_methods = {
        node.name for node in _widget_class().body if isinstance(node, ast.FunctionDef)
    }
    assert len(widget_methods) <= 16
