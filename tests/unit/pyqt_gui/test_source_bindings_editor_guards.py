"""Guards keeping the source-binding editor derived from its dataclasses (C3)."""

from __future__ import annotations

import ast
import importlib.util
from dataclasses import fields, is_dataclass
from enum import Enum
from pathlib import Path

import openhcs.core.source_bindings_preview as preview_module
import openhcs.pyqt_gui.widgets.source_bindings_editor as editor_module
from openhcs.core.source_bindings import NamedSourceBinding
from pyqt_reactive.widgets.editable_table import CellEditor, DataclassFieldColumns


def module_tree(module) -> ast.Module:
    return ast.parse(Path(module.__file__).read_text())


def test_editor_declares_no_column_roster_or_text_codec() -> None:
    tree = module_tree(editor_module)
    classes = [node for node in ast.walk(tree) if isinstance(node, ast.ClassDef)]
    functions = {
        node.name
        for node in ast.walk(tree)
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }

    assert not [
        node.name
        for node in classes
        if issubclass(getattr(editor_module, node.name, object), Enum)
    ]
    assert not [node.name for node in classes if node.name.endswith("Codec")]
    assert not functions & {"from_cells", "cells", "row_from_cells", "row_cells"}
    assert not [
        node.lineno
        for node in ast.walk(tree)
        if isinstance(node, ast.Attribute) and node.attr in {"split", "partition"}
    ], "Cells hold typed values; the editor never parses text into fields."


def test_editor_never_hand_lists_enum_choices() -> None:
    """Choices come from the field type through ChoiceCellEditor (rule 1a)."""

    iterated = [
        node.iter.id
        for node in ast.walk(module_tree(editor_module))
        if isinstance(node, (ast.For, ast.comprehension))
        and isinstance(node.iter, ast.Name)
    ]
    assert not [
        name
        for name in iterated
        if isinstance(getattr(editor_module, name, None), type)
        and issubclass(getattr(editor_module, name), Enum)
    ]


def test_source_binding_view_mirrors_are_gone() -> None:
    assert importlib.util.find_spec("openhcs.core.source_bindings_view") is None
    assert not [
        node.name
        for node in ast.walk(module_tree(preview_module))
        if isinstance(node, ast.ClassDef)
        and (node.name.endswith("View") or node.name.endswith("ViewModel"))
    ]


def leaf_fields(row_type: type, prefix: tuple[str, ...] = ()):
    from typing import get_type_hints

    hints = get_type_hints(row_type)
    for row_field in fields(row_type):
        annotation = hints[row_field.name]
        path = (*prefix, row_field.name)
        if isinstance(annotation, type) and is_dataclass(annotation):
            yield from leaf_fields(annotation, path)
            continue
        yield path, annotation


def test_every_editable_binding_field_has_a_derived_column() -> None:
    """A field gets a column exactly when a cell editor accepts its type."""

    column_paths = {column.path for column in DataclassFieldColumns.of(NamedSourceBinding)}
    for path, annotation in leaf_fields(NamedSourceBinding):
        editable = CellEditor.for_annotation(annotation) is not None
        assert (path in column_paths) is editable, path


# --- U6b: the widget declares sections; pyqt-reactive renders them ----------


def editor_widget_class() -> ast.ClassDef:
    return next(
        node
        for node in module_tree(editor_module).body
        if isinstance(node, ast.ClassDef) and node.name == "SourceBindingsEditorWidget"
    )


def test_widget_holds_declarations_only() -> None:
    """Rendering, value handling and chrome are inherited, not written here."""
    from pyqt_reactive.widgets.sectioned_dataclass_editor import SectionedDataclassEditor

    widget_class = editor_widget_class()
    methods = {
        node.name for node in widget_class.body if isinstance(node, ast.FunctionDef)
    }
    assert issubclass(editor_module.SourceBindingsEditorWidget, SectionedDataclassEditor)
    assert methods == {
        "__init__",
        "set_preview_context",
        "resolved_view_inputs",
        "suggestions",
        "step_bindings_dialog",
        "edit_step_bindings",
        "sections",
        "_preview_sections",
    }
    assert widget_class.end_lineno - widget_class.lineno < 200
    widget_calls = {
        node.func.id
        for node in ast.walk(widget_class)
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
    }
    assert not widget_calls & {
        "QTableWidget",
        "ScopedTableWidget",
        "QGroupBox",
        "QPushButton",
        "EditableTableController",
        "InlineDataclassChildChrome",
    }, "Sections build their own widgets."


def test_widget_has_one_optional_input_and_no_rendered_state() -> None:
    """The only ``None`` tests left are the optional inventory and an unset pairing."""
    widget_class = editor_widget_class()
    none_tests = [
        ast.unparse(node)
        for node in ast.walk(widget_class)
        if isinstance(node, ast.Compare)
        and any(isinstance(op, (ast.Is, ast.IsNot)) for op in node.ops)
        and any(
            isinstance(side, ast.Constant) and side.value is None
            for side in (node.left, *node.comparators)
        )
    ]
    assert sorted(none_tests) == ["plan is not None", "self._inventory is None"]
    assigned = {
        target.attr
        for node in ast.walk(widget_class)
        if isinstance(node, ast.Assign)
        for target in node.targets
        if isinstance(target, ast.Attribute)
    }
    assert assigned == {"_source_bindings", "_inventory"}


def test_new_filter_and_pairing_members_are_editable_without_a_widget_edit() -> None:
    """New-case test: a registered family member appears in its table's choices."""
    from PyQt6.QtWidgets import QApplication, QComboBox

    from openhcs.core.config import StepSourceBindingsConfig
    from openhcs.core.source_bindings import (
        PairByMetadata,
        PathIsImage,
        SourceFilterClause,
        SourceFilterSubject,
        SourceSetPairing,
    )

    app = QApplication.instance() or QApplication([])

    class ThrowawaySubject(SourceFilterSubject):
        name = "u6b_throwaway_subject"

        @staticmethod
        def text_of(file_path: str) -> str:
            return file_path.upper()

    class ThrowawayPairing(PairByMetadata):
        name = "u6b_throwaway_pairing"

    try:
        widget = editor_module.SourceBindingsEditorWidget.for_value(
            StepSourceBindingsConfig()
        )
        emitted: list[object] = []
        widget.connect_change_signal(emitted.append)

        widget.add_row("source_filters", SourceFilterClause(ThrowawaySubject, PathIsImage))
        widget.add_row(
            "match_plan", editor_module.SourceSetPairingRow(method=ThrowawayPairing)
        )
        app.processEvents()

        value = widget.get_value()
        assert value.source_filters[-1].subject is ThrowawaySubject
        assert type(value.match_plan) is ThrowawayPairing
        assert len(emitted) == 2

        def choice_texts(field_name: str, row_type: type, column: str) -> set[str]:
            combo = widget.table(field_name).cellWidget(
                0, DataclassFieldColumns.of(row_type).named(column).index
            )
            assert isinstance(combo, QComboBox)
            return {combo.itemText(index) for index in range(combo.count())}

        assert "u6b_throwaway_subject" in choice_texts(
            "source_filters", SourceFilterClause, "subject"
        )
        assert "u6b_throwaway_pairing" in choice_texts(
            "match_plan", editor_module.SourceSetPairingRow, "method"
        )
        widget.deleteLater()
    finally:
        del SourceFilterSubject.__registry__["u6b_throwaway_subject"]
        del SourceSetPairing.__registry__["u6b_throwaway_pairing"]
