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
from openhcs.pyqt_gui.widgets.source_bindings_editor import (
    CellEditor,
    DataclassFieldColumns,
)


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
