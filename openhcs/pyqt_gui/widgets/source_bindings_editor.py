"""PyQt source-bindings editor whose tables derive from the binding dataclasses."""

from __future__ import annotations

import re
from abc import ABC, abstractmethod
from dataclasses import MISSING, dataclass, field, fields, is_dataclass, replace
from enum import Enum
from functools import cache
from types import MappingProxyType, UnionType
from typing import (
    TYPE_CHECKING,
    Annotated,
    Callable,
    Generic,
    Mapping,
    TypeVar,
    Union,
    cast,
    get_args,
    get_origin,
    get_type_hints,
)

from metaclass_registry import AutoRegisterMeta
from PyQt6.QtCore import Qt, QTimer, pyqtSignal
from PyQt6.QtGui import QBrush, QColor
from PyQt6.QtWidgets import (
    QAbstractItemView,
    QCheckBox,
    QComboBox,
    QDialog,
    QDialogButtonBox,
    QGroupBox,
    QHBoxLayout,
    QHeaderView,
    QLabel,
    QLineEdit,
    QListWidget,
    QListWidgetItem,
    QPushButton,
    QSizePolicy,
    QStyle,
    QTableWidget,
    QTableWidgetItem,
    QVBoxLayout,
    QWidget,
)
from pyqt_reactive.protocols import (
    ChildFieldChromeRefreshable,
    ChildFieldIdentityProvider,
    ChildFieldNavigationTargetProvider,
    ChildFieldSemanticChromeRefreshable,
    ChildSubfieldNavigationTargetProvider,
    ChangeSignalEmitter,
    InlineDataclassGroupBoxChromeProvider,
    InlineDataclassRootResettable,
    PyQtWidgetMeta,
    RawResolvedValueSettable,
    ResolvedValuePreviewSettable,
    ValueGettable,
    ValueSettable,
)
from pyqt_reactive.forms.layout_constants import CURRENT_LAYOUT
from pyqt_reactive.forms.inline_dataclass_chrome import InlineDataclassChildChrome
from pyqt_reactive.forms.inline_dataclass_context import (
    InlineDataclassChildFieldIdentity,
    InlineDataclassFormContext,
)
from pyqt_reactive.forms.widget_creation_config import (
    EnabledTitleWidgetMoveAuthority,
)
from pyqt_reactive.forms.widget_strategies import PlaceholderConfig
from pyqt_reactive.widgets.shared.scoped_table_widget import ScopedTableWidget
from pyqt_reactive.widgets.shared.scope_color_receiver import ScopeColorSchemeReceiver
from pyqt_reactive.widgets.structural_table import (
    EditableTableSemanticBinding,
    IsomorphicDataclassRowPathPolicy,
    StructuralDescendantMaskTarget,
    StructuralFlashTarget,
    StructuralMaskedContainerTarget,
    StructuralTableCellTarget,
    StructuralWidgetTarget,
)
from pyqt_reactive.widgets.shared.clickable_help_components import (
    InlineDataclassGroupBox,
)
from pyqt_reactive.widgets.no_scroll_spinbox import NoScrollComboBox, NoneAwareCheckBox
from python_introspect import (
    AnnotationChoices,
    Enableable,
    SignatureAnalyzer,
    declared_annotation_choices,
    is_enableable,
)

from openhcs.core.field_label import FieldLabel
from openhcs.core.source_bindings import (
    ComponentSelector,
    EMPTY_SOURCE_BINDINGS,
    MetadataExtractionRule,
    MetadataSource,
    MetadataSelector,
    NamedSourceBinding,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    SourceBindingMatchMethod,
    SourceBindingMatchPlan,
    SourceFilterClause,
    SourceFilterMatchType,
    SourceFilterSubject,
    SourceBindingsConfig,
    StepSourceBindingsConfig,
)
from openhcs.core.source_bindings_preview import (
    SourceBindingsPreview,
    SourceInventory,
)
from objectstate import (
    DataclassFieldAccess,
    DottedFieldPath,
    ObjectStateSubfieldSemanticIndex,
    StructuralValuePath,
)
from objectstate.lazy_factory import (
    LazyDataclass,
    get_base_type_for_lazy,
    replace_raw,
    resolve_lazy_configurations_for_serialization,
)

if TYPE_CHECKING:
    from pyqt_reactive.forms.parameter_form_manager import ParameterFormManager
    from pyqt_reactive.forms.parameter_info_types import InlineDataclassWidgetInfo

EditableRowT = TypeVar("EditableRowT")
SourceBindingsEditorRawValue = SourceBindingsConfig | LazyDataclass
INVALID_CELL_VALUE_ERRORS = (ValueError, TypeError, re.error)
"""Errors a row constructor raises for a value the user has not finished editing."""

# --- Dataclass-derived table columns and typed cell editors -----------------
# Generic editable-table block owned by L4 (moves to pyqt-reactive): from here
# to ``EditableTableLayout`` inclusive.


@dataclass(frozen=True, slots=True)
class RowSuggestion:
    """Prefilled field values offered for a new record row in a picker dialog."""

    values: tuple[tuple[str, object], ...]
    label: str

    @classmethod
    def of(cls, row_type: type, **values: object) -> "RowSuggestion":
        columns = DataclassFieldColumns.of(row_type)
        return cls(
            values=tuple(values.items()),
            label=":".join(
                columns.named(name).editor.display(value)
                for name, value in values.items()
            ),
        )


RowSuggestionMap = Mapping[type, tuple[RowSuggestion, ...]]


@dataclass(frozen=True, slots=True)
class CellEditContext:
    """What a cell editor needs from its table besides the cell value."""

    on_change: Callable[[], None]
    suggestions: RowSuggestionMap = field(default_factory=lambda: MappingProxyType({}))


def cell_editor_key(name: str, cls: type) -> str:
    return name


class CellEditor(ABC, metaclass=AutoRegisterMeta):
    """Cell editor family keyed by the field annotation it edits.

    A cell holds a *raw* value (the widget's own state, e.g. item text); the
    editor converts it to the field's typed value. No raw value is ever a
    serialized encoding of several fields.
    """

    __registry_key__ = "editor_key"
    __key_extractor__ = cell_editor_key
    __skip_if_no_key__ = True

    def __init__(self, annotation: object) -> None:
        self.annotation = annotation

    @classmethod
    def for_annotation(cls, annotation: object) -> "CellEditor | None":
        for editor_type in cls.__registry__.values():
            if editor_type.accepts(annotation):
                return editor_type(annotation)
        return None

    @classmethod
    @abstractmethod
    def accepts(cls, annotation: object) -> bool: ...

    @abstractmethod
    def raw_for(self, value: object) -> object:
        """Return the raw cell state that renders ``value``."""

    @abstractmethod
    def empty_raw(self) -> object:
        """Raw state of a new cell whose field has no default."""

    @abstractmethod
    def value_from_raw(self, raw: object) -> object:
        """Return the typed field value; raise ``ValueError`` while incomplete."""

    @abstractmethod
    def display(self, value: object) -> str: ...

    @abstractmethod
    def create(
        self,
        table: QTableWidget,
        row: int,
        column: int,
        raw: object,
        context: CellEditContext,
    ) -> None: ...

    @abstractmethod
    def update(self, table: QTableWidget, row: int, column: int, raw: object) -> bool:
        """Update an existing cell in place; return False when it must be rebuilt."""

    @abstractmethod
    def raw(self, table: QTableWidget, row: int, column: int) -> object: ...

    @staticmethod
    def union_members(annotation: object) -> tuple[object, ...]:
        if get_origin(annotation) in (Union, UnionType):
            return get_args(annotation)
        return (annotation,)


class ScalarTextCellEditor(CellEditor):
    """Text item for ``str``/``int``/``float`` scalars, optionally ``None``."""

    SCALAR_TYPES = (str, int, float, bool)

    @classmethod
    def accepts(cls, annotation: object) -> bool:
        if annotation is bool:
            return False
        members = tuple(
            member
            for member in cls.union_members(annotation)
            if member is not type(None)
        )
        return bool(members) and all(member in cls.SCALAR_TYPES for member in members)

    @property
    def optional(self) -> bool:
        return type(None) in self.union_members(self.annotation)

    @property
    def scalar_type(self) -> type:
        members = tuple(
            member
            for member in self.union_members(self.annotation)
            if member is not type(None)
        )
        return members[0] if len(members) == 1 else str

    def raw_for(self, value: object) -> str:
        return "" if value is None else str(value)

    def empty_raw(self) -> str:
        return ""

    def value_from_raw(self, raw: object) -> object:
        text = str(raw).strip()
        if not text and self.optional:
            return None
        return self.scalar_type(text)

    def display(self, value: object) -> str:
        return self.raw_for(value)

    def create(self, table, row, column, raw, context) -> None:
        table.setItem(row, column, EditableTableItem(str(raw)))

    def update(self, table, row, column, raw) -> bool:
        item = table.item(row, column)
        if not isinstance(item, EditableTableItem):
            return False
        item.set_logical_text(str(raw))
        return True

    def raw(self, table, row, column) -> str:
        item = table.item(row, column)
        if item is None:
            return ""
        return EditableTableController._editable_item(item).data(
            EditableTableItem.LOGICAL_VALUE_ROLE
        )


class BooleanCellEditor(CellEditor):
    """Check box for ``bool`` fields."""

    @classmethod
    def accepts(cls, annotation: object) -> bool:
        return annotation is bool

    def raw_for(self, value: object) -> bool:
        return bool(value)

    def empty_raw(self) -> bool:
        return False

    def value_from_raw(self, raw: object) -> bool:
        return bool(raw)

    def display(self, value: object) -> str:
        return str(bool(value))

    def create(self, table, row, column, raw, context) -> None:
        checkbox = QCheckBox(table)
        checkbox.setChecked(bool(raw))
        checkbox.toggled.connect(lambda _checked: context.on_change())
        table.setCellWidget(row, column, checkbox)

    def update(self, table, row, column, raw) -> bool:
        checkbox = table.cellWidget(row, column)
        if not isinstance(checkbox, QCheckBox):
            return False
        blocked = checkbox.blockSignals(True)
        try:
            checkbox.setChecked(bool(raw))
        finally:
            checkbox.blockSignals(blocked)
        return True

    def raw(self, table, row, column) -> bool:
        checkbox = table.cellWidget(row, column)
        return isinstance(checkbox, QCheckBox) and checkbox.isChecked()


class ChoiceCellEditor(CellEditor):
    """Combo box whose choices are the field type's members.

    Declared ``AnnotationChoices`` supply their choices and labels; an ``Enum``
    type supplies its members; ``type[F]`` for an ``AutoRegisterMeta`` family
    supplies the family registry, labelled by each member's registry key.
    """

    COMBO_LOGICAL_TEXT_ROLE = Qt.ItemDataRole.UserRole + 1

    @classmethod
    def accepts(cls, annotation: object) -> bool:
        return (
            cls.declared_choices(annotation) is not None
            or cls.family(annotation) is not None
            or (isinstance(annotation, type) and issubclass(annotation, Enum))
        )

    @staticmethod
    def declared_choices(annotation: object) -> AnnotationChoices | None:
        if get_origin(annotation) is not Annotated:
            return None
        return declared_annotation_choices(annotation)

    @staticmethod
    def family(annotation: object) -> type | None:
        if get_origin(annotation) is not type:
            return None
        (member_type,) = get_args(annotation)
        return member_type if isinstance(member_type, AutoRegisterMeta) else None

    @property
    def choices(self) -> tuple[object, ...]:
        declared = self.declared_choices(self.annotation)
        if declared is not None:
            return declared.choices()
        family = self.family(self.annotation)
        if family is not None:
            return tuple(family.__registry__.values())
        return tuple(cast(type[Enum], self.annotation))

    def raw_for(self, value: object) -> object:
        return value

    def empty_raw(self) -> object:
        return self.choices[0]

    def value_from_raw(self, raw: object) -> object:
        return raw

    def display(self, value: object) -> str:
        declared = self.declared_choices(self.annotation)
        if declared is not None:
            return declared.label(value)
        family = self.family(self.annotation)
        if family is not None:
            return str(getattr(value, family.__registry_key__))
        return str(cast(Enum, value).value)

    def create(self, table, row, column, raw, context) -> None:
        combo = NoScrollComboBox(table)
        for choice in self.choices:
            text = self.display(choice)
            combo.addItem(text, choice)
            combo.setItemData(combo.count() - 1, text, self.COMBO_LOGICAL_TEXT_ROLE)
        combo.setCurrentIndex(self.index_of(combo, raw))
        combo.currentIndexChanged.connect(lambda _: context.on_change())
        combo.activated.connect(lambda _: context.on_change())
        table.setCellWidget(row, column, combo)

    def update(self, table, row, column, raw) -> bool:
        combo = table.cellWidget(row, column)
        if not isinstance(combo, QComboBox):
            return False
        index = self.index_of(combo, raw)
        if index < 0:
            return False
        blocked = combo.blockSignals(True)
        try:
            combo.setCurrentIndex(index)
        finally:
            combo.blockSignals(blocked)
        return True

    def raw(self, table, row, column) -> object:
        combo = table.cellWidget(row, column)
        if not isinstance(combo, QComboBox):
            raise TypeError("Choice cells are rendered as combo boxes.")
        return combo.currentData()

    @staticmethod
    def index_of(combo: QComboBox, value: object) -> int:
        for index in range(combo.count()):
            if combo.itemData(index) == value:
                return index
        return -1


class RecordTupleCellEditor(CellEditor):
    """Picker cell for ``tuple[Record, ...]`` with columns derived from ``Record``."""

    @classmethod
    def accepts(cls, annotation: object) -> bool:
        if get_origin(annotation) is not tuple:
            return False
        arguments = get_args(annotation)
        return (
            len(arguments) == 2
            and arguments[1] is Ellipsis
            and isinstance(arguments[0], type)
            and is_dataclass(arguments[0])
        )

    @property
    def element_type(self) -> type:
        return get_args(self.annotation)[0]

    def raw_for(self, value: object) -> tuple[object, ...]:
        return tuple(cast(tuple, value))

    def empty_raw(self) -> tuple[object, ...]:
        return ()

    def value_from_raw(self, raw: object) -> tuple[object, ...]:
        return tuple(cast(tuple, raw))

    def display(self, value: object) -> str:
        columns = DataclassFieldColumns.of(self.element_type)
        return "; ".join(
            ":".join(
                text
                for column in columns.columns
                if (text := column.editor.display(column.value_of(element)))
            )
            for element in cast(tuple, value)
        )

    def create(self, table, row, column, raw, context) -> None:
        table.setCellWidget(
            row,
            column,
            StructuredSelectorCellWidget(
                editor=self,
                value=self.value_from_raw(raw),
                suggestions=context.suggestions.get(self.element_type, ()),
                apply_changes=context.on_change,
                parent=table,
            ),
        )

    def update(self, table, row, column, raw) -> bool:
        widget = table.cellWidget(row, column)
        if not isinstance(widget, StructuredSelectorCellWidget):
            return False
        widget.set_value_silently(self.value_from_raw(raw))
        return True

    def raw(self, table, row, column) -> tuple[object, ...]:
        widget = table.cellWidget(row, column)
        if not isinstance(widget, StructuredSelectorCellWidget):
            raise TypeError("Record-list cells are rendered as selector widgets.")
        return widget.value()


@dataclass(frozen=True, slots=True)
class DataclassFieldColumn:
    """One editable leaf field of a row dataclass, at ``path`` from the row."""

    index: int
    path: tuple[str, ...]
    declaring_type: type
    editor: CellEditor
    label: str
    tooltip: str | None
    default: object = MISSING

    @property
    def name(self) -> str:
        return self.path[-1]

    def value_of(self, row: object) -> object:
        value = row
        for name in self.path:
            value = getattr(value, name)
        return value

    def replaced(self, row: object, value: object) -> object:
        """Return ``row`` with this field replaced; every other field is kept."""

        return self._replaced(row, self.path, value)

    @classmethod
    def _replaced(cls, row: object, path: tuple[str, ...], value: object) -> object:
        name, *rest = path
        if rest:
            value = cls._replaced(getattr(row, name), tuple(rest), value)
        return replace(row, **{name: value})


@dataclass(frozen=True, slots=True)
class DataclassFieldColumns:
    """Columns derived from a row dataclass: one per field a cell editor accepts.

    Nested dataclass fields contribute their own fields. Fields no editor accepts
    have no column; editing a row through ``replaced`` keeps them unchanged.
    """

    row_type: type
    columns: tuple[DataclassFieldColumn, ...]

    @classmethod
    @cache
    def of(cls, row_type: type) -> "DataclassFieldColumns":
        columns: list[DataclassFieldColumn] = []
        cls._collect(row_type, (), columns)
        return cls(row_type=row_type, columns=tuple(columns))

    @classmethod
    def _collect(
        cls,
        row_type: type,
        prefix: tuple[str, ...],
        columns: list[DataclassFieldColumn],
    ) -> None:
        hints = get_type_hints(row_type, include_extras=True)
        for row_field in fields(row_type):
            annotation, metadata = cls._split_annotated(hints[row_field.name])
            path = (*prefix, row_field.name)
            if isinstance(annotation, type) and is_dataclass(annotation):
                cls._collect(annotation, path, columns)
                continue
            editor = CellEditor.for_annotation(
                hints[row_field.name]
                if any(isinstance(item, AnnotationChoices) for item in metadata)
                else annotation
            )

            if editor is None:
                continue
            columns.append(
                DataclassFieldColumn(
                    index=len(columns),
                    path=path,
                    declaring_type=row_type,
                    editor=editor,
                    label=next(
                        (
                            item.text
                            for item in metadata
                            if isinstance(item, FieldLabel)
                        ),
                        row_field.name.replace("_", " ").title(),
                    ),
                    tooltip=SignatureAnalyzer.extract_field_documentation(
                        row_type,
                        row_field.name,
                    ),
                    default=row_field.default,
                )
            )

    @staticmethod
    def _split_annotated(annotation: object) -> tuple[object, tuple[object, ...]]:
        if get_origin(annotation) is Annotated:
            base, *metadata = get_args(annotation)
            return base, tuple(metadata)
        return annotation, ()

    def __len__(self) -> int:
        return len(self.columns)

    def __iter__(self):
        return iter(self.columns)

    def named(self, *path: str) -> DataclassFieldColumn:
        for column in self.columns:
            if column.path[-len(path) :] == path:
                return column
        raise KeyError(f"{self.row_type.__name__} has no column {'.'.join(path)}.")

    @property
    def labels(self) -> tuple[str, ...]:
        return tuple(column.label for column in self.columns)

    def apply_header_items(self, header_item: Callable[[int], QTableWidgetItem | None]):
        for column in self.columns:
            item = header_item(column.index)
            if item is not None and column.tooltip is not None:
                item.setToolTip(column.tooltip)

    @property
    def is_isomorphic(self) -> bool:
        return len(self.columns) == len(fields(self.row_type)) and all(
            len(column.path) == 1 for column in self.columns
        )

    def construct(self, values: tuple[object, ...]) -> object:
        """Build an isomorphic row from one typed value per field."""

        return self.row_type(
            **{column.name: value for column, value in zip(self.columns, values)}
        )

    def draft_raw(self, values: Mapping[str, object]) -> tuple[object, ...]:
        """Raw cells for a new row: given values, then field defaults, then empty."""

        return tuple(
            column.editor.raw_for(values[column.name])
            if column.name in values
            else (
                column.editor.raw_for(column.default)
                if column.default is not MISSING
                else column.editor.empty_raw()
            )
            for column in self.columns
        )


class StructuredSelectorCellWidget(QWidget):
    """Read-only summary of a record list with a typed picker dialog."""

    def __init__(
        self,
        *,
        editor: RecordTupleCellEditor,
        value: tuple[object, ...],
        suggestions: tuple[RowSuggestion, ...],
        apply_changes: Callable[[], None],
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self.editor = editor
        self.suggestions = suggestions
        self._value = value
        self._apply_changes = apply_changes
        self.semantic_marker_label = QLabel("", self)
        self.semantic_marker_label.setVisible(False)
        self.line_edit = QLineEdit(editor.display(value), self)
        self.line_edit.setReadOnly(True)
        picker_button = QPushButton("...", self)
        picker_button.setFixedWidth(28)
        picker_button.clicked.connect(self._open_picker)

        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(2)
        layout.addWidget(self.semantic_marker_label)
        layout.addWidget(self.line_edit, 1)
        layout.addWidget(picker_button)

    def value(self) -> tuple[object, ...]:
        return self._value

    def set_value(self, value: tuple[object, ...]) -> None:
        self.set_value_silently(value)
        self._apply_changes()

    def set_value_silently(self, value: tuple[object, ...]) -> None:
        self._value = tuple(value)
        self.line_edit.setText(self.editor.display(self._value))

    def set_semantic_markers(self, markers: tuple[str, ...]) -> None:
        """Render ObjectState-owned markers without changing the edit value."""

        self.semantic_marker_label.setText("".join(markers))
        self.semantic_marker_label.setVisible(bool(markers))

    def create_dialog(self) -> "StructuredSelectorDialog":
        return StructuredSelectorDialog(
            element_type=self.editor.element_type,
            suggestions=self.suggestions,
            value=self._value,
            parent=self,
        )

    def _open_picker(self) -> None:
        dialog = self.create_dialog()
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return
        self.set_value(dialog.value())


class StructuredSelectorDialog(QDialog):
    """Typed editor for a record list; its columns derive from the record type."""

    def __init__(
        self,
        *,
        element_type: type,
        suggestions: tuple[RowSuggestion, ...],
        value: tuple[object, ...],
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        columns = DataclassFieldColumns.of(element_type)
        self.setWindowTitle(f"Edit {element_type.__name__} list")
        self.table = QTableWidget(0, len(columns), self)
        self.table.setHorizontalHeaderLabels(columns.labels)
        columns.apply_header_items(self.table.horizontalHeaderItem)
        self.validation_label = QLabel(self)
        self.controller: EditableTableController[object] = EditableTableController(
            table=self.table,
            columns=columns,
            apply_changes=self._update_validation_hint,
        )
        for element in value:
            self.controller.append(element)
        self.table.itemChanged.connect(
            lambda _item: self.controller.request_apply_changes()
        )
        self.suggestions = QListWidget(self)
        for suggestion in suggestions:
            item = QListWidgetItem(suggestion.label)
            item.setData(Qt.ItemDataRole.UserRole, suggestion)
            self.suggestions.addItem(item)
        self.suggestions.itemDoubleClicked.connect(
            lambda item: self._append_suggestion(item.data(Qt.ItemDataRole.UserRole))
        )
        add_button = QPushButton("Add selected", self)
        add_button.clicked.connect(self._append_selected)
        add_row_button = QPushButton("Add row", self)
        add_row_button.clicked.connect(lambda: self.append_draft({}))
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel,
            self,
        )
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        layout = QVBoxLayout(self)
        layout.addWidget(self.table)
        layout.addWidget(self.validation_label)
        layout.addWidget(add_row_button)
        layout.addWidget(QLabel("Suggestions", self))
        layout.addWidget(self.suggestions)
        layout.addWidget(add_button)
        layout.addWidget(buttons)
        self._update_validation_hint()

    def value(self) -> tuple[object, ...]:
        return self.controller.rows()

    def append_draft(self, values: Mapping[str, object]) -> None:
        self.controller.append_draft(values)
        self._update_validation_hint()

    def _append_selected(self) -> None:
        for item in self.suggestions.selectedItems():
            self._append_suggestion(item.data(Qt.ItemDataRole.UserRole))

    def _append_suggestion(self, suggestion: RowSuggestion) -> None:
        self.append_draft(dict(suggestion.values))

    def _update_validation_hint(self) -> None:
        invalid_rows = self.controller.incomplete_row_numbers()
        if invalid_rows:
            joined_rows = ", ".join(str(row) for row in invalid_rows)
            self.validation_label.setText(f"Incomplete rows ignored: {joined_rows}")
            return
        self.validation_label.setText("All rows are structurally valid.")


RawRow = tuple[object, ...]


@dataclass(slots=True, weakref_slot=True)
class EditableTableProgrammaticUpdateGuard:
    """Suppress table-driven change callbacks while the model updates the view."""

    depth: int = 0
    pending_release: bool = False
    programmatic_row_values: tuple[RawRow, ...] | None = None

    def __enter__(self) -> "EditableTableProgrammaticUpdateGuard":
        self.depth += 1
        self.pending_release = False
        self.programmatic_row_values = None
        return self

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        if self.depth > 0:
            self.depth -= 1
        self.pending_release = True
        QTimer.singleShot(0, lambda: self._release_pending())

    @property
    def active(self) -> bool:
        return self.depth > 0

    def remember_rows(self, row_values: tuple[RawRow, ...]) -> None:
        """Record the table rows produced by the current programmatic update."""

        self.programmatic_row_values = row_values

    def suppress_pending_rows(
        self,
        row_values: tuple[RawRow, ...],
    ) -> None:
        """Suppress delayed callbacks that still reflect programmatic rows."""

        self.pending_release = True
        self.remember_rows(row_values)
        QTimer.singleShot(0, lambda: self._release_pending())

    def should_suppress_pending_rows(
        self,
        row_values: tuple[RawRow, ...],
    ) -> bool:
        """Whether a pending callback still reflects the programmatic rows."""

        return self.pending_release and self.programmatic_row_values == row_values

    def release(self) -> None:
        self.pending_release = False
        self.programmatic_row_values = None

    def _release_pending(self) -> None:
        if self.depth == 0:
            self.release()


class EditableTableItem(QTableWidgetItem):
    """QTableWidgetItem with separate logical/edit value and rendered chrome."""

    LOGICAL_VALUE_ROLE = Qt.ItemDataRole.UserRole
    RENDERED_TEXT_ROLE = Qt.ItemDataRole.UserRole + 1

    def __init__(self, value: str) -> None:
        super().__init__()
        self._logical_value = value
        self._rendered_text = value
        super().setData(Qt.ItemDataRole.DisplayRole, value)

    def data(self, role):
        if role == Qt.ItemDataRole.DisplayRole:
            return self._rendered_text
        if role == Qt.ItemDataRole.EditRole:
            return self._logical_value
        if role == self.LOGICAL_VALUE_ROLE:
            return self._logical_value
        if role == self.RENDERED_TEXT_ROLE:
            return self._rendered_text
        return super().data(role)

    def setData(self, role, value) -> None:
        text = "" if value is None else str(value)
        if role == Qt.ItemDataRole.EditRole:
            self.set_logical_text(text)
            return
        if role == Qt.ItemDataRole.DisplayRole:
            self.set_rendered_text(text)
            return
        if role == self.LOGICAL_VALUE_ROLE:
            self._logical_value = text
            super().setData(self.LOGICAL_VALUE_ROLE, text)
            return
        if role == self.RENDERED_TEXT_ROLE:
            self.set_rendered_text(text)
            return
        super().setData(role, value)

    def setText(self, text: str) -> None:
        self.set_logical_text(text)

    def set_logical_text(self, value: str) -> None:
        self._logical_value = value
        self._rendered_text = value
        super().setData(self.LOGICAL_VALUE_ROLE, value)
        super().setData(self.RENDERED_TEXT_ROLE, value)
        super().setData(Qt.ItemDataRole.DisplayRole, value)

    def set_rendered_text(self, value: str) -> None:
        self._rendered_text = value
        super().setData(self.RENDERED_TEXT_ROLE, value)
        super().setData(Qt.ItemDataRole.DisplayRole, value)


@dataclass(frozen=True)
class EditableTableController(Generic[EditableRowT]):
    """Own editable Qt table mechanics for one isomorphic row dataclass.

    Every field of the row type has a column, so a row is constructed from its
    typed cell values without losing anything.
    """

    LOGICAL_VALUE_ROLE = EditableTableItem.LOGICAL_VALUE_ROLE
    RENDERED_TEXT_ROLE = EditableTableItem.RENDERED_TEXT_ROLE
    COMBO_LOGICAL_TEXT_ROLE = ChoiceCellEditor.COMBO_LOGICAL_TEXT_ROLE

    table: QTableWidget
    columns: DataclassFieldColumns
    apply_changes: Callable[[], None]
    suggestions: RowSuggestionMap = field(default_factory=lambda: MappingProxyType({}))
    semantic_binding: EditableTableSemanticBinding | None = None
    update_guard: EditableTableProgrammaticUpdateGuard = field(
        default_factory=EditableTableProgrammaticUpdateGuard,
    )

    def __post_init__(self) -> None:
        if not self.columns.is_isomorphic:
            raise TypeError(
                f"{self.columns.row_type.__name__} has fields without an editable "
                "column; edit it through replace-based typed rows instead."
            )

    @property
    def cell_context(self) -> CellEditContext:
        return CellEditContext(
            on_change=self.request_apply_changes,
            suggestions=self.suggestions,
        )

    def append(self, row_model: EditableRowT) -> None:
        self._append_raw(
            tuple(
                column.editor.raw_for(column.value_of(row_model))
                for column in self.columns
            )
        )

    def append_draft(self, values: Mapping[str, object]) -> None:
        """Append a row prefilled with ``values`` that may not be complete yet."""

        self._append_raw(self.columns.draft_raw(values))

    def _append_raw(self, raw_row: RawRow) -> None:
        table_signals_blocked = self.table.blockSignals(True)
        try:
            row_index = self.table.rowCount()
            self.table.insertRow(row_index)
            for column, raw in zip(self.columns, raw_row, strict=True):
                self._set_cell(row_index, column, raw)
        finally:
            self.table.blockSignals(table_signals_blocked)

    def replace_all(self, row_models: tuple[EditableRowT, ...]) -> bool:
        """Replace table contents; return whether table structure changed."""

        with self.update_guard:
            table_signals_blocked = self.table.blockSignals(True)
            try:
                if self.table.rowCount() == len(row_models):
                    for row_index, row_model in enumerate(row_models):
                        for column in self.columns:
                            raw = column.editor.raw_for(column.value_of(row_model))
                            if not column.editor.update(
                                self.table, row_index, column.index, raw
                            ):
                                self._set_cell(row_index, column, raw)
                    return False

                self.table.setRowCount(0)
                for row_model in row_models:
                    self.append(row_model)
                return True
            finally:
                self.table.blockSignals(table_signals_blocked)
                self.update_guard.remember_rows(self.row_values())

    def request_apply_changes(self) -> None:
        """Apply edits unless they are fallout from a programmatic table update."""

        if self.update_guard.active:
            return
        self._sync_item_logical_values_from_edit_role()
        if self.update_guard.pending_release:
            if self.update_guard.should_suppress_pending_rows(self.row_values()):
                return
            self.update_guard.release()
        self.apply_changes()

    def rows(self) -> tuple[EditableRowT, ...]:
        """Return the complete rows; incomplete rows are reported separately."""

        return tuple(
            row
            for row in (self._row_or_none(values) for values in self.row_values())
            if row is not None
        )

    def row_values(self) -> tuple[RawRow, ...]:
        """Return the current raw cell state for every row."""

        return tuple(
            tuple(
                column.editor.raw(self.table, row_index, column.index)
                for column in self.columns
            )
            for row_index in range(self.table.rowCount())
        )

    def incomplete_row_numbers(self) -> tuple[int, ...]:
        """One-based numbers of rows whose cells do not yet form a valid row."""

        return tuple(
            row_index + 1
            for row_index, values in enumerate(self.row_values())
            if self._row_or_none(values) is None
        )

    def has_incomplete_rows(self) -> bool:
        return bool(self.incomplete_row_numbers())

    def _row_or_none(self, raw_row: RawRow) -> EditableRowT | None:
        try:
            return cast(
                EditableRowT,
                self.columns.construct(
                    tuple(
                        column.editor.value_from_raw(raw)
                        for column, raw in zip(self.columns, raw_row, strict=True)
                    )
                ),
            )
        except INVALID_CELL_VALUE_ERRORS:
            return None

    def suppress_current_rows_until_idle(self) -> None:
        """Suppress delayed callbacks for the currently rendered row values."""

        self.update_guard.suppress_pending_rows(self.row_values())

    def _sync_item_logical_values_from_edit_role(self) -> None:
        """Update item backing values for a real table edit without re-emitting."""

        table_signals_blocked = self.table.blockSignals(True)
        try:
            for row_index in range(self.table.rowCount()):
                for column in self.columns:
                    if self.table.cellWidget(row_index, column.index) is not None:
                        continue
                    item = self.table.item(row_index, column.index)
                    if item is None:
                        continue
                    edit_value = item.data(Qt.ItemDataRole.EditRole)
                    if not isinstance(edit_value, str):
                        edit_value = item.text()
                    if item.data(self.LOGICAL_VALUE_ROLE) == edit_value:
                        continue
                    self._set_item_logical_text(item, edit_value)
        finally:
            self.table.blockSignals(table_signals_blocked)

    def remove_selected(self) -> bool:
        selected_rows = {index.row() for index in self.table.selectedIndexes()}
        if not selected_rows:
            return False
        table_signals_blocked = self.table.blockSignals(True)
        try:
            for row_index in sorted(selected_rows, reverse=True):
                self.table.removeRow(row_index)
        finally:
            self.table.blockSignals(table_signals_blocked)
        return True

    def _set_cell(
        self,
        row_index: int,
        column: DataclassFieldColumn,
        raw: object,
    ) -> None:
        column.editor.create(
            self.table,
            row_index,
            column.index,
            raw,
            self.cell_context,
        )
        self._apply_current_placeholder_text_style_to_cell(row_index, column)

    @classmethod
    def _set_item_logical_text(cls, item: EditableTableItem, value: str) -> None:
        cls._editable_item(item)
        item.set_logical_text(value)

    @staticmethod
    def _editable_item(item: QTableWidgetItem) -> EditableTableItem:
        if not isinstance(item, EditableTableItem):
            raise TypeError(
                "Editable table text cells must be EditableTableItem instances "
                f"for semantic chrome isolation, got {type(item).__name__}."
            )
        return item

    def _apply_current_placeholder_text_style_to_cell(
        self,
        row_index: int,
        column: DataclassFieldColumn,
    ) -> None:
        """Apply the table's current inherited-preview style to a newly built cell."""

        active = self.table.property("placeholder_text_style_active") is True
        widget = self.table.cellWidget(row_index, column.index)
        if widget is not None:
            self._apply_widget_placeholder_text_style(widget, active)
            return
        item = self.table.item(row_index, column.index)
        if item is not None:
            self._apply_item_placeholder_text_style(item, active)

    def apply_semantic_index(
        self,
        semantic_index: ObjectStateSubfieldSemanticIndex,
    ) -> None:
        """Apply ObjectState structural semantics to table cell chrome."""

        from objectstate.time_travel_profile import TimeTravelProfiler

        with TimeTravelProfiler.phase(
            "openhcs.editable_table.apply_semantic_index",
            rows=self.table.rowCount(),
            columns=self.table.columnCount(),
        ):
            with self.update_guard:
                table_signals_blocked = self.table.blockSignals(True)
                try:
                    for (
                        row_index,
                        column_index,
                    ), relative_path in self.semantic_paths().items():
                        semantic = semantic_index.leaf_for(relative_path)
                        if semantic is None:
                            continue
                        widget = self.table.cellWidget(row_index, column_index)
                        if widget is not None:
                            self._apply_widget_semantic(widget, semantic)
                            continue
                        item = self.table.item(row_index, column_index)
                        if item is not None:
                            self._apply_item_semantic(item, semantic)
                finally:
                    self.table.blockSignals(table_signals_blocked)
                    self.update_guard.remember_rows(self.row_values())

    def set_placeholder_text_style(self, active: bool) -> None:
        """Apply inherited-preview text styling to every rendered table cell."""

        with self.update_guard:
            self.apply_placeholder_text_style_to_table(self.table, active)
            self.update_guard.remember_rows(self.row_values())

    @classmethod
    def apply_placeholder_text_style_to_table(
        cls,
        table: QTableWidget,
        active: bool,
    ) -> None:
        """Apply or clear placeholder text styling without dimming table controls."""

        table_signals_blocked = table.blockSignals(True)
        try:
            table.setProperty("placeholder_text_style_active", active)
            for row_index in range(table.rowCount()):
                for column_index in range(table.columnCount()):
                    widget = table.cellWidget(row_index, column_index)
                    if widget is not None:
                        cls._apply_widget_placeholder_text_style(widget, active)
                        continue
                    item = table.item(row_index, column_index)
                    if item is not None:
                        cls._apply_item_placeholder_text_style(item, active)
        finally:
            table.blockSignals(table_signals_blocked)

    def semantic_paths(self) -> Mapping[tuple[int, int], StructuralValuePath]:
        """Return structural paths for all currently rendered cells."""

        if self.semantic_binding is None:
            return MappingProxyType({})
        return MappingProxyType(
            {
                (row_index, column.index): self.semantic_binding.relative_path_for_cell(
                    row_index,
                    column.index,
                )
                for row_index in range(self.table.rowCount())
                for column in self.columns
            }
        )

    def cell_target_for_semantic_path(
        self,
        relative_path: StructuralValuePath,
    ) -> StructuralTableCellTarget | None:
        """Return a concrete target for a structural cell path."""

        for (row_index, column_index), candidate in self.semantic_paths().items():
            if candidate != relative_path:
                continue
            return StructuralTableCellTarget(
                table=self.table,
                row_index=row_index,
                column_index=column_index,
                cell_widget=self.table.cellWidget(row_index, column_index),
            )
        return None

    @staticmethod
    def _semantic_tooltip(semantic) -> str:
        reasons: list[str] = [semantic.display_path]
        if semantic.dirty:
            reasons.append("* differs from saved value")
        if semantic.signature_diff:
            reasons.append("_ differs from signature default")
        if semantic.inherited_value:
            reasons.append("inherited resolved value")
        return "\n".join(reasons)

    @classmethod
    def _apply_item_semantic(cls, item: QTableWidgetItem, semantic) -> None:
        item = cls._editable_item(item)
        logical_value = item.data(cls.LOGICAL_VALUE_ROLE)
        if not isinstance(logical_value, str):
            edit_value = item.data(Qt.ItemDataRole.EditRole)
            logical_value = edit_value if isinstance(edit_value, str) else item.text()
            item.setData(cls.LOGICAL_VALUE_ROLE, logical_value)
        target_text = f"{''.join(semantic.semantic_markers)}{logical_value}"
        target_tooltip = cls._semantic_tooltip(semantic)
        font = item.font()
        if (
            item.text() == target_text
            and item.data(Qt.ItemDataRole.EditRole) == logical_value
            and item.data(cls.RENDERED_TEXT_ROLE) == target_text
            and font.underline() == semantic.signature_diff
            and item.toolTip() == target_tooltip
        ):
            return
        item.set_rendered_text(target_text)
        font.setUnderline(semantic.signature_diff)
        item.setFont(font)
        item.setToolTip(target_tooltip)

    @classmethod
    def _apply_widget_semantic(cls, widget: QWidget, semantic) -> None:
        target_tooltip = cls._semantic_tooltip(semantic)
        font = widget.font()
        if isinstance(widget, QComboBox):
            widget_marker_matches = cls._combo_current_marker_matches(
                widget,
                semantic.semantic_markers,
            )
        elif isinstance(widget, StructuredSelectorCellWidget):
            marker_text = "".join(semantic.semantic_markers)
            widget_marker_matches = (
                widget.semantic_marker_label.text() == marker_text
                and widget.semantic_marker_label.isVisible() == bool(marker_text)
            )
        else:
            widget_marker_matches = True
        if (
            widget.property("objectstate_dirty") == semantic.dirty
            and widget.property("objectstate_signature_diff") == semantic.signature_diff
            and widget.property("objectstate_inherited") == semantic.inherited_value
            and widget.toolTip() == target_tooltip
            and font.underline() == semantic.signature_diff
            and widget_marker_matches
        ):
            return
        if isinstance(widget, QComboBox):
            cls._apply_combo_semantic_markers(widget, semantic.semantic_markers)
        elif isinstance(widget, StructuredSelectorCellWidget):
            widget.set_semantic_markers(semantic.semantic_markers)
        widget.setProperty("objectstate_dirty", semantic.dirty)
        widget.setProperty("objectstate_signature_diff", semantic.signature_diff)
        widget.setProperty("objectstate_inherited", semantic.inherited_value)
        widget.setToolTip(target_tooltip)
        font.setUnderline(semantic.signature_diff)
        widget.setFont(font)
        widget.style().unpolish(widget)
        widget.style().polish(widget)
        widget.update()

    @staticmethod
    def _combo_current_marker_matches(
        combo: QComboBox,
        markers: tuple[str, ...],
    ) -> bool:
        rendered_index = combo.currentIndex() if markers else -1
        return (
            combo.property("objectstate_rendered_markers") == markers
            and combo.property("objectstate_rendered_marker_index") == rendered_index
        )

    @classmethod
    def _apply_combo_semantic_markers(
        cls,
        combo: QComboBox,
        markers: tuple[str, ...],
    ) -> None:
        was_blocked = combo.blockSignals(True)
        try:
            cls._restore_combo_item_texts(combo)
            if markers and combo.currentIndex() >= 0:
                current_index = combo.currentIndex()
                combo.setItemText(
                    current_index,
                    f"{''.join(markers)}{cls._combo_logical_text(combo, current_index)}",
                )
                combo.setProperty("objectstate_rendered_marker_index", current_index)
            else:
                combo.setProperty("objectstate_rendered_marker_index", -1)
            combo.setProperty("objectstate_rendered_markers", markers)
        finally:
            combo.blockSignals(was_blocked)

    @classmethod
    def _restore_combo_item_texts(cls, combo: QComboBox) -> None:
        for index in range(combo.count()):
            combo.setItemText(index, cls._combo_logical_text(combo, index))

    @classmethod
    def _combo_logical_text(cls, combo: QComboBox, index: int) -> str:
        logical_text = combo.itemData(index, cls.COMBO_LOGICAL_TEXT_ROLE)
        if not isinstance(logical_text, str):
            raise TypeError("Editable table choice cells require logical text data.")
        return logical_text

    @classmethod
    def _apply_item_placeholder_text_style(
        cls,
        item: QTableWidgetItem,
        active: bool,
    ) -> None:
        font = item.font()
        font.setItalic(active)
        item.setFont(font)
        item.setForeground(
            QBrush(QColor(PlaceholderConfig.text_color_name())) if active else QBrush()
        )

    @classmethod
    def _apply_widget_placeholder_text_style(
        cls,
        widget: QWidget,
        active: bool,
    ) -> None:
        if isinstance(widget, StructuredSelectorCellWidget):
            cls._apply_line_edit_placeholder_text_style(widget.line_edit, active)
            return
        if isinstance(widget, QLineEdit):
            cls._apply_line_edit_placeholder_text_style(widget, active)
            return
        if isinstance(widget, QComboBox):
            widget.setStyleSheet(
                f"QComboBox {{ {PlaceholderConfig.text_style(include_opacity=False)} }}"
                if active
                else ""
            )

    @staticmethod
    def _apply_line_edit_placeholder_text_style(
        line_edit: QLineEdit,
        active: bool,
    ) -> None:
        line_edit.setStyleSheet(
            f"QLineEdit {{ {PlaceholderConfig.text_style(include_opacity=False)} }}"
            if active
            else ""
        )


class EditableTableLayout:
    """Shared layout policy for compact source-binding tables."""

    @staticmethod
    def configure(table: QTableWidget) -> None:
        table.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        table.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        table.setSizePolicy(
            QSizePolicy.Policy.Expanding,
            QSizePolicy.Policy.Fixed,
        )
        table.verticalHeader().setVisible(False)
        table.verticalHeader().setDefaultSectionSize(22)
        table.verticalHeader().setMinimumSectionSize(18)
        table.horizontalHeader().setSectionResizeMode(
            QHeaderView.ResizeMode.ResizeToContents
        )
        table.verticalHeader().setSectionResizeMode(
            QHeaderView.ResizeMode.ResizeToContents
        )

    @staticmethod
    def fit_to_rows(table: QTableWidget) -> None:
        table.ensurePolished()
        table.resizeRowsToContents()
        header = table.horizontalHeader()
        header_height = max(header.height(), header.sizeHint().height())
        row_height = sum(table.rowHeight(row) for row in range(table.rowCount()))
        if table.rowCount() == 0:
            row_height = table.verticalHeader().defaultSectionSize()
        scrollbar_height = table.horizontalScrollBar().sizeHint().height()
        frame = table.frameWidth() * 2
        viewport_vertical_margin = 2 * table.style().pixelMetric(
            QStyle.PixelMetric.PM_FocusFrameVMargin,
            None,
            table,
        )
        table.viewport().setMinimumHeight(row_height)
        table.setFixedHeight(
            header_height
            + row_height
            + scrollbar_height
            + frame
            + viewport_vertical_margin
        )


# --- Source-binding tables ---------------------------------------------------


@dataclass(frozen=True, slots=True)
class SourceSetPairingRow:
    """One row of the source-set pairing table: a match method and one shared key."""

    method: Annotated[SourceBindingMatchMethod, FieldLabel("Pairing Method")]
    """How selected aliases are grouped into one source set: by source order, or by declared metadata keys."""

    fields: Annotated[
        tuple[SourceBindingMatchField, ...], FieldLabel("Pairing Keys")
    ] = ()
    """Alias-to-metadata-field pairs forming one shared source-set key when the method is metadata."""

    @classmethod
    def from_plan(
        cls,
        plan: SourceBindingMatchPlan | None,
    ) -> tuple["SourceSetPairingRow", ...]:
        if plan is None:
            return ()
        if not plan.dimensions:
            return (cls(method=plan.method),)
        return tuple(
            cls(method=plan.method, fields=dimension.fields)
            for dimension in plan.dimensions
        )

    @staticmethod
    def to_plan(
        rows: tuple["SourceSetPairingRow", ...],
    ) -> SourceBindingMatchPlan | None:
        if not rows:
            return None
        return SourceBindingMatchPlan(
            method=rows[0].method,
            dimensions=tuple(
                SourceBindingMatchDimension(fields=row.fields)
                for row in rows
                if row.fields
            ),
        )


def source_binding_suggestions(
    *,
    source_bindings: SourceBindingsConfig,
    inventory: SourceInventory | None,
) -> RowSuggestionMap:
    """Picker suggestions per record type, from field choices, config and inventory."""

    metadata_fields: set[str] = set(source_bindings.grouping_metadata_fields)
    for rule in source_bindings.metadata_rule_declarations:
        metadata_fields.update(re.compile(rule.pattern).groupindex)
    inventory_metadata: set[tuple[str, str]] = set()
    if inventory is not None:
        for candidate in inventory.candidates:
            metadata_fields.update(candidate.metadata)
            inventory_metadata.update(
                (name, str(value)) for name, value in candidate.metadata.items()
            )
    sorted_fields = tuple(sorted(metadata_fields))
    component_choices = DataclassFieldColumns.of(ComponentSelector).named("component")
    filter_columns = DataclassFieldColumns.of(SourceFilterClause)
    return MappingProxyType(
        {
            ComponentSelector: tuple(
                RowSuggestion.of(ComponentSelector, component=component)
                for component in cast(
                    ChoiceCellEditor, component_choices.editor
                ).choices
            ),
            MetadataSelector: tuple(
                RowSuggestion.of(MetadataSelector, field=name) for name in sorted_fields
            )
            + tuple(
                RowSuggestion.of(MetadataSelector, field=name, value=value)
                for name, value in sorted(inventory_metadata)
            ),
            SourceFilterClause: tuple(
                RowSuggestion.of(
                    SourceFilterClause,
                    subject=subject,
                    match_type=match_type,
                )
                for subject in cast(
                    ChoiceCellEditor, filter_columns.named("subject").editor
                ).choices
                for match_type in cast(
                    ChoiceCellEditor, filter_columns.named("match_type").editor
                ).choices
            ),
            SourceBindingMatchField: tuple(
                RowSuggestion.of(
                    SourceBindingMatchField,
                    alias=alias,
                    metadata_field=name,
                )
                for alias in sorted(
                    binding.alias for binding in source_bindings.binding_declarations
                )
                for name in sorted_fields
            ),
        }
    )


class StepBindingsTableEditor(QWidget):
    """Transposed table over typed ``NamedSourceBinding`` values.

    Each binding is one table column and each derived binding field one table
    row. An edit replaces exactly the edited field of the stored binding, so
    fields without a row (``explicit_source``, ``source_channel_counts``) are kept.
    """

    changed = pyqtSignal()

    def __init__(
        self,
        *,
        bindings: tuple[NamedSourceBinding, ...],
        suggestions: RowSuggestionMap,
        scope_color_scheme: object | None = None,
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self._updating_ui = False
        self.columns = DataclassFieldColumns.of(NamedSourceBinding)
        self.cell_context = CellEditContext(
            on_change=self._request_apply_changes,
            suggestions=suggestions,
        )
        self._bindings: list[NamedSourceBinding] = []
        self.table = ScopedTableWidget(len(self.columns), 0, self)
        self.table.set_scope_color_scheme(scope_color_scheme)
        self.table.setVerticalHeaderLabels(self.columns.labels)
        self.columns.apply_header_items(self.table.verticalHeaderItem)
        self._updating_ui = True
        try:
            for binding in bindings:
                self._append_column(binding)
        finally:
            self._updating_ui = False
        self.table.itemChanged.connect(lambda _: self._request_apply_changes())
        self._configure_table()
        self._sync_header_labels()
        self._fit_table()

        buttons = QHBoxLayout()
        add_button = QPushButton("Add binding", self)
        add_button.clicked.connect(lambda: self.add_binding_row())
        remove_button = QPushButton("Remove selected", self)
        remove_button.clicked.connect(self.remove_selected_binding_rows)
        buttons.addWidget(add_button)
        buttons.addWidget(remove_button)
        buttons.addStretch(1)

        layout = QVBoxLayout(self)
        layout.addWidget(self.table)
        layout.addLayout(buttons)

    def add_binding_row(self, binding: NamedSourceBinding | None = None) -> None:
        self._updating_ui = True
        try:
            self._append_column(binding or NamedSourceBinding(alias="NewSource"))
        finally:
            self._updating_ui = False
        self._sync_header_labels()
        self._fit_table()
        self.changed.emit()

    def remove_selected_binding_rows(self) -> None:
        selected_columns = {index.column() for index in self.table.selectedIndexes()}
        if not selected_columns:
            return
        table_signals_blocked = self.table.blockSignals(True)
        try:
            for binding_index in sorted(selected_columns, reverse=True):
                self.table.removeColumn(binding_index)
                del self._bindings[binding_index]
        finally:
            self.table.blockSignals(table_signals_blocked)
        self._sync_header_labels()
        self._fit_table()
        self.changed.emit()

    def bindings(self) -> tuple[NamedSourceBinding, ...]:
        return tuple(self._bindings)

    def cell_position(
        self,
        binding_index: int,
        *path: str,
    ) -> tuple[int, int]:
        """Table (row, column) of one binding field."""

        return self.columns.named(*path).index, binding_index

    def _append_column(self, binding: NamedSourceBinding) -> None:
        binding_index = self.table.columnCount()
        self.table.insertColumn(binding_index)
        self._bindings.append(binding)
        for column in self.columns:
            column.editor.create(
                self.table,
                column.index,
                binding_index,
                column.editor.raw_for(column.value_of(binding)),
                self.cell_context,
            )

    def _request_apply_changes(self) -> None:
        if self._updating_ui:
            return
        self._apply_cell_edits()
        self._sync_header_labels()
        self.changed.emit()

    def _apply_cell_edits(self) -> None:
        """Replace each binding field whose cell holds a new, valid value.

        Passes repeat until nothing applies, so an edit that is only valid
        together with another pending edit (e.g. a non-image kind and a
        source-artifact projection) lands once both cells are set.
        """

        for binding_index, binding in enumerate(self._bindings):
            applied = True
            while applied:
                applied = False
                for column in self.columns:
                    try:
                        value = column.editor.value_from_raw(
                            column.editor.raw(self.table, column.index, binding_index)
                        )
                        if value == column.value_of(binding):
                            continue
                        binding = cast(
                            NamedSourceBinding, column.replaced(binding, value)
                        )
                        applied = True
                    except INVALID_CELL_VALUE_ERRORS:
                        continue
            self._bindings[binding_index] = binding

    def _sync_header_labels(self) -> None:
        for binding_index, binding in enumerate(self._bindings):
            item = QTableWidgetItem(binding.alias)
            item.setToolTip(binding.alias)
            self.table.setHorizontalHeaderItem(binding_index, item)

    def _configure_table(self) -> None:
        EditableTableLayout.configure(self.table)
        self.table.setSelectionBehavior(
            QAbstractItemView.SelectionBehavior.SelectColumns
        )
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.table.verticalHeader().setVisible(True)

    def _fit_table(self) -> None:
        EditableTableLayout.fit_to_rows(self.table)


class StepBindingsDialog(QDialog):
    """Modal editor for the large step-bindings table."""

    def __init__(
        self,
        *,
        bindings: tuple[NamedSourceBinding, ...],
        suggestions: RowSuggestionMap,
        scope_color_scheme: object | None = None,
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self.setWindowTitle("Edit step source bindings")
        self.editor = StepBindingsTableEditor(
            bindings=bindings,
            suggestions=suggestions,
            scope_color_scheme=scope_color_scheme,
            parent=self,
        )
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel,
            self,
        )
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)

        layout = QVBoxLayout(self)
        layout.addWidget(self.editor)
        layout.addWidget(buttons)
        self.resize(820, 560)

    def bindings(self) -> tuple[NamedSourceBinding, ...]:
        return self.editor.bindings()


@dataclass(frozen=True, slots=True)
class SourceBindingsEditorValue:
    """Validated editor bridge between raw lazy configs and concrete source-binding views."""

    raw: SourceBindingsEditorRawValue

    def __post_init__(self) -> None:
        self.base_type()

    def base_type(self) -> type[SourceBindingsConfig]:
        value_type = type(self.raw)
        base_type = get_base_type_for_lazy(value_type) or value_type
        if not issubclass(base_type, SourceBindingsConfig):
            raise TypeError(
                "SourceBindingsEditorWidget requires SourceBindingsConfig, "
                f"got {value_type.__name__}."
            )
        return base_type

    def raw_field_value(self, field_name: str) -> object:
        """Return one source-binding field without triggering lazy resolution."""

        return DataclassFieldAccess.raw_value(self.raw, field_name)

    @property
    def is_enableable(self) -> bool:
        return is_enableable(self.base_type())

    @property
    def enabled_value(self) -> bool | None:
        if not self.is_enableable:
            return None
        return cast(
            bool | None,
            self.raw_field_value(Enableable.require_parameter_name()),
        )

    @property
    def source_filter_declarations(self) -> tuple[SourceFilterClause, ...]:
        return tuple(self.raw_field_value("source_filters") or ())

    @property
    def binding_declarations(self) -> tuple[NamedSourceBinding, ...]:
        return tuple(self.raw_field_value("bindings") or ())

    @property
    def metadata_rule_declarations(self) -> tuple[MetadataExtractionRule, ...]:
        return tuple(self.raw_field_value("metadata_rules") or ())

    @property
    def match_plan(self) -> SourceBindingMatchPlan | None:
        return cast(
            SourceBindingMatchPlan | None,
            self.raw_field_value("match_plan"),
        )

    def concrete_view(self) -> SourceBindingsConfig:
        if isinstance(self.raw, SourceBindingsConfig):
            return self.raw
        config_type = self.base_type()
        concrete = resolve_lazy_configurations_for_serialization(self.raw)
        if not isinstance(concrete, config_type):
            raise TypeError(
                "Lazy source-binding resolution returned "
                f"{type(concrete).__name__}, expected {config_type.__name__}."
            )
        return concrete

    def view_inputs(
        self,
        pipeline_source_bindings: SourceBindingsConfig,
    ) -> tuple[SourceBindingsConfig, StepSourceBindingsConfig]:
        """Return nominal pipeline and step values rendered by the editor."""
        concrete = self.concrete_view()
        if isinstance(concrete, StepSourceBindingsConfig):
            return pipeline_source_bindings, concrete
        return concrete, EMPTY_SOURCE_BINDINGS


class SourceBindingsEditorWidget(
    QWidget,
    ValueGettable,
    ValueSettable,
    ResolvedValuePreviewSettable,
    RawResolvedValueSettable,
    ChildFieldChromeRefreshable,
    ChildFieldIdentityProvider,
    ChildFieldNavigationTargetProvider,
    ChildFieldSemanticChromeRefreshable,
    ChildSubfieldNavigationTargetProvider,
    InlineDataclassGroupBoxChromeProvider,
    InlineDataclassRootResettable,
    ChangeSignalEmitter,
    ScopeColorSchemeReceiver,
    metaclass=PyQtWidgetMeta,
):
    """Inline form widget for typed source-binding semantics."""

    changed = pyqtSignal()

    def __init__(
        self,
        *,
        source_bindings: SourceBindingsConfig = SourceBindingsConfig(),
        bindings: SourceBindingsEditorRawValue | None = None,
        display_bindings: SourceBindingsEditorRawValue | None = None,
        inventory: SourceInventory | None = None,
        form_context: InlineDataclassFormContext | None = None,
        parent: QWidget | None = None,
    ) -> None:
        super().__init__(parent)
        self._source_bindings = source_bindings
        self._bindings = bindings if bindings is not None else EMPTY_SOURCE_BINDINGS
        self._display_bindings = (
            display_bindings if display_bindings is not None else self._bindings
        )
        self._inventory = inventory
        self._form_context = form_context
        self._child_chrome = (
            InlineDataclassChildChrome(form_context)
            if form_context is not None
            else None
        )
        self._change_signal_callbacks: dict[
            Callable[[SourceBindingsEditorRawValue], None],
            Callable[[], None],
        ] = {}
        self._updating_ui = False
        self.step_bindings_summary_table: QTableWidget | None = None
        self.step_bindings_table: QTableWidget | None = None
        self.step_bindings_editor: StepBindingsTableEditor | None = None
        self.source_filters_table: QTableWidget | None = None
        self.metadata_rules_table: QTableWidget | None = None
        self.match_plan_table: QTableWidget | None = None
        self._inline_groupbox: object | None = None
        self._enabled_checkbox: NoneAwareCheckBox | None = None
        self._enabled_title_widget: QWidget | None = None
        self._enabled_reset_button: QPushButton | None = None
        self._enabled_provenance_button: QWidget | None = None
        self._updating_enableable_chrome = False
        self.source_filters_controller: (
            EditableTableController[SourceFilterClause] | None
        ) = None
        self.metadata_rules_controller: (
            EditableTableController[MetadataExtractionRule] | None
        ) = None
        self.match_plan_controller: (
            EditableTableController[SourceSetPairingRow] | None
        ) = None
        self._editable_table_controllers: list[EditableTableController] = []
        self._structural_table_controllers: list[EditableTableController] = []
        self._table_placeholder_chrome_state: dict[str, bool] = {}
        self._scope_color_scheme = None
        self.layout = QVBoxLayout(self)
        self.layout.setContentsMargins(0, 0, 0, 0)
        self.layout.setSpacing(3)
        self.refresh()

    @classmethod
    def from_bindings(
        cls,
        bindings: SourceBindingsEditorRawValue,
        *,
        display_bindings: SourceBindingsEditorRawValue | None = None,
        source_bindings: SourceBindingsConfig = SourceBindingsConfig(),
        inventory: SourceInventory | None = None,
        form_context: InlineDataclassFormContext | None = None,
        parent: QWidget | None = None,
    ) -> "SourceBindingsEditorWidget":
        """Create an editor from typed source bindings and pipeline defaults."""

        return cls(
            source_bindings=source_bindings,
            bindings=bindings,
            display_bindings=display_bindings,
            inventory=inventory,
            form_context=form_context,
            parent=parent,
        )

    @property
    def value(self) -> SourceBindingsEditorRawValue:
        """Value property used by pyqt-reactive signal adapters."""

        return self.get_value()

    def get_value(self) -> SourceBindingsEditorRawValue:
        """Return the current typed source-bindings config."""

        return self._bindings

    def resolved_view_inputs(
        self,
        source_bindings: SourceBindingsConfig | None = None,
    ) -> tuple[SourceBindingsConfig, StepSourceBindingsConfig]:
        """Return the concrete values currently rendered by this editor."""
        return SourceBindingsEditorValue(self._display_bindings).view_inputs(
            self._source_bindings if source_bindings is None else source_bindings
        )

    def set_value(self, value: SourceBindingsEditorRawValue | None) -> None:
        """Update the widget from a typed source-bindings config."""

        from objectstate.time_travel_profile import TimeTravelProfiler

        bindings = value if value is not None else type(self._bindings)()
        SourceBindingsEditorValue(bindings)
        with TimeTravelProfiler.phase(
            "openhcs.source_bindings.set_value",
            widget=type(self).__qualname__,
        ):
            if bindings == self._bindings:
                if bindings != self._display_bindings:
                    if self._rendered_bindings_equal(bindings, self._display_bindings):
                        self._display_bindings = bindings
                        self.refresh_child_field_chrome()
                        return
                    self._display_bindings = bindings
                    self.refresh()
                    return
                self.refresh_child_field_chrome()
                return
            if self._refresh_enableable_only(bindings, bindings):
                return
            if self._refresh_source_filters_only(bindings):
                return
            self._bindings = bindings
            self._display_bindings = bindings
            self.refresh()

    def set_resolved_value_preview(self, value: SourceBindingsEditorRawValue) -> None:
        """Update inherited/resolved display without changing the raw edit value."""

        SourceBindingsEditorValue(value)
        if value == self._display_bindings:
            self.refresh_child_field_chrome()
            return
        if self._rendered_bindings_equal(value, self._display_bindings):
            self._display_bindings = value
            self.refresh_child_field_chrome()
            return
        if self._refresh_enableable_only(self._bindings, value):
            return
        if self._refresh_source_filters_only(value, update_raw=False):
            return
        self._display_bindings = value
        self.refresh()

    def set_raw_value_with_resolved_preview(
        self,
        raw_value: SourceBindingsEditorRawValue | None,
        resolved_value: SourceBindingsEditorRawValue | None,
    ) -> None:
        """Update raw edit value and resolved display in one render pass."""

        raw_bindings = raw_value if raw_value is not None else type(self._bindings)()
        display_bindings = (
            resolved_value if resolved_value is not None else raw_bindings
        )
        SourceBindingsEditorValue(raw_bindings)
        SourceBindingsEditorValue(display_bindings)

        if (
            raw_bindings == self._bindings
            and display_bindings == self._display_bindings
        ):
            return

        if self._refresh_enableable_only(raw_bindings, display_bindings):
            return

        if self._refresh_source_filters_only(
            display_bindings,
            raw_bindings=raw_bindings,
            refresh_chrome=False,
        ):
            return

        self._bindings = raw_bindings
        self._display_bindings = display_bindings
        self.refresh()

    def refresh_child_field_chrome(
        self,
        owner_field_paths: tuple[DottedFieldPath, ...] | None = None,
    ) -> None:
        """Refresh child labels and reset buttons after ObjectState changes."""

        self.refresh_section_label_markers(owner_field_paths)

    def reset_inline_dataclass_fields(self) -> None:
        """Reset SourceBindings child fields through the inline form context."""

        if self._form_context is None:
            raise RuntimeError(
                "SourceBindingsEditorWidget requires an InlineDataclassFormContext "
                "for root reset-all behavior."
            )
        self._form_context.reset_children()

    def child_field_semantic_owner_paths(self) -> tuple[DottedFieldPath, ...]:
        """Return SourceBindings child fields with structural table semantics."""

        if self._form_context is None:
            return ()
        return tuple(
            self._form_context.child_path(binding.owner_field_name)
            for binding in self._structural_table_bindings()
        )

    def refresh_child_field_semantics(
        self,
        owner_field_path: DottedFieldPath,
        semantic_index: ObjectStateSubfieldSemanticIndex,
    ) -> None:
        """Apply ObjectState-derived child structural semantics."""

        if self._form_context is None:
            return
        for controller, binding in self._structural_table_controller_bindings():
            if owner_field_path != self._form_context.child_path(
                binding.owner_field_name
            ):
                continue
            controller.apply_semantic_index(semantic_index)
            return

    def _refresh_source_filters_only(
        self,
        bindings: SourceBindingsEditorRawValue,
        *,
        update_raw: bool = True,
        raw_bindings: SourceBindingsEditorRawValue | None = None,
        refresh_chrome: bool = True,
    ) -> bool:
        """Update the source-filter table without rebuilding sibling sections."""

        from objectstate.time_travel_profile import TimeTravelProfiler

        if self.source_filters_table is None or self.source_filters_controller is None:
            return False

        with TimeTravelProfiler.phase(
            "openhcs.source_bindings.refresh_source_filters_only",
            update_raw=update_raw,
        ):
            current = SourceBindingsEditorValue(self._display_bindings)
            incoming = SourceBindingsEditorValue(bindings)
            if (
                current.source_filter_declarations
                == incoming.source_filter_declarations
            ):
                return False
            if (
                current.binding_declarations != incoming.binding_declarations
                or current.metadata_rule_declarations
                != incoming.metadata_rule_declarations
                or current.match_plan != incoming.match_plan
            ):
                return False

            if update_raw:
                self._bindings = raw_bindings if raw_bindings is not None else bindings
            self._display_bindings = bindings
            self._updating_ui = True
            try:
                structure_changed = self.source_filters_controller.replace_all(
                    incoming.source_filter_declarations
                )
            finally:
                self._updating_ui = False
            if structure_changed:
                self._fit_table_to_rows(self.source_filters_table)
            if refresh_chrome:
                self._refresh_single_child_field_chrome("source_filters")
            return True

    def _refresh_enableable_only(
        self,
        raw_bindings: SourceBindingsEditorRawValue,
        display_bindings: SourceBindingsEditorRawValue,
    ) -> bool:
        """Update enableable chrome without rebuilding source-binding tables."""

        if not is_enableable(SourceBindingsEditorValue(raw_bindings).base_type()):
            return False
        if not self._rendered_sections_equal(display_bindings, self._display_bindings):
            return False

        self._bindings = raw_bindings
        self._display_bindings = display_bindings
        self._sync_enableable_chrome()
        self._refresh_single_child_field_chrome(self._enabled_field_name())
        return True

    def _refresh_single_child_field_chrome(self, field_name: str) -> None:
        """Refresh child chrome for one source-binding field."""

        if self._form_context is None:
            self.refresh_child_field_chrome()
            return
        self.refresh_child_field_chrome(
            (self._form_context.child_path(field_name),),
        )

    def _rendered_bindings_equal(
        self,
        left: SourceBindingsEditorRawValue,
        right: SourceBindingsEditorRawValue,
    ) -> bool:
        """Return whether two configs render the same source-binding editor rows."""

        return self._rendered_sections_equal(
            left,
            right,
        ) and (
            SourceBindingsEditorValue(left).enabled_value
            == SourceBindingsEditorValue(right).enabled_value
        )

    def _rendered_sections_equal(
        self,
        left: SourceBindingsEditorRawValue,
        right: SourceBindingsEditorRawValue,
    ) -> bool:
        """Return whether two configs render the same non-enableable sections."""

        left_value = SourceBindingsEditorValue(left)
        right_value = SourceBindingsEditorValue(right)
        return (
            left_value.binding_declarations == right_value.binding_declarations
            and left_value.source_filter_declarations
            == right_value.source_filter_declarations
            and left_value.metadata_rule_declarations
            == right_value.metadata_rule_declarations
            and left_value.match_plan == right_value.match_plan
        )

    def child_field_navigation_target(self, field_name: str) -> QWidget | None:
        """Return the rendered section widget for a source-binding child field."""

        if self._form_context is None:
            return None
        if self._child_chrome is None:
            return None
        return self._child_chrome.navigation_target(field_name)

    def child_subfield_navigation_target(
        self,
        child_identity: InlineDataclassChildFieldIdentity,
        relative_path: StructuralValuePath,
    ) -> StructuralFlashTarget | None:
        """Return the rendered target for one structural child cell."""

        if self._form_context is None:
            return None
        if (
            child_identity.field_name == self._enabled_field_name()
            and not relative_path.segments
        ):
            return self._enabled_structural_target()
        section_group = self.child_field_navigation_target(child_identity.field_name)
        if section_group is None:
            return None
        if not relative_path.segments:
            label_widget = self.child_field_label(child_identity.field_name)
            return StructuralMaskedContainerTarget(
                container=self,
                masked_target=StructuralDescendantMaskTarget(section_group),
                label_widget=label_widget,
                scroll_target=StructuralWidgetTarget(label_widget),
            )
        controller = self._structural_table_controller_for_field(
            child_identity.field_name
        )
        if controller is None:
            return None
        cell_target = controller.cell_target_for_semantic_path(relative_path)
        if cell_target is None:
            return None
        return StructuralMaskedContainerTarget(
            container=section_group,
            masked_target=cell_target,
            label_widget=self.child_field_label(child_identity.field_name),
        )

    def child_field_identity(
        self, field_name: str
    ) -> InlineDataclassChildFieldIdentity:
        """Return the nominal ObjectState identity for one source-binding child."""

        if self._child_chrome is None:
            raise RuntimeError("Source binding child identity requires form context.")
        return self._child_chrome.child_identity(field_name)

    def child_field_label(self, field_name: str):
        """Return the rendered label for one source-binding child field."""

        if self._child_chrome is None:
            raise RuntimeError("Source binding child label requires form context.")
        return self._child_chrome.labels[self.child_field_identity(field_name)]

    def child_field_reset_button(self, field_name: str) -> QPushButton:
        """Return the rendered reset button for one source-binding child field."""

        if self._child_chrome is None:
            raise RuntimeError(
                "Source binding child reset button requires form context."
            )
        return self._child_chrome.reset_buttons[self.child_field_identity(field_name)]

    def child_field_section_group(self, field_name: str) -> QWidget:
        """Return the rendered section group for one source-binding child field."""

        target = self.child_field_navigation_target(field_name)
        if target is None:
            raise RuntimeError(
                f"Source binding child section {field_name!r} is not rendered."
            )
        return target

    def _enabled_structural_target(self) -> StructuralFlashTarget | None:
        """Return the structural target for inline enableable title chrome."""

        if not isinstance(self._inline_groupbox, InlineDataclassGroupBox):
            return None
        if self._enabled_checkbox is None:
            return None
        return EnabledTitleWidgetMoveAuthority.title_field_flash_target(
            container=self._inline_groupbox,
            title_widget=self._enabled_title_widget or self._enabled_checkbox,
            checkbox_widget=self._enabled_checkbox,
            reset_button=self._enabled_reset_button,
            provenance_button=self._enabled_provenance_button,
        )

    def set_preview_context(
        self,
        *,
        source_bindings: SourceBindingsConfig,
        inventory: SourceInventory | None = None,
    ) -> None:
        """Set pipeline source config and optional inventory for preview."""

        self._source_bindings = source_bindings
        self._inventory = inventory
        self.refresh()

    def refresh(self) -> None:
        """Rebuild the rendered view from current bindings and preview context."""

        source_bindings, step_bindings = self.resolved_view_inputs()
        binding_columns = DataclassFieldColumns.of(NamedSourceBinding)
        self._updating_ui = True
        self.clear()
        self.layout.addWidget(
            self._table_group(
                "Pipeline Sources",
                ("Field", "Value"),
                (
                    (
                        "image-plane sources",
                        str(len(source_bindings.image_plane_sources)),
                    ),
                    (
                        "imported metadata tables",
                        str(len(source_bindings.imported_metadata_tables)),
                    ),
                ),
            ),
        )
        self.layout.addWidget(
            self._table_group(
                "Pipeline Bindings",
                tuple(
                    binding_columns.named(name).label
                    for name in ("alias", "artifact_kind", "origin")
                ),
                tuple(
                    tuple(
                        binding_columns.named(name).editor.display(
                            getattr(binding, name)
                        )
                        for name in ("alias", "artifact_kind", "origin")
                    )
                    for binding in source_bindings.binding_declarations
                ),
            ),
        )
        self.layout.addWidget(self._step_bindings_group(step_bindings))
        self.layout.addWidget(self._source_filters_group())
        self.layout.addWidget(self._metadata_rules_group())
        self.layout.addWidget(self._match_plan_group())
        pairing_columns = DataclassFieldColumns.of(SourceSetPairingRow)
        self.layout.addWidget(
            self._table_group(
                "Resolved Source Set Pairing",
                ("Scope", "Method", "Dimensions"),
                tuple(
                    (
                        scope,
                        pairing_columns.named("method").editor.display(plan.method),
                        str(len(plan.dimensions)),
                    )
                    for scope, plan in (
                        ("pipeline", source_bindings.match_plan),
                        ("step", step_bindings.match_plan),
                    )
                    if plan is not None
                ),
            )
        )
        if self._inventory is not None:
            preview = SourceBindingsPreview.from_config_and_step_bindings(
                source_bindings=source_bindings,
                step_bindings=step_bindings,
                inventory=self._inventory,
            )
            if preview.diagnostics:
                self.layout.addWidget(
                    self._table_group(
                        "Diagnostics",
                        ("Severity", "Code", "Alias", "Message"),
                        tuple(
                            (
                                diagnostic.severity.value,
                                diagnostic.code,
                                diagnostic.alias or "",
                                diagnostic.message,
                            )
                            for diagnostic in preview.diagnostics
                        ),
                    )
                )
            self.layout.addWidget(
                self._table_group(
                    "Preview Matches",
                    ("Alias", "Scope", "Matched", "Samples"),
                    tuple(
                        (
                            row.alias,
                            row.declaration_scope,
                            str(row.matched_source_count),
                            ", ".join(row.sample_paths),
                        )
                        for row in preview.binding_rows
                    ),
                )
            )
            self.layout.addWidget(
                self._table_group(
                    "Source Sets",
                    ("Index", "Aliases", "Metadata"),
                    tuple(
                        (
                            str(row.index),
                            ", ".join(
                                f"{alias}:{path}" for alias, path in row.paths_by_alias
                            ),
                            ", ".join(
                                f"{field}={value}" for field, value in row.metadata
                            ),
                        )
                        for row in preview.source_set_rows
                    ),
                )
            )
        self.layout.addStretch(1)
        self.refresh_section_label_markers()
        for controller in self._editable_table_controllers:
            controller.suppress_current_rows_until_idle()
        self._updating_ui = False

    def connect_change_signal(
        self, callback: Callable[[SourceBindingsEditorRawValue], None]
    ) -> None:
        """Implement ChangeSignalEmitter for pyqt-reactive inline dataclass forms."""

        def delegated_callback() -> None:
            callback(self.get_value())

        self._change_signal_callbacks[callback] = delegated_callback
        self.changed.connect(delegated_callback)

    def disconnect_change_signal(
        self, callback: Callable[[SourceBindingsEditorRawValue], None]
    ) -> None:
        """Disconnect a previously registered change callback."""

        delegated_callback = self._change_signal_callbacks.pop(callback, None)
        if delegated_callback is None:
            return
        try:
            self.changed.disconnect(delegated_callback)
        except TypeError:
            pass

    def set_scope_color_scheme(self, scheme) -> None:
        """Apply scope styling to every source-binding table."""

        self._scope_color_scheme = scheme
        for table in self.findChildren(ScopedTableWidget):
            table.set_scope_color_scheme(scheme)
            self._fit_table_to_rows(table)

    def configure_inline_dataclass_groupbox(
        self,
        groupbox: InlineDataclassGroupBox,
    ) -> None:
        """Attach source-binding enableable chrome to the inline groupbox title."""

        self._inline_groupbox = groupbox
        if not self._config_type_is_enableable():
            return
        if self._enabled_checkbox is not None:
            return

        enableable_title_authority = EnabledTitleWidgetMoveAuthority()
        checkbox = NoneAwareCheckBox(groupbox)
        checkbox.setToolTip("Enable step source bindings")
        checkbox.toggled.connect(self._on_enabled_checkbox_toggled)
        title_widget = enableable_title_authority.wrap_checkbox_widget_for_title(
            checkbox,
            groupbox.color_scheme,
        )
        enableable_title_authority.bind_title_label_to_checkbox(groupbox, checkbox)

        reset_button = QPushButton("Reset", groupbox)
        reset_button.setToolTip("Reset enabled to default")
        enableable_title_authority.prepare_title_reset_button(
            reset_button,
            groupbox.color_scheme,
        )
        reset_button.clicked.connect(self._reset_enabled_field)

        provenance_button = None
        if self._form_context is not None:
            provenance_button = (
                enableable_title_authority.create_title_provenance_button(
                    state=self._form_context.state,
                    dotted_path=self._form_context.child_path(
                        self._enabled_field_name()
                    ).value,
                    color_scheme=groupbox.color_scheme,
                )
            )

        self._enabled_checkbox = checkbox
        self._enabled_title_widget = title_widget
        self._enabled_reset_button = reset_button
        self._enabled_provenance_button = provenance_button
        groupbox.addEnableableWidgets(title_widget, reset_button, provenance_button)
        self._sync_enableable_chrome()

    def _config_type_is_enableable(self) -> bool:
        return is_enableable(SourceBindingsEditorValue(self._bindings).base_type())

    def _enabled_field_name(self) -> str:
        return Enableable.require_parameter_name()

    def _enabled_value(
        self,
        value: SourceBindingsEditorRawValue,
    ) -> bool | None:
        if not is_enableable(value):
            raise TypeError(
                f"{type(value).__name__} is not an Enableable source-binding config."
            )
        enabled = cast(Enableable, value).enabled
        return None if enabled is None else bool(enabled)

    def _sync_enableable_chrome(self) -> None:
        if not self._config_type_is_enableable():
            InlineDataclassChildChrome.set_widget_dimmed(self, False)
            return

        effective_enabled = bool(self._enabled_value(self._display_bindings))
        raw_enabled = self._enabled_value(self._bindings)
        if self._enabled_checkbox is not None:
            self._updating_enableable_chrome = True
            try:
                if raw_enabled is None:
                    self._enabled_checkbox.set_value(None)
                    self._enabled_checkbox.set_placeholder_preview(effective_enabled)
                else:
                    self._enabled_checkbox.set_value(raw_enabled)
            finally:
                self._updating_enableable_chrome = False
        if self._enabled_reset_button is not None and self._form_context is not None:
            self._form_context.update_reset_button_styling(
                self._enabled_reset_button,
                self._enabled_field_name(),
            )
        InlineDataclassChildChrome.set_widget_dimmed(self, not effective_enabled, 0.4)

    def _on_enabled_checkbox_toggled(self, checked: bool) -> None:
        if self._updating_enableable_chrome:
            return
        self._set_enabled_value(bool(checked))

    def _set_enabled_value(self, enabled: bool) -> None:
        field_name = self._enabled_field_name()
        self._bindings = replace_raw(self._bindings, **{field_name: enabled})
        self._display_bindings = replace_raw(
            self._display_bindings,
            **{field_name: enabled},
        )
        self._sync_enableable_chrome()
        self.changed.emit()

    def _reset_enabled_field(self) -> None:
        field_name = self._enabled_field_name()
        if self._form_context is not None:
            self._form_context.reset_child(field_name)
            return
        default_value = cast(
            Enableable,
            SourceBindingsEditorValue(self._bindings).base_type()(),
        ).enabled
        self._bindings = replace_raw(self._bindings, **{field_name: default_value})
        self._display_bindings = replace_raw(
            self._display_bindings,
            **{field_name: default_value},
        )
        self._sync_enableable_chrome()
        self.changed.emit()

    def add_binding_row(self, binding: NamedSourceBinding | None = None) -> None:
        """Append one editable source binding row to the active binding table."""

        if self.step_bindings_table is None:
            self._append_step_binding(binding or NamedSourceBinding(alias="NewSource"))
            return
        if self.step_bindings_editor is None:
            self._append_step_binding(binding or NamedSourceBinding(alias="NewSource"))
            return
        self.step_bindings_editor.add_binding_row(binding)
        self._apply_step_bindings(self.step_bindings_editor.bindings())

    def add_source_filter_row(
        self,
        clause: SourceFilterClause | None = None,
    ) -> None:
        """Append one editable source-universe filter clause row."""

        if self.source_filters_table is None:
            return
        if self.source_filters_controller is None:
            raise RuntimeError("Source filters table controller is not initialized.")
        self._updating_ui = True
        try:
            self.source_filters_controller.append(
                clause
                or SourceFilterClause(
                    SourceFilterSubject.FILE,
                    SourceFilterMatchType.IS_IMAGE,
                )
            )
        finally:
            self._updating_ui = False
        self._fit_table_to_rows(self.source_filters_table)
        self._apply_source_filters_table()

    def remove_selected_source_filter_rows(self) -> None:
        """Remove selected source-universe filter clause rows."""

        if self.source_filters_table is None:
            return
        if self.source_filters_controller is None:
            raise RuntimeError("Source filters table controller is not initialized.")
        if not self.source_filters_controller.remove_selected():
            return
        self._fit_table_to_rows(self.source_filters_table)
        self._apply_source_filters_table()

    def remove_selected_binding_rows(self) -> None:
        """Remove selected source binding rows from the open dialog editor."""

        if self.step_bindings_editor is None:
            return
        self.step_bindings_editor.remove_selected_binding_rows()
        self._apply_step_bindings(self.step_bindings_editor.bindings())

    def add_metadata_rule_row(
        self,
        rule: MetadataExtractionRule | None = None,
    ) -> None:
        """Append one editable metadata extraction rule row."""

        if self.metadata_rules_table is None:
            return
        if self.metadata_rules_controller is None:
            raise RuntimeError("Metadata rules table controller is not initialized.")
        self._updating_ui = True
        try:
            self.metadata_rules_controller.append(
                rule
                or MetadataExtractionRule(
                    source=MetadataSource.FILE_NAME,
                    pattern=r"(?P<field>.+)",
                )
            )
        finally:
            self._updating_ui = False
        self._fit_table_to_rows(self.metadata_rules_table)
        self._apply_metadata_rules_table()

    def remove_selected_metadata_rule_rows(self) -> None:
        """Remove selected metadata extraction rule rows."""

        if self.metadata_rules_table is None:
            return
        if self.metadata_rules_controller is None:
            raise RuntimeError("Metadata rules table controller is not initialized.")
        if not self.metadata_rules_controller.remove_selected():
            return
        self._fit_table_to_rows(self.metadata_rules_table)
        self._apply_metadata_rules_table()

    def add_match_plan_row(
        self,
        row: SourceSetPairingRow | None = None,
    ) -> None:
        """Append one editable match-plan dimension row."""

        if self.match_plan_table is None:
            return
        if self.match_plan_controller is None:
            raise RuntimeError("Match plan table controller is not initialized.")
        self._updating_ui = True
        try:
            self.match_plan_controller.append(
                row or SourceSetPairingRow(method=SourceBindingMatchMethod.METADATA)
            )
        finally:
            self._updating_ui = False
        self._fit_table_to_rows(self.match_plan_table)
        self._apply_match_plan_table()

    def remove_selected_match_plan_rows(self) -> None:
        """Remove selected match-plan dimension rows."""

        if self.match_plan_table is None:
            return
        if self.match_plan_controller is None:
            raise RuntimeError("Match plan table controller is not initialized.")
        if not self.match_plan_controller.remove_selected():
            return
        self._fit_table_to_rows(self.match_plan_table)
        self._apply_match_plan_table()

    def clear(self) -> None:
        self._table_placeholder_chrome_state.clear()
        while self.layout.count():
            item = self.layout.takeAt(0)
            widget = item.widget()
            if widget is not None:
                widget.setParent(None)
                widget.deleteLater()
        self.step_bindings_summary_table = None
        self.step_bindings_table = None
        self.step_bindings_editor = None
        self.source_filters_table = None
        self.metadata_rules_table = None
        self.match_plan_table = None
        self.source_filters_controller = None
        self.metadata_rules_controller = None
        self.match_plan_controller = None
        self._editable_table_controllers.clear()
        self._structural_table_controllers.clear()
        if self._form_context is not None:
            self._child_chrome = InlineDataclassChildChrome(self._form_context)

    def _register_editable_table_controller(
        self,
        controller: EditableTableController[EditableRowT],
    ) -> EditableTableController[EditableRowT]:
        """Track a rendered editable table controller for lifecycle guards."""

        self._editable_table_controllers.append(controller)
        return controller

    def _register_structural_table_controller(
        self,
        controller: EditableTableController[EditableRowT],
    ) -> EditableTableController[EditableRowT]:
        """Track a rendered table controller that owns structural child semantics."""

        if controller.semantic_binding is None:
            raise ValueError(
                "Structural table controllers must declare an "
                "EditableTableSemanticBinding."
            )
        controller = self._register_editable_table_controller(controller)
        self._structural_table_controllers.append(controller)
        return controller

    def _structural_table_bindings(
        self,
    ) -> tuple[EditableTableSemanticBinding, ...]:
        return tuple(
            binding for _, binding in self._structural_table_controller_bindings()
        )

    def _structural_table_controller_bindings(
        self,
    ) -> tuple[tuple[EditableTableController, EditableTableSemanticBinding], ...]:
        return tuple(
            (controller, binding)
            for controller in self._structural_table_controllers
            if (binding := controller.semantic_binding) is not None
        )

    def _structural_table_controller_for_field(
        self,
        field_name: str,
    ) -> EditableTableController | None:
        for controller, binding in self._structural_table_controller_bindings():
            if binding.owner_field_name == field_name:
                return controller
        return None

    def _suggestions(self) -> RowSuggestionMap:
        return source_binding_suggestions(
            source_bindings=self._source_bindings,
            inventory=self._inventory,
        )

    @staticmethod
    def _compact_button(button: QPushButton) -> QPushButton:
        button.setFixedHeight(min(CURRENT_LAYOUT.button_height, 24))
        return button

    def _step_bindings_group(
        self,
        step_bindings: StepSourceBindingsConfig,
    ) -> QGroupBox:
        group, layout = self._section_group("Bindings", "bindings")
        summary_table = self._create_table(0, 3)
        self.step_bindings_summary_table = summary_table
        summary_table.setHorizontalHeaderLabels(("Bindings", "Aliases", "Origins"))
        for row_index, row in enumerate(self._binding_summary_rows(step_bindings)):
            summary_table.insertRow(row_index)
            for column_index, value in enumerate(row):
                summary_table.setItem(row_index, column_index, QTableWidgetItem(value))
        summary_table.resizeColumnsToContents()
        self._configure_table(summary_table)
        self._fit_table_to_rows(summary_table)
        layout.addWidget(summary_table)

        buttons = QHBoxLayout()
        buttons.setContentsMargins(0, 0, 0, 0)
        buttons.setSpacing(3)
        edit_button = self._compact_button(QPushButton("Edit bindings...", group))
        edit_button.clicked.connect(self._open_step_bindings_dialog)
        add_button = self._compact_button(QPushButton("Add binding", group))
        add_button.clicked.connect(lambda: self.add_binding_row())
        buttons.addWidget(edit_button)
        buttons.addWidget(add_button)
        buttons.addStretch(1)
        layout.addLayout(buttons)
        return group

    def _create_step_bindings_dialog(self) -> StepBindingsDialog:
        return StepBindingsDialog(
            bindings=SourceBindingsEditorValue(
                self._display_bindings
            ).binding_declarations,
            suggestions=self._suggestions(),
            scope_color_scheme=self._scope_color_scheme,
            parent=self,
        )

    def _open_step_bindings_dialog(self) -> None:
        dialog = self._create_step_bindings_dialog()
        self.step_bindings_editor = dialog.editor
        self.step_bindings_table = dialog.editor.table
        accepted = dialog.exec() == QDialog.DialogCode.Accepted
        if accepted:
            self._apply_step_bindings(dialog.bindings())
        self.step_bindings_editor = None
        self.step_bindings_table = None

    def _append_step_binding(self, binding: NamedSourceBinding) -> None:
        self._apply_step_bindings(
            SourceBindingsEditorValue(self._display_bindings).binding_declarations
            + (binding,)
        )

    @staticmethod
    def _binding_summary_rows(
        step_bindings: StepSourceBindingsConfig,
    ) -> tuple[tuple[str, str, str], ...]:
        bindings = step_bindings.binding_declarations
        if not bindings:
            return ()
        origin_column = DataclassFieldColumns.of(NamedSourceBinding).named("origin")
        return (
            (
                str(len(bindings)),
                ", ".join(binding.alias for binding in bindings),
                ", ".join(
                    sorted(
                        {
                            origin_column.editor.display(binding.origin)
                            for binding in bindings
                        }
                    )
                ),
            ),
        )

    def _source_filters_group(self) -> QGroupBox:
        group, layout = self._section_group("Source Filters", "source_filters")
        table = self._create_row_table(SourceFilterClause)
        self.source_filters_table = table
        self.source_filters_controller = self._register_structural_table_controller(
            self._row_table_controller(
                table,
                SourceFilterClause,
                self._apply_source_filters_table,
                owner_field_name="source_filters",
            ),
        )
        for clause in SourceBindingsEditorValue(
            self._display_bindings
        ).source_filter_declarations:
            self.source_filters_controller.append(clause)
        table.itemChanged.connect(
            lambda _: self.source_filters_controller.request_apply_changes()
        )
        table.resizeColumnsToContents()
        self._configure_table(table)
        self._fit_table_to_rows(table)
        layout.addWidget(table)

        buttons = QHBoxLayout()
        buttons.setContentsMargins(0, 0, 0, 0)
        buttons.setSpacing(3)
        add_button = self._compact_button(QPushButton("Add source filter"))
        add_button.clicked.connect(self.add_source_filter_row)
        remove_button = self._compact_button(QPushButton("Remove selected"))
        remove_button.clicked.connect(self.remove_selected_source_filter_rows)
        buttons.addWidget(add_button)
        buttons.addWidget(remove_button)
        buttons.addStretch(1)
        layout.addLayout(buttons)
        return group

    def _metadata_rules_group(self) -> QGroupBox:
        group, layout = self._section_group("Metadata Rules", "metadata_rules")
        table = self._create_row_table(MetadataExtractionRule)
        self.metadata_rules_table = table
        self.metadata_rules_controller = self._register_structural_table_controller(
            self._row_table_controller(
                table,
                MetadataExtractionRule,
                self._apply_metadata_rules_table,
                owner_field_name="metadata_rules",
            )
        )
        for rule in SourceBindingsEditorValue(
            self._display_bindings
        ).metadata_rule_declarations:
            self.metadata_rules_controller.append(rule)
        table.itemChanged.connect(
            lambda _: self.metadata_rules_controller.request_apply_changes()
        )
        table.resizeColumnsToContents()
        self._configure_table(table)
        self._fit_table_to_rows(table)
        layout.addWidget(table)

        buttons = QHBoxLayout()
        buttons.setContentsMargins(0, 0, 0, 0)
        buttons.setSpacing(3)
        add_button = self._compact_button(QPushButton("Add metadata rule"))
        add_button.clicked.connect(self.add_metadata_rule_row)
        remove_button = self._compact_button(QPushButton("Remove selected"))
        remove_button.clicked.connect(self.remove_selected_metadata_rule_rows)
        buttons.addWidget(add_button)
        buttons.addWidget(remove_button)
        buttons.addStretch(1)
        layout.addLayout(buttons)
        return group

    def _match_plan_group(self) -> QGroupBox:
        group, layout = self._section_group("Source Set Pairing", "match_plan")
        table = self._create_row_table(SourceSetPairingRow)
        self.match_plan_table = table
        self.match_plan_controller = self._register_editable_table_controller(
            self._row_table_controller(
                table,
                SourceSetPairingRow,
                self._apply_match_plan_table,
            )
        )
        for row in SourceSetPairingRow.from_plan(
            SourceBindingsEditorValue(self._display_bindings).match_plan
        ):
            self.match_plan_controller.append(row)
        table.itemChanged.connect(
            lambda _: self.match_plan_controller.request_apply_changes()
        )
        table.resizeColumnsToContents()
        self._configure_table(table)
        self._fit_table_to_rows(table)
        layout.addWidget(table)

        buttons = QHBoxLayout()
        buttons.setContentsMargins(0, 0, 0, 0)
        buttons.setSpacing(3)
        add_button = self._compact_button(QPushButton("Add pairing key"))
        add_button.clicked.connect(self.add_match_plan_row)
        remove_button = self._compact_button(QPushButton("Remove selected"))
        remove_button.clicked.connect(self.remove_selected_match_plan_rows)
        buttons.addWidget(add_button)
        buttons.addWidget(remove_button)
        buttons.addStretch(1)
        layout.addLayout(buttons)
        return group

    def _apply_step_bindings(
        self,
        bindings: tuple[NamedSourceBinding, ...],
    ) -> None:
        if self._updating_ui:
            return
        self._bindings = replace_raw(self._bindings, bindings=bindings)
        self._display_bindings = replace_raw(self._display_bindings, bindings=bindings)
        self.refresh()
        self.changed.emit()

    def _apply_source_filters_table(self) -> None:
        if self._updating_ui or self.source_filters_table is None:
            return
        if self.source_filters_controller is None:
            raise RuntimeError("Source filters table controller is not initialized.")
        if self.source_filters_controller.has_incomplete_rows():
            return
        source_filters = self.source_filters_controller.rows()
        self._bindings = replace_raw(
            self._bindings,
            source_filters=source_filters,
        )
        self._display_bindings = replace_raw(
            self._display_bindings,
            source_filters=source_filters,
        )
        self.changed.emit()

    def _apply_metadata_rules_table(self) -> None:
        if self._updating_ui or self.metadata_rules_table is None:
            return
        if self.metadata_rules_controller is None:
            raise RuntimeError("Metadata rules table controller is not initialized.")
        if self.metadata_rules_controller.has_incomplete_rows():
            return
        metadata_rules = self.metadata_rules_controller.rows()
        self._bindings = replace_raw(
            self._bindings,
            metadata_rules=metadata_rules,
        )
        self._display_bindings = replace_raw(
            self._display_bindings,
            metadata_rules=metadata_rules,
        )
        self.changed.emit()

    def _apply_match_plan_table(self) -> None:
        if self._updating_ui or self.match_plan_table is None:
            return
        if self.match_plan_controller is None:
            raise RuntimeError("Match plan table controller is not initialized.")
        if self.match_plan_controller.has_incomplete_rows():
            return
        rows = self.match_plan_controller.rows()
        if any(row.fields for row in rows) and not all(row.fields for row in rows):
            return
        match_plan = SourceSetPairingRow.to_plan(rows)
        self._bindings = replace_raw(
            self._bindings,
            match_plan=match_plan,
        )
        self._display_bindings = replace_raw(
            self._display_bindings,
            match_plan=match_plan,
        )
        self.changed.emit()

    def _table_group(
        self,
        title: str,
        columns: tuple[str, ...],
        rows: tuple[tuple[str, ...], ...],
    ) -> QGroupBox:
        group, layout = self._section_group(title)
        table = self._create_table(len(rows), len(columns))
        table.setHorizontalHeaderLabels(columns)
        for row_index, row in enumerate(rows):
            for column_index, value in enumerate(row):
                table.setItem(row_index, column_index, QTableWidgetItem(value))
        table.resizeColumnsToContents()
        self._configure_table(table)
        self._fit_table_to_rows(table)
        layout.addWidget(table)
        return group

    def _create_row_table(self, row_type: type) -> ScopedTableWidget:
        columns = DataclassFieldColumns.of(row_type)
        table = self._create_table(0, len(columns))
        table.setHorizontalHeaderLabels(columns.labels)
        columns.apply_header_items(table.horizontalHeaderItem)
        return table

    def _row_table_controller(
        self,
        table: QTableWidget,
        row_type: type,
        apply_changes: Callable[[], None],
        *,
        owner_field_name: str | None = None,
    ) -> EditableTableController:
        columns = DataclassFieldColumns.of(row_type)
        return EditableTableController(
            table=table,
            columns=columns,
            apply_changes=apply_changes,
            suggestions=self._suggestions(),
            semantic_binding=(
                None
                if owner_field_name is None
                else EditableTableSemanticBinding(
                    owner_field_name=owner_field_name,
                    row_path_policy=IsomorphicDataclassRowPathPolicy(
                        row_value_type=row_type,
                        column_count=len(columns),
                    ),
                )
            ),
        )

    def _create_table(self, rows: int, columns: int) -> ScopedTableWidget:
        table = ScopedTableWidget(rows, columns)
        table.set_scope_color_scheme(self._scope_color_scheme)
        return table

    def _section_group(
        self,
        title: str,
        field_name: str | None = None,
    ) -> tuple[QGroupBox, QVBoxLayout]:
        group = QGroupBox("")
        group.setStyleSheet("""
            QGroupBox {
                margin-top: 6px;
            }
            """)
        layout = QVBoxLayout(group)
        layout.setContentsMargins(4, 4, 4, 4)
        layout.setSpacing(3)
        if field_name and self._child_chrome:
            self._child_chrome.register_section_group(field_name, group)
            title_layout = self._child_chrome.create_section_header(
                title=title,
                field_name=field_name,
            )
            layout.addLayout(title_layout)
        else:
            label = QLabel(title, group)
            font = label.font()
            font.setBold(True)
            label.setFont(font)
            label.setAlignment(
                Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter
            )
            label.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Fixed)
            layout.addWidget(label)
        return group, layout

    def refresh_section_label_markers(
        self,
        owner_field_paths: tuple[DottedFieldPath, ...] | None = None,
    ) -> None:
        from objectstate.time_travel_profile import TimeTravelProfiler

        with TimeTravelProfiler.phase(
            "openhcs.source_bindings.refresh_section_label_markers"
        ):
            field_names = self._field_names_for_owner_paths(owner_field_paths)
            if self._child_chrome is not None:
                self._child_chrome.refresh_markers(field_names)
            self._refresh_table_placeholder_chrome(field_names)
            if field_names is None or self._enabled_field_name() in field_names:
                self._sync_enableable_chrome()

    def _field_names_for_owner_paths(
        self,
        owner_field_paths: tuple[DottedFieldPath, ...] | None,
    ) -> tuple[str, ...] | None:
        if owner_field_paths is None:
            return None
        if self._form_context is None:
            return ()

        owner_parts = self._form_context.owner_path.parts
        field_names: list[str] = []
        seen: set[str] = set()
        for owner_field_path in owner_field_paths:
            path_parts = owner_field_path.parts
            if path_parts[: len(owner_parts)] != owner_parts:
                continue
            if len(path_parts) != len(owner_parts) + 1:
                continue
            field_name = path_parts[-1]
            if field_name not in seen:
                seen.add(field_name)
                field_names.append(field_name)
        return tuple(field_names)

    def _refresh_table_placeholder_chrome(
        self,
        field_names: tuple[str, ...] | None = None,
    ) -> None:
        target_field_names = set(field_names) if field_names is not None else None
        for field_name, table in self._table_placeholder_targets():
            if target_field_names is not None and field_name not in target_field_names:
                continue
            active = self._field_has_table_placeholder_preview(field_name)
            if active and self._child_chrome is not None:
                group = self._child_chrome.navigation_target(field_name)
                if group is not None:
                    InlineDataclassChildChrome.set_widget_dimmed(group, False)
            if table is not None:
                if self._table_placeholder_chrome_state.get(field_name) != active:
                    EditableTableController.apply_placeholder_text_style_to_table(
                        table,
                        active,
                    )
                    self._table_placeholder_chrome_state[field_name] = active

    def _table_placeholder_targets(self) -> tuple[tuple[str, QTableWidget | None], ...]:
        return (
            ("bindings", self.step_bindings_summary_table),
            ("source_filters", self.source_filters_table),
            ("metadata_rules", self.metadata_rules_table),
            ("match_plan", self.match_plan_table),
        )

    def _field_has_table_placeholder_preview(self, field_name: str) -> bool:
        if (
            self._form_context is not None
            and self._form_context.child_has_inherited_preview(field_name)
        ):
            return True
        raw_value = SourceBindingsEditorValue(self._bindings).raw_field_value(
            field_name
        )
        display_value = SourceBindingsEditorValue(
            self._display_bindings
        ).raw_field_value(field_name)
        return raw_value is None and display_value is not None

    @staticmethod
    def _configure_table(table: QTableWidget) -> None:
        EditableTableLayout.configure(table)

    @staticmethod
    def _fit_table_to_rows(table: QTableWidget) -> None:
        EditableTableLayout.fit_to_rows(table)


def create_source_bindings_editor_widget(
    *,
    current_value: SourceBindingsEditorRawValue,
    manager: ParameterFormManager | None = None,
    param_info: InlineDataclassWidgetInfo | None = None,
    parent: QWidget | None = None,
    **_: object,
) -> SourceBindingsEditorWidget:
    """pyqt-reactive inline dataclass widget factory for source bindings."""

    SourceBindingsEditorValue(current_value)
    display_value = resolved_source_bindings_value(
        current_value=current_value,
        manager=manager,
        param_info=param_info,
    )
    return SourceBindingsEditorWidget.from_bindings(
        current_value,
        display_bindings=display_value,
        form_context=source_bindings_form_context(
            current_value=current_value,
            manager=manager,
            param_info=param_info,
        ),
        parent=parent,
    )


def source_bindings_form_context(
    *,
    current_value: SourceBindingsEditorRawValue,
    manager: ParameterFormManager | None,
    param_info: InlineDataclassWidgetInfo | None,
) -> InlineDataclassFormContext | None:
    """Build the semantic form context for source-binding child fields."""

    if manager is None or param_info is None:
        return None
    SourceBindingsEditorValue(current_value)
    return InlineDataclassFormContext.from_inline_widget(
        manager=manager,
        param_info=param_info,
        current_value=current_value,
    )


def resolved_source_bindings_value(
    *,
    current_value: SourceBindingsEditorRawValue,
    manager: ParameterFormManager | None,
    param_info: InlineDataclassWidgetInfo | None,
) -> SourceBindingsEditorRawValue:
    """Return the live inherited value used to seed placeholder tables."""

    if manager is None or param_info is None:
        return current_value
    field_path = (
        DottedFieldPath(manager.field_id).child(param_info.name)
        if manager.field_id
        else DottedFieldPath(param_info.name)
    )
    resolved_value = manager.state.get_resolved_value(field_path.value)
    if resolved_value is None:
        return current_value
    expected_base_type = SourceBindingsEditorValue(current_value).base_type()
    resolved_editor_value = SourceBindingsEditorValue(resolved_value)
    if resolved_editor_value.base_type() is not expected_base_type:
        raise TypeError(
            f"Resolved source-bindings value must be {expected_base_type.__name__}, "
            f"got {type(resolved_value).__name__}."
        )
    return resolved_value


def register_source_bindings_editor_widget() -> None:
    """Register the typed source-binding editor with pyqt-reactive forms."""

    from pyqt_reactive.forms.parameter_info_types import (
        register_inline_dataclass_widget,
    )

    for config_type in SourceBindingsConfig.registered_plan_types():
        if issubclass(config_type, SourceBindingsConfig):
            register_inline_dataclass_widget(
                config_type,
                create_source_bindings_editor_widget,
            )


register_source_bindings_editor_widget()


__all__ = (
    "SourceBindingsEditorWidget",
    "create_source_bindings_editor_widget",
    "resolved_source_bindings_value",
    "register_source_bindings_editor_widget",
)
