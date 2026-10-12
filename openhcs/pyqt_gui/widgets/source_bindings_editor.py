"""PyQt source-bindings editor whose tables derive from the binding dataclasses."""

from __future__ import annotations

import re
from dataclasses import dataclass, fields
from types import MappingProxyType
from typing import (
    Annotated,
    cast,
)

from objectstate.lazy_factory import (
    LazyDataclass,
    resolve_lazy_configurations_for_serialization,
)
from PyQt6.QtCore import pyqtSignal
from PyQt6.QtWidgets import (
    QAbstractItemView,
    QDialog,
    QDialogButtonBox,
    QHBoxLayout,
    QPushButton,
    QTableWidgetItem,
    QVBoxLayout,
    QWidget,
)
from pyqt_reactive.forms.inline_dataclass_context import (
    InlineDataclassFormContext,
)
from pyqt_reactive.widgets.editable_table import (
    INVALID_CELL_VALUE_ERRORS,
    CellEditContext,
    ChoiceCellEditor,
    DataclassFieldColumns,
    EditableTableLayout,
    RowSuggestion,
    RowSuggestionMap,
)
from pyqt_reactive.widgets.sectioned_dataclass_editor import (
    EditorSection,
    ReadOnlyTableSection,
    RowTableSection,
    SectionedDataclassEditor,
    TupleFieldSection,
    TupleSummarySection,
)
from formbridge.forms.parameter_info_types import register_inline_dataclass_widget
from formbridge.forms.raw_display_value import RawDisplayValue
from pyqt_reactive.widgets.shared.scoped_table_widget import ScopedTableWidget
from python_introspect import (
    FieldLabel,
    RegisteredClassChoices,
)

from openhcs.core.source_bindings import (
    ComponentSelector,
    MetadataExtractionRule,
    MetadataSelector,
    FromFileName,
    NamedSourceBinding,
    SourceBindingMatchDimension,
    SourceBindingMatchField,
    PathIsImage,
    SourceFileName,
    SourceFilterClause,
    SourceSetPairing,
    PairByMetadata,
    PairByOrder,
)
from openhcs.core.config import (
    EMPTY_SOURCE_BINDINGS,
    SourceBindingsConfig,
    StepSourceBindingsConfig,
)
from openhcs.core.source_bindings_preview import (
    SourceBindingsPreview,
    SourceInventory,
)

SourceBindingsEditorRawValue = SourceBindingsConfig | LazyDataclass


# --- Source-binding tables ---------------------------------------------------


@dataclass(frozen=True, slots=True)
class SourceSetPairingRow:
    """One row of the source-set pairing table: a pairing and one shared key."""

    method: Annotated[
        type[SourceSetPairing],
        RegisteredClassChoices(SourceSetPairing),
        FieldLabel("Pairing Method"),
    ]
    """How selected aliases are grouped into one source set: by source order, or by declared metadata keys."""

    fields: Annotated[
        tuple[SourceBindingMatchField, ...], FieldLabel("Pairing Keys")
    ] = ()
    """Alias-to-metadata-field pairs forming one shared source-set key when the method is metadata."""

    @classmethod
    def from_plan(
        cls,
        plan: SourceSetPairing | None,
    ) -> tuple["SourceSetPairingRow", ...]:
        """Rows for one pairing; the default order pairing and an unset one show none."""
        if plan is None or plan == PairByOrder():
            return ()
        if not plan.dimensions:
            return (cls(method=type(plan)),)
        return tuple(
            cls(method=type(plan), fields=dimension.fields)
            for dimension in plan.dimensions
        )

    @staticmethod
    def to_plan(
        rows: tuple["SourceSetPairingRow", ...],
        owner: SourceBindingsEditorRawValue,
    ) -> SourceSetPairing | None:
        """The pairing the rows declare; ``owner``'s field default without rows."""
        if not rows:
            return next(
                item.default for item in fields(owner) if item.name == "match_plan"
            )
        return rows[0].method.keyed_by(
            tuple(
                SourceBindingMatchDimension(fields=row.fields)
                for row in rows
                if row.fields
            )
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



def shown_pipeline_and_step_configs(
    display: SourceBindingsEditorRawValue,
    pipeline_source_bindings: SourceBindingsConfig,
) -> tuple[SourceBindingsConfig, StepSourceBindingsConfig]:
    """The pipeline and step configs an editor showing ``display`` renders.

    A step config is shown against the given pipeline config; a pipeline
    config is shown as itself with no step bindings.
    """

    concrete = (
        display
        if isinstance(display, SourceBindingsConfig)
        else resolve_lazy_configurations_for_serialization(display)
    )
    if not isinstance(concrete, SourceBindingsConfig):
        raise TypeError(
            "Lazy source-binding resolution returned "
            f"{type(concrete).__name__}, expected SourceBindingsConfig."
        )
    if isinstance(concrete, StepSourceBindingsConfig):
        return pipeline_source_bindings, concrete
    return concrete, EMPTY_SOURCE_BINDINGS


@dataclass(frozen=True, kw_only=True)
class PairingRowsSection(RowTableSection):
    """The pairing field shown as one row per shared key."""

    def rows_of(self, field_value: object) -> tuple[SourceSetPairingRow, ...]:
        return SourceSetPairingRow.from_plan(cast(SourceSetPairing | None, field_value))

    def value_of(
        self,
        rows: tuple[SourceSetPairingRow, ...],
        value: RawDisplayValue,
    ) -> SourceSetPairing | None:
        return SourceSetPairingRow.to_plan(rows, value.raw)

    def rows_complete(self, rows: tuple[SourceSetPairingRow, ...]) -> bool:
        """Keyed rows and unkeyed rows are not mixed while the user is typing."""

        return all(row.fields for row in rows) or not any(row.fields for row in rows)


SOURCE_FILTERS = TupleFieldSection(
    title="Source Filters",
    field_name="source_filters",
    row_type=SourceFilterClause,
    new_row=lambda: SourceFilterClause(SourceFileName, PathIsImage),
    add_label="Add source filter",
    refreshes_alone=True,
)
METADATA_RULES = TupleFieldSection(
    title="Metadata Rules",
    field_name="metadata_rules",
    row_type=MetadataExtractionRule,
    new_row=lambda: MetadataExtractionRule(source=FromFileName, pattern=r"(?P<field>.+)"),
    add_label="Add metadata rule",
)
PAIRING = PairingRowsSection(
    title="Source Set Pairing",
    field_name="match_plan",
    row_type=SourceSetPairingRow,
    new_row=lambda: SourceSetPairingRow(method=PairByMetadata),
    add_label="Add pairing key",
)


class SourceBindingsEditorWidget(SectionedDataclassEditor):
    """Inline form widget for source bindings: it declares the sections.

    The pipeline config and the file inventory are the inputs the read-only
    sections and the picker suggestions are computed from.
    """

    value_type = SourceBindingsConfig
    enable_tooltip = "Enable step source bindings"

    def __init__(
        self,
        value: RawDisplayValue,
        *,
        source_bindings: SourceBindingsConfig = SourceBindingsConfig(),
        inventory: SourceInventory | None = None,
        form_context: InlineDataclassFormContext | None = None,
        parent: QWidget | None = None,
    ) -> None:
        self._source_bindings = source_bindings
        self._inventory = inventory
        super().__init__(value, form_context=form_context, parent=parent)

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

    def resolved_view_inputs(
        self,
        source_bindings: SourceBindingsConfig,
    ) -> tuple[SourceBindingsConfig, StepSourceBindingsConfig]:
        """The pipeline and step configs shown against ``source_bindings``."""

        return shown_pipeline_and_step_configs(self.shown.display, source_bindings)

    def suggestions(self) -> RowSuggestionMap:
        return source_binding_suggestions(
            source_bindings=self._source_bindings,
            inventory=self._inventory,
        )

    def step_bindings_dialog(self) -> StepBindingsDialog:
        return StepBindingsDialog(
            bindings=cast(tuple, self.rendered("bindings").section.shown(self.shown)),
            suggestions=self.suggestions(),
            scope_color_scheme=self._scope_color_scheme,
            parent=self,
        )

    def edit_step_bindings(self) -> None:
        dialog = self.step_bindings_dialog()
        if dialog.exec() == QDialog.DialogCode.Accepted:
            self.replace_field("bindings", dialog.bindings())

    def sections(self) -> tuple[EditorSection, ...]:
        pipeline, step = self.resolved_view_inputs(self._source_bindings)
        binding_columns = tuple(
            DataclassFieldColumns.of(NamedSourceBinding).named(name)
            for name in ("alias", "artifact_kind", "origin")
        )
        origin = binding_columns[-1].editor
        pairing_method = DataclassFieldColumns.of(SourceSetPairingRow).named("method").editor
        step_bindings = step.binding_declarations
        return (
            ReadOnlyTableSection(
                title="Pipeline Sources",
                columns=("Field", "Value"),
                rows=(
                    ("image-plane sources", str(len(pipeline.image_plane_sources))),
                    (
                        "imported metadata tables",
                        str(len(pipeline.imported_metadata_tables)),
                    ),
                ),
            ),
            ReadOnlyTableSection(
                title="Pipeline Bindings",
                columns=tuple(column.label for column in binding_columns),
                rows=tuple(
                    tuple(
                        column.editor.display(column.value_of(binding))
                        for column in binding_columns
                    )
                    for binding in pipeline.binding_declarations
                ),
            ),
            TupleSummarySection(
                title="Bindings",
                field_name="bindings",
                columns=("Bindings", "Aliases", "Origins"),
                rows=(
                    (
                        str(len(step_bindings)),
                        ", ".join(binding.alias for binding in step_bindings),
                        ", ".join(
                            sorted({origin.display(binding.origin) for binding in step_bindings})
                        ),
                    ),
                )
                if step_bindings
                else (),
                actions=(
                    ("Edit bindings...", self.edit_step_bindings),
                    (
                        "Add binding",
                        lambda: self.append_to_field(
                            "bindings", NamedSourceBinding(alias="NewSource")
                        ),
                    ),
                ),
            ),
            SOURCE_FILTERS,
            METADATA_RULES,
            PAIRING,
            ReadOnlyTableSection(
                title="Resolved Source Set Pairing",
                columns=("Scope", "Method", "Dimensions"),
                rows=tuple(
                    (scope, pairing_method.display(type(plan)), str(len(plan.dimensions)))
                    for scope, plan in (
                        ("pipeline", pipeline.match_plan),
                        ("step", step.match_plan),
                    )
                    if plan is not None
                ),
            ),
            *self._preview_sections(pipeline, step),
        )

    def _preview_sections(
        self,
        pipeline: SourceBindingsConfig,
        step: StepSourceBindingsConfig,
    ) -> tuple[EditorSection, ...]:
        """What the bindings match in the file inventory, when one is known."""

        if self._inventory is None:
            return ()
        preview = SourceBindingsPreview.from_config_and_step_bindings(
            source_bindings=pipeline,
            step_bindings=step,
            inventory=self._inventory,
        )
        diagnostics = ReadOnlyTableSection(
            title="Diagnostics",
            columns=("Severity", "Code", "Alias", "Message"),
            rows=tuple(
                (
                    diagnostic.severity.value,
                    diagnostic.code,
                    diagnostic.alias or "",
                    diagnostic.message,
                )
                for diagnostic in preview.diagnostics
            ),
        )
        return (
            *((diagnostics,) if preview.diagnostics else ()),
            ReadOnlyTableSection(
                title="Preview Matches",
                columns=("Alias", "Scope", "Matched", "Samples"),
                rows=tuple(
                    (
                        row.alias,
                        row.declaration_scope,
                        str(row.matched_source_count),
                        ", ".join(row.sample_paths),
                    )
                    for row in preview.binding_rows
                ),
            ),
            ReadOnlyTableSection(
                title="Source Sets",
                columns=("Index", "Aliases", "Metadata"),
                rows=tuple(
                    (
                        str(row.index),
                        ", ".join(f"{alias}:{path}" for alias, path in row.paths_by_alias),
                        ", ".join(f"{field}={value}" for field, value in row.metadata),
                    )
                    for row in preview.source_set_rows
                ),
            ),
        )


register_inline_dataclass_widget(SourceBindingsConfig, SourceBindingsEditorWidget.in_form)


__all__ = (
    "SourceBindingsEditorWidget",
    "shown_pipeline_and_step_configs",
)
