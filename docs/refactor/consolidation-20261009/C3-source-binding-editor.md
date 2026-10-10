# C3: Source-binding editor

**Head audited:** `openhcs` `main` at `c1ec3c5e7` (#1164). **Rules:** [00-RULES.md](00-RULES.md) (including 1a, families not enums). **Step 2.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* pyqt-reactive `IsomorphicDataclassRowPathPolicy`. *Hands to:* L4 (the editable table).

## What is wrong

**The editor restates the source-binding dataclasses as hand-enumerated text columns and rebuilds every binding from that text, so any field without a column is silently reset when the GUI saves (live data loss).**

- `pyqt_gui/widgets/source_bindings_editor.py` is 3,554 lines. `SourceBindingColumn` (:163-223) lists 11 columns of `NamedSourceBinding` (core/source_bindings.py:892) by hand; `SourceFilterColumn`, `MetadataRuleColumn` and `MatchPlanColumn` (:226-263) restate `SourceFilterClause`, `MetadataExtractionRule` and the match plan the same way.
- **Bug:** `StepBindingsTableEditor.bindings()` (:1448) calls `EditableSourceBindingRow.from_cells` (:1730) on the cell text, which constructs a new `NamedSourceBinding` from the 11 cells. `explicit_source`, `load_as_monochrome` (added in `ccfef5f6d`), `load_as_mask`, `source_channel_axis` and `source_channel_counts` return to their defaults on every save. Five fields, not two.
- The text round-trip: `SelectorListCodec` (:1600-1720) encodes selectors, filters and match fields as `k=v;…` / `subject:match:value` strings and parses them back; `from_cells` re-parses booleans with a literal set written twice (:1751, :1764) and restates four core defaults (`ImageArtifactType`, `STEP_INPUT`, `MATCHED`, `PRIMARY_PLANE`; :1756-1770) plus `FILE_NAME`, `IS_IMAGE`, `FILE`, `ORDER` in the sibling row models (:1810-1886). `filter_cells` raises on grouped filters (:1630), so a metadata rule with an `any_group` filter cannot be displayed.
- `STRUCTURED_SELECTOR_EDITOR_SPEC_ITEMS` (:340-390) hand-lists five dialog shapes with per-shape parser/formatter callables and hand-written choice lists, all restating element dataclass fields.
- `StepBindingsTableEditor` (:1375-1563) re-implements the controller's `_set_cell`/`_cell_text` for the transposed table.
- `core/source_bindings_view.py` (575 lines) holds 9 `*View` mirrors plus `SourceBindingsViewModel` that flatten enums and types to strings; the editor reads those strings back for display. Its only consumer is the editor.

## Target

- **Columns are derived from the row dataclass.** `DataclassFieldColumn` is built from `dataclasses.fields` + `get_type_hints(include_extras=True)`: a nested dataclass field (`selector`) flattens into its fields; header text is the field name, overridden by `Annotated[..., FieldLabel("…")]` only where the UI wording differs; the tooltip is the field's own docstring. A field gets a column exactly when a cell editor accepts its type. Fields no editor accepts (`explicit_source`, `source_channel_counts`) have no column and are preserved.
- **Cell editors are an `AutoRegisterMeta` family keyed by the field type:** text scalars, booleans (check box), choices (an `Enum` type's members or an `AutoRegisterMeta` family's registry, e.g. `type[ArtifactType]`; never hand-listed), and tuples of records (a typed dialog whose columns are derived from the element dataclass, recursively). Cells hold typed values; no text codec.
- **Editing replaces the typed value.** The bindings table keeps the `NamedSourceBinding` values and applies `dataclasses.replace` along the column's field path; `bindings()` returns them. Isomorphic tables (`SourceFilterClause`, `MetadataExtractionRule`, the pairing row) construct the row type from all its fields, and `IsomorphicDataclassRowPathPolicy` asserts every field has a column.
- **Deleted:** `EditableTableColumn` and the four column enums, `EnumCellSpec`, `FreeFormCellEditorKind`, `FreeFormCellSpec`, `StructuredSelectorEditorSpec` and its spec table, the four dialog row parse/format functions, `SelectorListCodec`, the four `Editable*Row` models, `StepBindingsTableEditor`'s duplicated cell code, and every `*View` class plus `SourceBindingsViewModel`. The remaining preview code (`SourceInventory`, `SourceBindingsPreview`) moves to `core/source_bindings_preview.py`.
- Visible consequences: `load_as_monochrome`, `load_as_mask` and `source_channel_axis` gain rows because their types have editors; booleans are check boxes; record-list cells are edited through the typed picker only (no free-text `k=v;…` entry); field docstrings carry the tooltip text the column enums used to hold.
- `ComponentSelector.component` is annotated `AllComponents` (what `__post_init__` already coerces to), so its editor derives from the type.

**L4 boundary (left in place, not extended):** `EditableTableProgrammaticUpdateGuard`, `EditableTableItem`, `EditableTableController` (Qt mechanics, ObjectState semantic chrome, placeholder styling), `EditableTableLayout`, `StructuredSelectorCellWidget`/`StructuredSelectorDialog`, and the cell-editor family with `DataclassFieldColumn`. C3 changes their cell protocol from `str` to typed values; L4 moves the block to pyqt-reactive unchanged.

**Rule 1a records for other owners:** `SourceBindingOrigin`, `SourceSetRole`, `SourceProjectionRole`, `MetadataSource`, `SourceFilterSubject`, `SourceFilterMatchType` (behaviour already on members: `requires_value`) and `SourceBindingMatchMethod` are behaviourless or near-behaviourless enums in `core/source_bindings.py`; they belong to G4 (sources). `AllComponents` belongs to G1. The editor derives choices from whatever type they become.

## Guards

`tests/unit/pyqt_gui/test_source_bindings_editor_guards.py`:
- AST: `source_bindings_editor.py` defines no `Enum` subclass, no class named `*Codec`, no `from_cells`/`cells`/`row_from_cells`/`row_cells`, and calls no `split`/`partition` (cells are never parsed from text).
- AST: the editor never iterates an `Enum` class directly; choice lists come from `ChoiceCellEditor` over the field type (rule 1a).
- `core/source_bindings_view.py` does not exist; `core/source_bindings_preview.py` defines no `*View`/`*ViewModel` class.
- Every `NamedSourceBinding` leaf field has a derived column exactly when a cell editor accepts its type (a new editable field cannot be forgotten; a non-editable one is preserved by the round-trip test).

## Tests

- New: a binding with `explicit_source`, `load_as_monochrome`, `load_as_mask`, `source_channel_axis` and `source_channel_counts` set, edited through the bindings table, comes back with every untouched field equal (written first, failing at head).
- Rewrite the editor tests that drive text cells (`set_binding_cell_text(…, "channel=1")`) to set typed values; delete tests of deleted code (structured-dialog text format, view model mirrors).
- Keep the ObjectState chrome, time-travel and navigation tests unchanged in intent.

## New-case experiments

- *Today:* a new editable `NamedSourceBinding` field needs a `SourceBindingColumn` member, a position in `from_cells` unpacking, a parse with a copied default, a `cells()` entry, and (if a list) a codec pair: 5 edits; forgetting them silently resets the field.
- *After:* the field declaration only. Its column, editor and parsing derive from its type; a type with no editor is preserved untouched.

## Done when

The bindings table round-trips every field; the deleted names above are gone; the guards and the source-binding editor, preview and cross-window tests pass offscreen.
