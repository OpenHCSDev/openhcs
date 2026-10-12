# U6b: Source-bindings editor widget

**Head audited:** `openhcs` `main` at `ae6ddace5` (#1210). **Rules:** [00-RULES.md](00-RULES.md). **Origin:** fork. **Step 2 (U6).**
**Shared abstractions.** *Builds:* a sectioned inline-dataclass editor in pyqt-reactive and a raw/display value pair in formbridge. *Uses:* `EditableTableController`, `DataclassFieldColumns`, `InlineDataclassChildChrome`, `EnabledTitleWidgetMoveAuthority` (pyqt-reactive, all existing).

## What is wrong

**`SourceBindingsEditorWidget` (`openhcs/pyqt_gui/widgets/source_bindings_editor.py:516-1903`, 1,388 lines, 77 methods, 28 instance attributes, 74 `None` comparisons) is a generic "edit a dataclass whose fields are lists of typed rows" widget written once, by hand, for one config class.**

### Classification (77 methods)

| Concern | Methods | Lines | Members |
|---|---|---|---|
| raw value and resolved preview (generic) | 10 | 204 | `from_bindings`, `value`, `get_value`, `set_value`, `set_resolved_value_preview`, `set_raw_value_with_resolved_preview`, `_refresh_source_filters_only`, `_refresh_enableable_only`, `_rendered_bindings_equal`, `_rendered_sections_equal` |
| child-field labels, reset, navigation, placeholder style (generic) | 17 | 237 | `refresh_child_field_chrome`, `reset_inline_dataclass_fields`, `child_field_semantic_owner_paths`, `refresh_child_field_semantics`, `_refresh_single_child_field_chrome`, `child_field_navigation_target`, `child_subfield_navigation_target`, `child_field_identity`, `child_field_label`, `child_field_reset_button`, `child_field_section_group`, `_section_group`, `refresh_section_label_markers`, `_field_names_for_owner_paths`, `_refresh_table_placeholder_chrome`, `_table_placeholder_targets`, `_field_has_table_placeholder_preview` |
| enable checkbox in the group-box title (generic) | 9 | 128 | `_enabled_structural_target`, `configure_inline_dataclass_groupbox`, `_config_type_is_enableable`, `_enabled_field_name`, `_enabled_value`, `_sync_enableable_chrome`, `_on_enabled_checkbox_toggled`, `_set_enabled_value`, `_reset_enabled_field` |
| change-signal wiring and scope colours (generic) | 3 | 29 | `connect_change_signal`, `disconnect_change_signal`, `set_scope_color_scheme` |
| typed row tables: build, add, remove, apply, track (generic) | 25 | 381 | `add_source_filter_row`, `remove_selected_source_filter_rows`, `add_metadata_rule_row`, `remove_selected_metadata_rule_rows`, `add_match_plan_row`, `remove_selected_match_plan_rows`, `clear`, `_register_editable_table_controller`, `_register_structural_table_controller`, `_structural_table_bindings`, `_structural_table_controller_bindings`, `_structural_table_controller_for_field`, `_compact_button`, `_source_filters_group`, `_metadata_rules_group`, `_match_plan_group`, `_apply_source_filters_table`, `_apply_metadata_rules_table`, `_apply_match_plan_table`, `_table_group`, `_create_row_table`, `_row_table_controller`, `_create_table`, `_configure_table`, `_fit_table_to_rows` |
| source-binding declarations (domain) | 13 | 306 | `__init__`, `resolved_view_inputs`, `set_preview_context`, `refresh`, `add_binding_row`, `remove_selected_binding_rows`, `_suggestions`, `_step_bindings_group`, `_create_step_bindings_dialog`, `_open_step_bindings_dialog`, `_append_step_binding`, `_binding_summary_rows`, `_apply_step_bindings` |

64 of 77 methods (979 of 1,285 method lines) are generic machinery. Of the 13 domain methods, `refresh` and `__init__` mix a declaration (which sections exist) with machinery (how a section is built).

### Attributes (28)

- **Domain, 2:** `_source_bindings`, `_inventory` (the pipeline config and the file inventory that the read-only tables and the suggestions are computed from).
- **Value pair, 2:** `_bindings`, `_display_bindings`. Two attributes updated side by side in 9 places.
- **`None` modes, 16 attributes for 3 modes:** `_form_context`, `_child_chrome` ("is this widget inside a form", stored twice, tested 23 times); `step_bindings_summary_table`, `step_bindings_table`, `step_bindings_editor`, `source_filters_table`, `metadata_rules_table`, `match_plan_table`, `source_filters_controller`, `metadata_rules_controller`, `match_plan_controller` ("is this section rendered", reset by hand in `clear`); `_inline_groupbox`, `_enabled_checkbox`, `_enabled_title_widget`, `_enabled_reset_button`, `_enabled_provenance_button` ("is the enable checkbox attached").
- **Lifecycle flags, 2:** `_updating_ui`, `_updating_enableable_chrome`.
- **Rosters, 3:** `_editable_table_controllers`, `_structural_table_controllers`, `_table_placeholder_chrome_state`, plus the method roster `_table_placeholder_targets` (field name to table, restated).
- **Qt plumbing, 3:** `_change_signal_callbacks`, `_scope_color_scheme`, `layout`.

### Restated relations

- **Three copies per row section.** `_source_filters_group` / `_metadata_rules_group` / `_match_plan_group` (37 lines each), `add_*_row` and `remove_selected_*_rows` (3 each), `_apply_*_table` (3). They differ in: field name, row type, title, button label, default new row, and (pairing only) a rows-to-value conversion. P1 Thm 4.7: a copy is one implementation; derive it from one place.
- **Field roster restated 5 times:** `_rendered_sections_equal`, `_refresh_source_filters_only`, `_table_placeholder_targets`, `clear`, and `SourceBindingsEditorValue`'s four per-field properties.
- **13 forwarded methods:** `from_bindings` (to `__init__`), `value` (to `get_value`), `refresh_child_field_chrome` (to `refresh_section_label_markers`), `child_field_navigation_target`, `child_field_identity`, `child_field_label`, `child_field_reset_button` (to `InlineDataclassChildChrome`), `_configure_table`, `_fit_table_to_rows` (to `EditableTableLayout`), `_config_type_is_enableable`, `_enabled_field_name` (to python-introspect), `_register_editable_table_controller`, `_structural_table_bindings`.
- **Kind switches, 3:** `if form_context is None` (attached or standalone), `if field_name and self._child_chrome` in `_section_group` (field section or read-only), `isinstance(concrete, StepSourceBindingsConfig)` in `view_inputs` (domain; stays, it is a nominal check on the config family).

## Target

Section kinds are a family; the widget renders what the members declare (P1 Prop 3.1, rule 1a). Crossing concerns are separate bases of the widget (P1 Prop 4.2, Thm 4.6): the value pair, the child-field chrome, the title checkbox and the row tables each have consumers the others lack.

```python
# pyqt-reactive: pyqt_reactive/widgets/sectioned_dataclass_editor.py
class EditorSection(ABC):            # build(editor) -> RenderedSection
class ReadOnlyTableSection(EditorSection)   # title, columns, rows
class FieldSection(EditorSection)           # field_name; header with label and reset
class RowTableSection(FieldSection)         # row_type, new_row, add_label; rows_of / value_of

class SectionedDataclassEditor(QWidget, ...):   # value pair, chrome, title checkbox, rows
    value_type: type
    def sections(self) -> tuple[EditorSection, ...]: ...   # the one thing a subclass declares

# formbridge: formbridge/forms/raw_display_value.py
class RawDisplayValue:   # raw (edited) and display (inherited values resolved), one record
```

```python
# openhcs: declarations only
class SourceBindingsEditorWidget(SectionedDataclassEditor):
    value_type = SourceBindingsConfig
    def sections(self): return (pipeline summary, StepBindingsSection(...),
        RowTableSection("source_filters", SourceFilterClause, ...), ...)
```

- "Attached to a form or standalone" becomes a two-member family of child-field chrome (`InlineDataclassChildChrome`, already in pyqt-reactive, and a standalone member), replacing `_form_context is None` / `_child_chrome is None`.
- "Section rendered or not" becomes membership in one dict of rendered sections, cleared in one statement; the 9 table/controller attributes go.
- "Enable checkbox attached or not" becomes one record of title widgets or its absence, in one place.
- Source visibility (P10 Def 2.1, Prop 6.1): `RawDisplayValue` keeps raw and display together, so "was this field supplied by this config or inherited" stays answerable per field (`shows_inherited`); the resolved-pairing table keeps its Scope column.

**Deleted from OpenHCS:** every generic method in the table above; `SourceBindingsEditorValue`'s per-field properties; `from_bindings`.

## Inventory before creation

Searched pyqt-reactive and formbridge (`grep -rn "class .*\(Enableable\|Section\|RawResolved\|ChangeSignal\)"`, outlines of `forms/inline_dataclass_chrome.py`, `forms/inline_dataclass_context.py`, `widgets/editable_table.py`, `widgets/structural_table.py`, `protocols/widget_protocols.py`, `forms/widget_creation_config.py`):

- Row tables: `EditableTableController`, `DataclassFieldColumns`, `EditableTableLayout`, `EditableTableSemanticBinding` exist. **Used, not duplicated.**
- Child-field chrome with a form: `InlineDataclassChildChrome` exists. **Extended** into a family with a standalone member.
- Title checkbox: `EnabledTitleWidgetMoveAuthority` owns the title-row widgets for form-built checkboxes. **Used**; the part that is new is binding it to a value widget's raw/display pair.
- The contracts (`ValueGettable`, `RawResolvedValueSettable`, `ChildField*`, `InlineDataclass*`, `ChangeSignalEmitter`) exist as ABCs; the only implementer of the inline-dataclass ones is this OpenHCS widget. No implementation exists in either library.
- No existing raw/display value record and no section abstraction in either library.

## Guards

- `tests/unit/pyqt_gui/test_source_bindings_editor_guards.py`: the widget class body defines no method that builds a table, reads `is None`, or names a row field; its size stays under a bound.
- Existing: `tests/unit/test_k4_source_binding_guards.py`, `tests/unit/test_e1_enum_dispatch_guards.py`.

## Tests

`tests/unit/pyqt_gui/test_source_bindings_editor.py` (84 tests) keeps its behavioural assertions; accessors are renamed to the section API. Generic behaviour gets tests in pyqt-reactive and formbridge.

## New-case experiments

Today a new row section needs 4 methods and 5 roster edits in the widget. After: one `RowTableSection` declaration. A new filter kind (a `SourceFilterSubject` / match-type member) or pairing member must appear in the table's choices and be editable with no widget edit; tested by registering a throwaway member.

## Done when

The widget declares sections and domain inputs only; guards, the K4 and E1 guard files, the editor tests, `guardrails rc=0` and `smoke rc=0` pass; library PRs are open.

## Result

Library branches: formbridge `refactor/U6b-raw-display-value`, pyqt-reactive `refactor/U6b-sectioned-dataclass-editor` (needs the formbridge branch).

| | Before | After |
|---|---|---|
| Widget class | 1,388 lines, 77 methods | 192 lines, 8 methods |
| File | 1,999 lines | 661 lines |
| Instance attributes set by the widget | 28 | 2 (`_source_bindings`, `_inventory`) |
| `None` comparisons in the class | 74 | 2 (`self._inventory is None`, `plan is not None`) |
| Lifecycle flags | 2 | 0 (the table controller's own `update_guard`; `QSignalBlocker` on the checkbox) |
| Forwarded methods | 13 | 0 in OpenHCS; 5 in the library, each required by a form contract or used as a query (`value`, `child_field_identity`, `child_field_label`, `child_field_reset_button`, `child_field_navigation_target`) |
| Copies of the row-section code | 3 x 4 methods | 1 (`RowTableSection`) |
| Field rosters | 5 | 0 (the rendered-section dict, filled by `build`) |
| Kind switches | 3 | 1 domain (`isinstance(concrete, StepSourceBindingsConfig)`), 1 library boundary (`form_context is None` in the constructor, which picks the chrome member), 1 library nominal check (`_form_chrome`, which rejects form-only questions on a standalone editor) |

What the OpenHCS widget still holds: its two inputs, `sections()` (the declaration), `suggestions()`, the bindings dialog (`step_bindings_dialog`, `edit_step_bindings`), `set_preview_context`, `resolved_view_inputs`.

### Deletions and their certificates

- **derived** (the mechanism is `SectionedDataclassEditor` and the section family in pyqt-reactive): every generic method in the classification table; the 9 per-section table and controller attributes (now `rendered(field)`, `table(field)`, `row_table(field)`); `_updating_ui` (the controller's `update_guard`); `_table_placeholder_targets`; `from_bindings` (now `for_value`, which reads `value_type`); `create_source_bindings_editor_widget`, `source_bindings_form_context`, `resolved_source_bindings_value`, `register_source_bindings_editor_widget` (now `SectionedDataclassEditor.in_form`, registered directly); `SourceBindingsEditorValue` (now `RawDisplayValue` plus the module function `shown_pipeline_and_step_configs`).
- **unused**: `step_bindings_table`, `step_bindings_editor`, `remove_selected_binding_rows` and the "dialog is open" branch of `add_binding_row`. They were set only while the modal dialog's `exec()` blocked, and the dialog's own editor has its own add and remove buttons. One test asserted `step_bindings_table is None`; that assertion is removed.
- **tests-only**: `in_form` requires `manager` and `param_info`. The old factory accepted either as `None` and built a standalone editor. The form machinery always passes both (all form tests pass); a third-party caller of the registered factory without a manager is what the interface admitted and tests do not exercise. Standalone construction is `for_value`.

### Behaviour changes

- Any row section may declare `refreshes_alone`; only Source Filters does, as before.
- `set_raw_value_with_resolved_preview` with an unchanged raw value and a display value that renders the same rows now refreshes markers only. Before, a config that is not enableable rebuilt every table in that case. The rendered rows are the same.
- When only the enable state changed and the raw value did not, the title checkbox and its markers are refreshed without rebuilding the tables (before: rebuild, from `set_value` only).
- A single-section refresh also re-reads the enable state into the title.
- The profiler phases are named `sectioned_dataclass_editor.show_value` and `.refresh_child_field_chrome` (were `openhcs.source_bindings.*`; nothing read the names).
- The widget's layout attribute is `sections_layout`; it no longer shadows `QWidget.layout()`.
- Error text for a wrong value type now comes from `RawDisplayValue` (`Expected SourceBindingsConfig, got X.`).

### Left for another surface

- `StepBindingsTableEditor` and `StepBindingsDialog` (same file, not this class): a transposed "one record per column" table editor and its dialog. Generic; belongs in pyqt-reactive next to `EditableTableController`.
- `inventory: SourceInventory | None` is the one optional domain input left.

## Progress

- [x] Step 1: classification (this commit).
- [x] Step 2: formbridge `RawDisplayValue`; pyqt-reactive sectioned editor.
- [x] Step 3: OpenHCS widget reduced to declarations; tests renamed.
- [x] Step 4: new-case test and guards (`test_new_filter_and_pairing_members_are_editable_without_a_widget_edit`).
- [ ] Next: move the transposed bindings table editor to pyqt-reactive (not part of this class).
