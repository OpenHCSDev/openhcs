# U6: GUI integration (one library shape per concept, one OpenHCS PR)

Supersedes #1216 (U6a, dual editor), #1215 (U6b, source bindings editor) and #1218 (U6c, image
browser). Their receipts (`U6a-dual-editor.md`, `U6b-source-bindings-editor.md`,
`U6c-image-browser.md`) stay valid for what each surface did; this one records what changed when the
three met.

Libraries: pyqt-reactive `release/0.7.0-gui-machinery` (PR OpenHCSDev/PyQT-reactive#27),
formbridge `refactor/U6b-raw-display-value` (0.1.1, unchanged).

## What is wrong

Three agents moved generic machinery into pyqt-reactive independently. The merged release branch
held three contradictions.

| # | concept | shape A | shape B |
|---|---|---|---|
| 1 | table columns | `ColumnDef` (U6c browser) | `columns: tuple[str, ...]` plus `rows: tuple[tuple[str, ...], ...]` (U6b `ReadOnlyTableSection`, `TupleSummarySection`) |
| 2 | `owns_field_path` | `(field_path) -> bool` callable given to `FieldWindowNavigationDriver`, default "accept everything" | `ObjectStateNavigationTargetAuthority.owns_field_path(state, field_path)` |
| 3 | a field path claimed by several owners | `ConfigWindow`: not accepted, silently | `TabbedEditorWindow`: the later tab wins |

Supply map (`--package pyqt_reactive --package formbridge`, 240 modules, 1075 classes): no glued
`<Type><Mechanism>` driver in either library (`glued.md` lists 4 names, none a navigation driver);
`twins.md`, `copies.md` report nothing in the three concepts; `forwarders.md` lists
`ConfigWindow -> self.active_tab` (4 members), part of the deferred `ConfigWindow` surface below.

### What the dual editor's tabs actually do (contradiction 3)

Measured on the merged tree, a live `DualEditorWindow` over a `FunctionStep`:

- the step's ObjectState has a `func` parameter;
- the step form builds 12 widgets and none is `func` (the form structure hides it);
- before this change the step tab's driver accepted `func`, `func.0` and `func.token:...` anyway,
  because the form answered "is it mine" from every parameter of its ObjectState;
- the function tab accepts the same three paths from `FunctionPatternField`.

So the overlap was apparent only. The step form claimed a field it does not show. The later-tab rule
was compensating for that wrong claim; no real case needs two owners of one path.

## Target (done)

1. **One column declaration: `ColumnDef`.** It gains `value` (what a row shows in the column; the
   row attribute named `key` when left out). `ReadOnlyTableSection` and `TupleSummarySection` take
   `ColumnDef` columns and row records, so a header and its cell are one declaration instead of two
   positions in parallel tuples. `AbstractTableBrowser.extract_row_data` is derived from the columns;
   the snapshot and function browsers drop their positional overrides. `DataclassFieldColumn.read_only()`
   derives the read-only column of an editable field (label and shown text from the field's
   declaration). The tuple shape is deleted.
2. **One `owns_field_path(field_path) -> bool`, asked of the thing that shows the fields.**
   `ParameterFormManager.owns_field_path` (was `owns_navigation_field_path`) answers from the form's
   own form structure. A config tab answers from its config's parameters (it is asked before its form
   exists). `FieldWindowNavigationDriver` requires the callable; the accept-everything default is
   gone. `ObjectStateNavigationTargetAuthority` is deleted. No driver negates another's fields and
   there is no per-domain driver class.
3. **One rule, in `pyqt_reactive.services.window_navigation.sole_owner`: several claims on one
   target raise `NavigationTargetClaimedTwiceError` naming the claimants.**
   `CompositeWindowNavigationDriver` (so `TabbedEditorWindow`) and `ConfigWindowNavigationDriver`
   both call it. `TabbedEditorNavigationDriver` no longer overrides the match to pick the last tab.

## OpenHCS call sites changed

- `openhcs/pyqt_gui/widgets/source_bindings_editor.py`: seven read-only tables declare `ColumnDef`
  columns over the records themselves (diagnostics, preview rows, bindings); four static column sets
  are module constants; the pipeline-bindings table derives its columns from `NamedSourceBinding`'s
  fields with `read_only()`.
- `pyproject.toml`: `pyqt-reactive>=0.7,<0.8`, `formbridge>=0.1.1,<0.2`.
- `tests/unit/pyqt_gui/test_config_window_state_resolution.py`: `save_button` / `header_label`
  (renamed by the release branch); the ambiguous-field case now expects the raise.
- `tests/unit/pyqt_gui/test_dual_editor_window.py`: asserts the step form does not claim `func`.
- No change was needed in `dual_editor_tabs.py` or the image browser.

`StepFieldNavigationDriver`, `FunctionFieldNavigationDriver` and `DualEditorWindowNavigationDriver`
exist nowhere in code (they are named only in the U6a receipt's history).

## Deletion certificates

- tuple `columns`/`rows` on the two sections: **contract** (first-party lockstep, no compatibility
  shape); every caller moved.
- `SnapshotTableBrowser.extract_row_data`, `FunctionTableBrowser.extract_row_data`: **derived**
  (`AbstractTableBrowser.extract_row_data` from `ColumnDef.value`). The function browser's per-row
  type check in `extract_row_data` is covered by the check `set_items` / `set_filtered_items` already
  make on every row.
- `ObjectStateNavigationTargetAuthority`: **derived** for config tabs (`_ConfigEditorTab.owns_field_path`
  is the same expression).
- A form accepting navigation to a state parameter it does not show: **tests-only**. The interface
  admits any hidden parameter of any form; the tests exercise `func` in the step editor and the
  forms in `tests/unit/pyqt_gui`. Such a path had no widget to scroll to.
- `FieldWindowNavigationDriver`'s accept-everything default: **contract** (the owner's rule: a
  positive answer from declared fields).
- Later-tab-wins in `TabbedEditorNavigationDriver`: **tests-only** for third-party tab families; in
  this tree the only family with two field-showing tabs is the step editor, measured above.
- `ConfigWindow` silent rejection of an ambiguous path: **contract** (refuse loudly). Only a request
  that names none of the tabs' states and a path two tabs share reaches it.

Kept and reported: `FormFieldWindowNavigationDriver` still accepts any path while its form does not
exist yet (readiness then waits for the form). Removing it could not be certified.

## Guards and tests

See "Results" in the PR body for observed numbers. Guards and new-case tests are those named in the
three surface receipts, plus:

- pyqt-reactive `tests/test_tabbed_editor_window.py::test_two_tabs_claiming_one_field_path_is_a_declaration_error`
- pyqt-reactive `tests/test_sectioned_dataclass_editor.py::test_a_read_only_table_shows_each_row_through_its_columns`

## Follow-up surfaces (pre-existing duplicates, not done here)

Sizes are members declared on the class, from the supply map's `owners.json`.

| surface | classes (declared members) |
|---|---|
| three float mechanisms | `DetachablePanel` 6 + `_FloatingPanelWindow` 2; `TearOffTabWidget` 14 + `TearOffTabBar` 5 + `FloatingTabWindow` 6; `DockPane` 12 |
| two table stacks | `EditableTableController` 40 + `DataclassFieldColumns` 15 + `DataclassFieldColumn` 14; `AbstractTableBrowser` 49 + `ColumnDef` 10 + `ColumnPresentationState` 10 |
| two tab containers | `TabbedFormWidget` 10 + `ConfigActionTabs` 6; `ActionTabbedWindowBody` 24 |
| `ConfigWindow` is its own tabbed editor | `ConfigWindow` 34 + `_ConfigEditorTab` 17 + `ConfigWindowTabSpec` 6 + `ConfigWindowNavigationDriver` 4 + `_ActiveConfigCodeDocumentDriver` 4, beside `TabbedEditorWindow` 23 + `EditorTab` 11 + `TabbedEditorNavigationDriver` 3 |

The two table stacks now share the column declaration for read-only tables only
(`DataclassFieldColumn.read_only()`); the editable stack still has its own column type.
