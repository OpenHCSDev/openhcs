# U6c: The image browser declares; pyqt-reactive browses

**Head audited:** `openhcs` `main` at `ae6ddace5` (#1210); `pyqt-reactive` at `4991fc7` (0.6.0). **Rules:** [00-RULES.md](00-RULES.md). **Brief:** `.claude/verify/U6-COMMON.md`.
**Shared abstractions.** *Builds (pyqt-reactive):* `RowFilter`, `RecordTableBrowser` with `ValueLabels`, `FolderTreeWidget`, `GridColumnFilterLink`, `DetachablePanel`, `ConfigActionTabs`. *Uses:* `AbstractTableBrowser`, `ColumnDef`, `GridSelectorWidget`, `TabbedFormWidget`, `AxisFamily.with_role`, the `StreamingConfig` registry, `ResultFileFormat.open_with`.

## What is wrong

**`ImageBrowserWidget` (`openhcs/pyqt_gui/widgets/image_browser.py`, 1,560 lines; class 1,138 lines, 46 methods) is a table-of-records browser, a folder tree, a detachable grid panel, a config-action tab strip and a streaming client written as one Qt class, with the missing dataset, the missing grid axis and the row kind each encoded as `None`.**

Measured at `ae6ddace5`: 29 `is None`/`is not None` checks in the file; 10 `if self.orchestrator` mode checks; 5 `if self.plate_view_widget`/`plate_view_detached_window` checks.

### Classification (46 methods)

| Concern | Kind | Methods | n |
|---|---|---|---|
| Layout of search row, splitters | generic Qt | `init_ui` | 1 |
| Folder tree built from record keys, selection kept across rebuilds, folder filter | generic Qt | `_create_folder_tree`, `_build_folder_tree`, `_restore_folder_selection`, `on_folder_selection_changed` | 4 |
| Record table: columns, visible rows, status text | generic Qt | `_create_table_widget`, `_set_visible_files` | 2 |
| Focus a row by path | generic (forwarder) | `focus_file_by_path` | 1 |
| Panel shown in a splitter or its own window | generic Qt | `_toggle_plate_view`, `_detach_plate_view`, `_reattach_plate_view`, `_on_detached_window_closed` | 4 |
| Grid selection kept equal to one column filter; cells offered from rows | generic Qt | `_on_wells_selected`, `_on_table_filter_selection_changed`, `_update_plate_view`, `_extract_well_id` | 4 |
| One tab and one action button per nested config; button enabled by `<field>.enabled` and a selection; live baseline | generic Qt | `_create_right_panel`, `_rebuild_right_panel`, `_on_parameter_changed`, `_on_files_selected` | 4 |
| Status text set from worker threads | generic Qt | `_update_status_threadsafe`, `_update_status_label`, `_show_streaming_error` | 3 |
| **Generic total** | | | **23** |
| Dataset (orchestrator) binding and ObjectState scope | domain | `__init__`, `filemanager`, `streaming_service`, `_create_state_for_orchestrator`, `_replace_state_for_orchestrator`, `set_orchestrator`, `cleanup` | 7 |
| Viewer-instance panel and process config | domain | `_create_instance_manager_panel`, `set_zmq_config`, `set_progress_config`, `set_ui_config` | 4 |
| Inventory records to rows | domain | `load_images`, `load_results`, `_items_from_file_records`, `_result_items_from_inventory` | 4 |
| Opening and streaming a selection | domain | `_on_file_double_clicked`, `_handle_image_double_click`, `_handle_result_double_click`, `_view_selected_in_viewer`, `_prepare_streaming`, `_stream_images_to_viewer`, `_stream_rois_to_viewer`, `_stream_roi_file` | 8 |
| **Domain total** | | | **23** |

Attributes (26 assigned in `__init__`/`init_ui`): 14 generic widget handles and view state (`search_input`, `folder_tree`, `image_table_browser`, `plate_view_widget`, `plate_view_detached_window`, `plate_view_toggle_btn`, `middle_splitter`, `main_splitter`, `right_panel`, `tabbed_form`, `view_buttons`, `refresh_btn`, `info_label`, `_syncing_plate_filter_selection`), 4 helper objects that forward (`viewer_controls`, `metadata_display_resolver`, `filter_controller`, `file_focus_controller`), 8 domain (`orchestrator`, `_state_scope_parent_id`, `_zmq_config`, `_progress_config`, `config`, `scope_id`, `state`, `zmq_manager`), plus restated or dead state: `file_items` (copy of the table's `all_items`), `metadata_keys` (copy of the table's columns), `selected_wells` (second owner of the grid filter), `_fallback_filemanager`, `_streaming_service_cache`/`_streaming_service_orchestrator`.

### Restated relations and modes

- **Dataset absent is `orchestrator is None`** (10 checks). Two cases with different answers (scope, parent state, records, ports, streaming) share one representation told apart by a null test (P1 Thm 4.8).
- **Row kind is optional fields** on `ImageBrowserItem` (`file_kind`, `streamable_image_path`, `result_file_type`, `full_path`), re-decided at `_on_file_double_clicked`, `_view_selected_in_viewer` and `result_path` (P1 Prop 3.1, Thm 3.2).
- **The grid selection has two owners**: the table's column filter and `selected_wells`, kept apart by the flag `_syncing_plate_filter_selection` (P10 Prop 2.2).
- **The detached window is a `None` mode** with the reattach body written twice (`_reattach_plate_view`, `_on_detached_window_closed`; P1 Thm 4.7).
- **Four helper classes hold `browser` and are reached by forwarding** (`filter_controller`, `file_focus_controller`, `viewer_controls`, `metadata_display_resolver`); `ImageBrowserFilterController` and `ImageBrowserFileFocusController` read 9 browser attributes back (P1 Thm 4.3).
- **The library table names microscopy columns**: `ImageTableBrowser._COLUMN_WIDTHS` keys `channel`, `site`; the browser hard-codes `"filename"` and `"extension"`.
- **The display resolver returns a bare string**; the axis that supplied a label is not recoverable from a cell (P10 Def 2.1, Prop 6.1).
- **Dead:** `image_selected` signal, `_update_status_threadsafe`, `load_results`, `_result_items_from_inventory` (tests only), `_fallback_filemanager` (read only when an orchestrator exists, where it is not used).

## Inventory before creation (pyqt-reactive at `4991fc7`)

| Searched for | Found | Decision |
|---|---|---|
| table of mapping rows | `ImageTableBrowser(AbstractTableBrowser)` | renamed `RecordTableBrowser`; columns are declared `ColumnDef`s, not metadata keys |
| composing search with other row filters | `AbstractTableBrowser.set_filtered_items` (caller computes the set) | `RowFilter` ABC on the same class; it feeds `set_filtered_items` |
| folder/tree view | `config_hierarchy_tree`, `tree_state_adapter`, `tree_rebuild_coordinator` (config hierarchies, ObjectState scopes) | none for path keys; new `FolderTreeWidget` |
| detach to window | `TearOffTabWidget`/`FloatingTabWindow` (tabs), `DetachableActionBar` (reparents a bar), `DockFloatController` (QDockWidget) | none for a splitter child; new `DetachablePanel` |
| grid selector | `GridSelectorWidget`, `GridAddressing` | reused; new `GridColumnFilterLink` joins it to a table column |
| tab per nested config with header widgets | `TabbedFormWidget(header_widgets=...)` | `ConfigActionTabs(TabbedFormWidget)` adds the action buttons |
| value label cache | none | `ValueLabels`, `LabelledValue` |

## Target

- **pyqt-reactive:** the six owners above. A labelled cell is a `LabelledValue(column_key, raw, label, source)`: the declaration that supplied the label travels with it (P10 Prop 6.1).
- **OpenHCS `image_browser.py` declares:**
  - `BrowsedDataset` state family: `NoDataset`, `OrchestratorDataset` (scope, parent state, records, ports, streaming).
  - `BrowsedFile` row family: `ImageFile`, `ResultFile`; each says how it opens and what it adds to a viewer batch. `ResultFile` opens through `ResultFileFormat.open_with`.
  - Columns derived from `AxisFamily.active()` and the record's own fields; each axis column is named by the axis's `label`.
  - Grid panels: one per axis in `family.with_role(GridAddressed)`; none when the family declares none (no `None` widget).
  - Viewer tabs and buttons derived from `StreamingConfig.supported_config_keys()`.
- **Deleted:** `ImageBrowserItem`, `ImageBrowserViewerControls`, `ImageBrowserMetadataDisplayResolver`, `ImageBrowserFilterController`, `ImageBrowserFileFocusController`, `StreamingViewerField`, `streaming_viewer_fields`, `active_grid_axis`, `require_grid_axis`, `selected_wells`, `_syncing_plate_filter_selection`, the dead names above.

## Guards

`tests/unit/test_u6c_image_browser_guards.py` (AST): the module names no microscopy axis string; `ImageBrowserWidget` has no `is None` test and no attribute assigned `None`; no QTreeWidget/QDialog construction in the module; the deleted names stay deleted.

## Tests

Library: row filters, folder tree, grid link, detachable panel, config action tabs, labelled values. OpenHCS: one browser test under Microscopy, the same under the remote-sensing witness. The controller tests coupled to fake browsers are deleted.

## New-case experiment

With `RemoteSensing` active (no `GridAddressed` axis; axes scene, tile, band, date) the browser shows columns and filters for those axes and no grid panel, with no widget edit.

## Done when

Guards pass; G6 viewer guards and `test_k8_materialization_guards.py` pass; `guardrails rc=0`; smoke passes; pyqt-reactive suite passes.

## Result

`image_browser.py`: 1,560 → 702 lines; `ImageBrowserWidget` 1,138 lines / 46 methods → 246 lines / 14 methods. Production (`openhcs/`) −1,379 +538. pyqt-reactive PR OpenHCSDev/PyQT-reactive#24 (+917 −121, no version bump); the submodule points at its branch head.

Removed, by kind:

- **`None` modes (5):** absent dataset (`orchestrator is None`, 10 checks → `NoDataset`/`OrchestratorDataset`); absent grid (`plate_view_widget = None` → one `AxisGrid` per `GridAddressed` axis, possibly none); detached window (`plate_view_detached_window` → `Docked`/`Floating`); row kind (`streamable_image_path`/`result_file_type`/`full_path` optionals → `ImageFile`/`ResultFile`); lazily built `tabbed_form`/`zmq_manager`/splitter handles. `is None` checks in the file: 29 → 2 lines, both in `BrowsedFile.of`, the one boundary that reads `PlateFileRecord`.
- **Flags (3):** `_syncing_plate_filter_selection`; `scope_id = None` as "already released" (the widget becomes `NoDataset`); `_streaming_service_orchestrator` cache key (`cached_property` on the dataset).
- **Forwarding helper classes (4)** and the forwarded methods through them (`focus_file_by_path` → controller, `filter_images` → `apply_combined_filters`, `view_buttons` alias, resolver getter lambda).
- **Kind switches (3):** double-click on `streamable_image_path`/`is_result`; batch selection on `is_result and result_file_type.streams_rois` (now `ResultFileFormat.open_with` into `ViewerBatch`); `isinstance(inventory, PlateFileInventory)` in `_result_items_from_inventory`.
- **Second owners (3):** `selected_wells`, `file_items`, `metadata_keys`.

### Deletion certificates

| Deleted | Certificate |
|---|---|
| `selected_wells` and `_matches_wells` | derived: the column filter owns the selection (`GridColumnFilterLink`). The fallback ran only when the table had no column for the grid axis, where every row failed the well lookup and the grid offered no cell to select. |
| `_fallback_filemanager`, `filemanager` property | unused: read only by `streaming_service`, which returned early without an orchestrator. |
| `image_selected` signal, `_update_status_threadsafe`, `load_results`, `_result_items_from_inventory` | unused in production (the last two had test callers only). |
| `ImageTableBrowser._COLUMN_WIDTHS` (pyqt-reactive) | contract: the kernel and libraries name no microscopy axis (G1). Axis columns take width 70 when `OrdinalValued`; `extension`, `size`, `time`, `timestamp` lose their fixed widths. |
| `orchestrator=None` default, optional `color_scheme`/`progress_config` | derived: every caller passes them; absence of a dataset is `NoDataset`. |
| the widget's own search `QLineEdit` and its stylesheet | derived: the table's `search_input` is the one search box, moved into the header row. tests-only for the look of the box (application theme instead of the inline stylesheet). |
| `state_scope_parent_id` | derived: `OrchestratorDataset.scope_parent`, required. |

### Behaviour changes

- Status line reads `Showing f/t files` (was `Files: f/t`, overwritten by the library's text after a column-filter change).
- Default column order: file name, the family's axes in family order, then the other record fields alphabetically (was all keys alphabetically with `extension` first). Axis columns are headed by `axis.label`.
- The grid panel and its button are titled from the axis label (`Well Grid`), not `Plate View`.
- A column filter that admits every value shows as no selected grid cell.
- `set_items` keeps the search text.
- A viewer batch names ROI archives by full path (double-click already did).
- Streaming errors reach the UI through a signal on the UI thread; the empty-dataset label reads `0 files loaded (0 images, 0 results)`.
- A load failure leaves the summary at zero files after the warning box.

### Out of scope, found

- `PlateFileRecord` (`core/plate_image_inventory.py`) is a kind enum plus optional fields; it should be a record family so `BrowsedFile.of` needs no null tests. Owner: U2 (it already holds the `PlateFileKind` entries in `test_e1_enum_dispatch_guards.py`).
- `tests/pyqt_gui/test_managed_windows.py`: two tests fail on `main` too (`_PlateManagerStub` lacks `_get_current_orchestrator`; `PlateManagerWindow` has no `_setup_connections`). Owner: the surface that owns `windows/managed_windows.py`.
- `AbstractTableBrowser.reveal_key` keeps the old behaviour that an active column filter can still hide the revealed row.
- `function_selector_dialog.py` computes its own filtered set and calls `set_filtered_items`; it could declare `RowFilter`s. Owner: the surface that owns the function selector.
- `scripts/smoke_installed_gui` fails on `main` at `ae6ddace5` with `FunctionCatalogEndpointUnavailableError` (function catalog control timeout).
