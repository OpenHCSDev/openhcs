# U3 + L4: Generic Qt machinery leaves OpenHCS

**Head audited:** `openhcs` `main` at `84e7a2904` (#1193); `pyqt-reactive` `main` at `269e896` (0.4.0); `ObjectState` `main` at `c75a457` (1.3.1); `python-introspect` `main` at `4bb7d13` (0.2.5). **Rules:** [00-RULES.md](00-RULES.md). **Step 3** (U3 merges with L4, [04-ARCHITECTURE.md](04-ARCHITECTURE.md#the-ui-one-session-interface-thin-renderers-surfaces-u1-to-u5)).
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* `objectstate.ScopeKey`, `objectstate.inspection`; pyqt-reactive's editable table, grid selector, time-travel widgets, config window, dock and shortcut layout, open `PathCacheKey` and `PathNameRole` families. *Uses:* `AutoRegisterMeta`, `IsomorphicDataclassRowPathPolicy`, `ObjectStateRegistry` subscriptions.

Nothing in this surface had landed before this file was written; there is no closure note.

## What is wrong

**`openhcs/pyqt_gui` (33.9k lines) carries Qt machinery that knows nothing about microscopy, copies of library code, and an event bus beside ObjectState's own change subscriptions; ObjectState and pyqt-reactive restate one scope grammar as `::` string operations at 50 sites.**

Re-measured at `84e7a2904`:

| Item | Lines | Evidence |
|---|---|---|
| `core/path_cache.py` | 199 | Verbatim copy of `pyqt_reactive/core/path_cache.py` cut down to one key, `PLATE_IMPORT`. Both modules build their own `UnifiedPathCache` over the same file (`reactor_providers.py:319` points the library at OpenHCS's `path_cache.json`), so each overwrites the other's entries. The library's `PathCacheKey` enum (17 members) restates OpenHCS's file kinds (`FUNCTION_PATTERNS`, `PIPELINE_FILES`, `STEP_SETTINGS`, `DEBUG_FILES`, six `*_BROWSER` keys), most unused, plus four "backward compatibility alias" functions. `PathNameRole` (`enhanced_path_widget.py:176`) is an enum with behaviour whose `PIPELINE`/`STEP`/`FUNCTION` members name OpenHCS pickle formats F1 deleted. |
| `core/xdg_paths.py` legacy migration | ~210 | `migrate_all_legacy_cache_files`, `migrate_cache_file`, `migrate_cache_directory`, `get_legacy_openhcs_dir` and a legacy fallback inside each `get_*_file_path` move files out of a pre-XDG `~/.openhcs` (rule 1; F1 recorded the path-cache case for L4). |
| Editable table in `widgets/source_bindings_editor.py:136-1454` | ~1,320 | C3 left it in place "owned by L4": the `CellEditor` family, `DataclassFieldColumn(s)`, `RowSuggestion`, `StructuredSelectorCellWidget`/`Dialog`, `EditableTableProgrammaticUpdateGuard`, `EditableTableItem`, `EditableTableController`, `EditableTableLayout`. Its only OpenHCS import is `core/field_label.FieldLabel`, a generic `Annotated` label marker. |
| Header-timer leak | — | `ManagerStatusController._restart_scrolling` (`pyqt_reactive/widgets/shared/manager_status_controller.py:117`) stops the old marquee timer and drops the reference, but the `QTimer` stays a child of the manager widget; every status message too wide for the header adds one more live child object for the widget's lifetime. |
| Grid selector `widgets/shared/plate_view_widget.py` | 1,278 | Generic grid-of-buttons selection (bounds, click/drag/rectangle/row/column/invert, aspect-ratio container). Domain ties: six calls of `require_grid_axis()` (`:155,185,203,1130` and the noun at `:522,526,982,1026`), the "Plate View" title, and a subdirectory selector whose `active_subdir` nobody reads (`:851`). `partition_filter_widget` is never assigned, so `sync_to/from_partition_filter` (`:497-514,1272-1278`) is dead. Three enums dispatch behaviour through side tables (`PlateSelectionEventTarget` → `EVENT_ROUTE_BY_KEY` `:727`, `PlateSubdirectoryMode` → `MODE_HANDLERS` `:297`, `WellButtonState` → `WELL_BUTTON_STYLE_COLORS` `:72`; rule 1a). |
| Time travel | ~1,150 | `widgets/shared/time_travel_widget.py` (373), `windows/snapshot_browser_window.py` (268), `services/time_travel_navigation.py` (182), `MainWindowTimeTravelWorkflow` and `TimeTravelShortcutEventFilter` (`main_window_workflows.py:87-109,853-907`), and the navigation driver in `main.py:1105-1255`. Domain ties: the hidden `"__plates__"` scope written twice (`time_travel_widget.py:49`, `snapshot_browser_window.py:92`), `parse_function_scope_ref` parsing `functionstep_` tokens out of `::` strings (`:75-89`), and the dual-editor tab choice (`main.py:1257-1282`). |
| Config windows | ~1,370 | `windows/config_window.py` (844) is generic apart from the `""`→`global_config` window-id alias (`:487-490`) and its code-document renderer; `config_edit_session.py` (168) imports one OpenHCS helper (`LazyDataclassFieldEmissionState.retain_only_authored_paths`, which uses only ObjectState); `services/config_window_code_document.py` (85); `ui/shared/code_editor_form_updater.py` (269, ObjectState only). `OPENHCS_USE_EXTERNAL_EDITOR` is read in three places, two of them inside pyqt-reactive (`function_list_editor.py:1089`, `manager_action_controller.py:208`). |
| Dock and shortcut layout | ~420 | `MainWindowDockFloatController`, `MainWindowDockPane`, `MainWindowDockLayoutStore`, the generic half of `MainWindowEmbeddedWidgets`, `QtShortcutSequenceAuthority`, `CodeEditorFocusAuthority`, `MainWindowShortcutLifecycle` (`main_window_workflows.py:59-195,270-612`). |
| `GlobalEventBus` | ~100 | `services/service_adapter.py:22-32`, `GuiEventBusBroadcaster` (28), emitted at `pipeline_editor.py:391,614` and `plate_manager.py:342`, received only by `DualEditorWindow` (`:701-876`). `pipeline_changed` restates the `{plate}::pipeline` ObjectState's `step_scope_ids`; `config_changed` re-notifies a write the session already made to scope `""`. pyqt-reactive's `AbstractManagerWidget` requires `get_event_bus()` and never reads it (`abstract_manager_widget.py:690`). |
| `::` scope grammar | 50 sites | Join child, root, parent, ancestors, is-descendant, depth and last-token are written by hand in ObjectState (`object_state_registry.py:435,647,699,820,1366`; `object_state.py:698,2319,2463`; `context_manager.py:344,379`), pyqt-reactive (17 sites; `scope_token_service.py:447` matches `/plate1` as a parent of `/plate10`) and OpenHCS (`SCOPE_SEGMENT_SEPARATOR` and 20 sites). |
| ObjectState inspection | ~400 | `ObjectStateFieldSemanticProjection` (`ui_bridge_object_state.py:237-516`) and the provenance effects (`:181-234`) read raw/resolved values, dirty and signature state, provenance and type names with only ObjectState and python-introspect; the `*`/`_` marker rule is written four times (`ui_bridge_windows.py:201,257,1938`, `ui_bridge_object_state.py:~312`). |
| View state outside ObjectState | — | ObjectState has no field that is excluded from history and dirty detection. Session selection (`session.py:322-326`) and widget selections live on plain attributes. |
| Dead ObjectState API | 19 + params | `objectstate.history_migration.HistoryMigration` and the `migration=` parameter of `import_history_from_dict`/`load_history_from_file` have no consumer after U5 (recorded by U5). |

## Target

- **python-introspect 0.2.6:** `FieldLabel` and `declared_field_label` beside `AnnotationChoices`. `openhcs/core/field_label.py` is deleted.
- **ObjectState 1.4.0:**
  - `ScopeKey(str)` owns the scope grammar: `ScopeKey.of(*parts)`, `child`, `parent`, `root`, `ancestors()`, `contains`, `strictly_contains`, `depth`, `last`, `parts`, and `SEPARATOR` (declared once). Registry keys are `ScopeKey`s; every `::` operation in the three code bases calls it (`get_root_from_scope_key` and `is_scope_affected`, which nothing called, are deleted). It is a `str` subclass, so history documents and dict keys keep their encoding.
  - `objectstate.inspection`: `FieldInspection` (raw and resolved value, edit state, inheritance, provenance, type names) and `field_markers`/`state_markers`, the one owner of the `*`/`_` rule. The bridge's `ObjectStateFieldSemanticProjection` inherits `FieldInspection` and adds only its DTO projection.
  - `retain_only_authored_paths` (moved from OpenHCS's serializer; it touches only lazy-dataclass metadata), `ObjectStateRegistry.MAIN_BRANCH` and `is_restoring_snapshot()` (pyqt-reactive read `_in_time_travel` privately).
  - `HistoryMigration` and `migration=` are deleted; a history whose `format_version` is not current is refused.
- **pyqt-reactive 0.5.0:**
  - `core/path_cache.py`: `PathCacheKey` is an open `AutoRegisterMeta` family whose stored key is the snake-case class name (`General`, `FileSelection`, `DirectorySelection`, `CodeEditor`); `PathNameRole` is a family (`DirectoryPathRole`, `FilePathRole`). The alias functions, unused keys and the pipeline/step/function roles are deleted. OpenHCS declares `PlateImport(PathCacheKey)` beside its one use.
  - `ManagerStatusController` owns one marquee timer and restarts it (the header-timer leak).
  - `widgets/editable_table.py`: the editable table block, unchanged except the label lookup through `declared_field_label`.
  - `widgets/grid_selector.py`: `GridSelectorWidget` over a `GridAddressing` ABC; cell looks and event targets are class families. OpenHCS's `GridAxisAddressing` adapts the `GridAddressed` axis (the kernel cannot subclass a Qt-library ABC).
  - `widgets/time_travel.py` (`TimeTravelCommands`, `TimeTravelWidget`), `windows/snapshot_browser_window.py`, `services/time_travel_navigation.py` (`TimeTravelNavigator`; `FieldPathTarget`/`FunctionTokenTarget` replace a kind string). OpenHCS supplies the hidden dataset-list scope, `step_function_scope` (through `StepEditorScope`, not a second `functionstep_` parser) and the dual-editor tab choice.
  - `windows/config_window.py` (`ConfigWindow`, `ConfigEditSession`, `ConfigCodeDocumentDriver`, `ConfigDocumentFormat` ABC), `services/code_editor_form_updater.py`, and `use_external_code_editor()` reading `FormGenConfig.external_editor_env_var`. OpenHCS keeps `OpenHCSConfigWindow` (document format adapter over `ConfigDocumentAuthority`, global-config window id).
  - `widgets/shared/dock_layout.py` (`DockPane`, `DockFloatController`, `DockPanes`, `DockLayoutStore`) and `services/application_shortcuts.py` (`ShortcutLifecycle[ConfigT]`). OpenHCS keeps the window specs, the dock topology and `MainWindowEmbeddedWidgets(DockPanes)` naming its panes.
  - `AbstractManagerWidget` stops reading `get_event_bus()`; `PatternDataManager.extract_func_and_kwargs` raises on a malformed entry (recorded by U5).
- **`GlobalEventBus` is deleted.** ObjectState already had the change subscriptions; what the bus restated were the session's own events. `DualEditorWindow.connect_session_events(session)` follows `PipelineChanged`/`PipelineImported` for its plate and `GlobalConfigChanged`, and follows its pipeline after a restore; `GuiEventBusBroadcaster` and `get_event_bus` are deleted.

## Corrections to the plan

- **View fields were not built.** At this head nothing needs a field excluded from history and dirty detection: U1 moved session state onto `Session`, the remaining widget view state (selection, current tab) has one owner each, and `ObjectState.metadata` contracts already hold state outside dirty detection. A mechanism without a consumer would be speculative; it belongs to the first surface with a consumer.
- **The UI-bridge server and window introspection did not move** (see Reassigned): they speak the bridge DTOs and the `UiBridgeOperation` family, which U4 moves first.
- The change subscription that replaces `GlobalEventBus` is the session's event log (U1), not a new ObjectState API.

## Persisted state

- `path_cache.json` (runtime convenience): stored keys are derived from class names and equal the old enum values for the kept contexts (`plate_import`, `general`, `file_selection`, `directory_selection`, `code_editor`), so the file loads unchanged.
- ObjectState history files (runtime state, reset on upgrade per U5): scope ids keep their `::` text.
- QSettings dock layout (`main_window/dock_layout_state`, version 2): key and version unchanged.
- `OPENHCS_USE_EXTERNAL_EDITOR` keeps its name (OpenHCS's form config declares it).

## Guards

`tests/unit/pyqt_gui/test_generic_qt_machinery_guards.py`:
- the ten moved modules do not exist; no module under `openhcs/` defines a moved name (`GlobalEventBus`, `get_event_bus`, `CellEditor`, `EditableTableController`, `MainWindowDockPane`, `MainWindowShortcutLifecycle`, `TimeTravelWidget`, `PlateViewWidget`, `ConfigEditSession`, `CodeEditorFormUpdater`, …);
- no `::` scope literal (exactly `::`, or a string starting or ending with it) and no `SCOPE_SEGMENT_SEPARATOR` in `openhcs/`, `external/ObjectState/src` or `external/pyqt-reactive/src` outside `objectstate/scope_key.py`; three external spellings are exempt (the `local::` execution id, IPv6 `::1`, a reStructuredText directive regex);
- `xdg_paths.py` defines no `*legacy*`/`migrate_*` name; the path, grid and time-travel library families define no `Enum`;
- `OPENHCS_USE_EXTERNAL_EDITOR` is named only in `reactor_providers.py`; no `pyqt_gui` module appends a `*`/`_` marker by hand.

## Tests

- Library: `test_path_name_roles.py` (an application-declared context round-trips through the file), the marquee leak (one timer after twenty long messages; fails without the fix), `test_scope_key.py` (`/plate1` vs `/plate10`), `test_inspection.py`, `test_authored_paths.py`, and moved tests for the editable table, grid selector, time travel, config window, dock layout, shortcuts and form updater with stub domain adapters.
- OpenHCS: the source-binding editor, config-window, time-travel navigation, plate-manager, pipeline-editor and UI-bridge tests keep their assertions against the moved classes; the `GlobalEventBus` wiring tests are replaced by dual-editor tests driven by session events.

## New-case experiments

- A new remembered dialog context: today an enum member in OpenHCS's copy or in the library. After: one `PathCacheKey` subclass where it is used.
- A new editable record table in any pyqt-reactive application: today copy 1,320 lines out of OpenHCS. After: `EditableTableController(table, DataclassFieldColumns.of(Row), ...)`.
- A non-microscopy grid (remote-sensing tiles): today the widget calls the microscopy-shaped `require_grid_axis()`. After: one `GridAddressing` subclass.
- A new child-scope rule (`parent`, `is within`): today a hand-written `split("::")`. After: a `ScopeKey` method call.

## Done when

The guards pass; the three library PRs are open; OpenHCS points its submodules at the library branch heads and its UI tests pass offscreen; the structural ratchet and NRA show no regression.

## Reassigned

| Item | Evidence | Belongs to |
|---|---|---|
| UI-bridge server and window introspection (`ui_bridge_server.py` 623, the generic parts of `ui_bridge_windows.py` ~2.3k and `ui_agent_bridge.py` ~1.1k) | Every result factory returns `openhcs.agent.dto.ui_bridge` types and `AgentError`; the server dispatches through `openhcs.agent.services.ui_bridge_service.UiBridgeOperation`. Moving them into pyqt-reactive first would ship ~2.9k lines of DTO and contract code inside a Qt package, which U4 then moves out again. | U4 (DTO and contract tier first, then the Qt server beside it) |
| Bridge widget ids (`plate_manager`) and `WorkflowTerminalStateCriterion` (recorded by U2) | bridge descriptor vocabulary | U4, with the bridge |
| `PyQtServiceAdapter.get_current_color_scheme` as a library protocol (recorded by U5) | called by pyqt-reactive `abstract_manager_widget.py:685` | U4 (service-adapter protocol in the toolkit-neutral tier) |
| pyqt-reactive `PatternDataManager.extract_func_and_kwargs` returns `(None, {})` for a three-member tuple (recorded by U5) | `pattern_data_manager.py:120` | done here: it raises `TypeError` |
| `QApplication` teardown segfault after the main window closes (recorded by U5) | 1 in 5 runs, no Python frame | not investigated here; U4 (generic Qt lifecycle) |
