# U6a: decompose `DualEditorWindow`

Measured at origin/main `ae6ddace5`.

## What is wrong

`openhcs/pyqt_gui/windows/dual_editor_window.py` is 1,310 lines. `DualEditorWindow(BaseFormDialog)` is
1,081 lines; the file holds 51 `is None` checks. The window class owns generic concerns that
pyqt-reactive's `ConfigWindow` owns a second time, and it names its three tabs in every one of them.

### Classification of the class (methods, closures included)

| Kind | Count | Members |
|---|---|---|
| generic: tabs over a form | 5 | `setup_ui`, `setup_connections`, `on_tab_changed`, `form_managers`, `state` |
| generic: dirty / save / cancel | 14 | `_refresh_dirty_title_state`, `dirty_window_widgets`, `dirty_window_presentation`, `_apply_dirty_window_presentation`, `_update_window_title`, `_update_save_button_text`, `managed_window_action_capabilities`, `agent_save_managed_window`, `save_edit`, `cancel_edit`, `require_managed_state_mutation_allowed`, `before_managed_reject`, `after_managed_reject`, `before_managed_close` |
| generic: navigation to a field path | 2 (+9 in `DualEditorWindowNavigationDriver`) | `select_and_scroll_to_field`, `window_navigation_driver` |
| generic: time-travel hooks | 4 | `_connect_time_travel_title_refresh` and its two closures, `_refresh_after_time_travel` |
| generic: window state (size, scope accent) | 11 | `showEvent`, `resizeEvent`, `_log_window_size`, `apply_scope_accent_styling`, `_required_scope_accent_color`, `_style_save_button_for_scope`, `_style_header_for_scope`, `_style_tabs_for_scope`, `_style_step_editor_for_scope`, `_style_function_editor_for_scope`, `_ensure_window_flash_overlay` |
| generic: code-document editing | 1 | `window_code_document_driver` |
| generic: owned signal subscriptions | 4 | `connect_orchestrator_config_signal`, `connect_artifact_signals`, `_cleanup_managed_resources`, `_on_session_record` |
| generic: debounced cross-tab refresh | 2 | `_schedule_function_editor_sync`, `_flush_function_editor_sync` |
| generic: form context retarget | 1 | `_update_context_obj_recursively` |
| domain (step, pipeline, artifacts) | 24 | `__init__`, `_numbered_step_title_name`, `_title_step_name`, `_build_step_scope_id`, `_on_pipeline_changed`, `connect_session_events` and its closure, `on_session_event` x4, `_follow_pipeline`, `_sync_function_editor_from_step`, `_invalidate_artifact_plan`, `_current_compiled_artifact_inspection`, `_on_compiled_artifact_state_changed`, `_on_runtime_artifact_available`, `_on_debug_snapshot_available`, `on_orchestrator_config_changed`, `_normalized_form_change_path`, `on_form_parameter_changed`, `_clone_step`, `_create_new_step`, `_find_main_window` |
| dead | 2 | `set_original_step_for_change_detection`, `get_function_info` |

Generic 44, domain 24, dead 2: 70 function bodies (67 methods plus 3 closures).

Attributes: 10 are dead, write-only or double names (`current_tab`, `parameter_editors`,
`class_hierarchy`, `original_step`, `pipeline_config`, `_function_pattern_controller`, `tab_bar`,
`_tab_body`/`tab_widget`, `_base_window_title`, `_flash_overlay`); 5 are `None`-until-connected signal
slots; 3 are `None`-until-`setup_ui` editors (`step_editor`, `func_editor`, `artifact_plan_view`).

### Restated relations

- The three tabs are named in eleven places: `setup_ui` (through an 18-field
  `_DualEditorTabBuildContext` of callbacks), `apply_scope_accent_styling` (two per-tab stylers),
  both navigation paths (`DualEditorWindowNavigationDriver.driver_for_field_path`,
  `select_tab_for_field_path`, `select_and_scroll_to_field`), `_on_pipeline_changed` (three `if editor:`
  blocks), `on_tab_changed` (a list of tab names by index), `form_managers`, `state`,
  `window_code_document_driver`, `before_managed_close`. A fourth tab edits all of them.
- `DualEditorTab` is an enum (rule 1a) whose only behaviour, `select`, looks the tab up by label text.
- The window shell (header with Cancel/Save, tab body, dirty widgets, accent on save button and header,
  default size on first show, agent save capabilities) is written twice: here and in
  `pyqt_reactive.windows.config_window.ConfigWindow`.

## Inventory before creation (pyqt-reactive, formbridge)

Searched `external/pyqt-reactive/src` and `external/formbridge/src` for: `Tab` classes,
`NavigationDriver`, `add_time_travel_complete_callback`, `__subclasses__`, `Dirty*`, `BaseFormDialog`.

| Concern | Existing owner | Decision |
|---|---|---|
| tab bar + per-tab action widgets | `ActionTabbedWindowBody`, `ActionTabSpec`, `ActionTabMaterialization` | reuse; tabs return `ActionTabMaterialization` |
| dirty title / save marker | `DirtyWindowPresentation`, `DirtyWindowPresenter`, `DirtyWindowStateTracker` | reuse |
| save / reject / close lifecycle | `BaseManagedWindow` (`base_form_dialog.py`) | reuse; new window is a subclass |
| several navigation owners in one window | `CompositeWindowNavigationDriver` | extend by subclass (adds "show the owning tab") |
| scope accent | `ScopedBorderMixin` | reuse |
| a window that hosts a family of tab declarations over one edited object | none (`ConfigWindow` hosts N config states with a private `_ConfigEditorTab` record, not a family) | add `TabbedEditorWindow`, `EditorTab`, `EditedObject` |

## Target

pyqt-reactive `windows/tabbed_editor_window.py`:

- `EditorTab` (ABC): one tab. Declares `label`; supplies `build()`, and by default nothing for
  `form_managers`, `navigation_driver`, `code_document_driver`, `apply_scope_accent`,
  `write_pending_edits`, `refresh_from_state`, `release`. Membership is by inheritance from the tab
  family base the edited object names (P1 Prop 3.3, Thm 4.4); the roster is derived from the class
  hierarchy (`EditorTab.declared_tabs`), never listed.
- `EditedObject` (ABC): what is edited. Supplies scope id, ObjectState, title, save label, `save()`,
  mutation guard, and names its `tab_family`.
- `TabbedEditorWindow(BaseFormDialog)`: header, tab body, dirty presentation, save/cancel, scope accent,
  time-travel refresh, default size, composite navigation, code document. It never names a tab.
- Navigation keeps the owner visible: each tab supplies its own driver, and the window driver is a
  `CompositeWindowNavigationDriver` over `(tab, driver)` pairs (P10 Prop 6.1, Thm 4.3).

OpenHCS keeps declarations: `StepEdit(EditedObject)`, `StepEditorTab(EditorTab)` family with
`StepSettingsTab`, `FunctionPatternTab`, `ArtifactsTab`, and `DualEditorWindow(TabbedEditorWindow)` with
the pipeline-following code only. `DualEditorTab` (enum), `_DualEditorTabBuildContext`,
`_DualEditorTabBuilder`, `_DualEditorTabs`, `DualEditorFunctionPatternController` and
`DualEditorWindowNavigationDriver` are deleted.

## Guards

- `dual_editor_window.py` names no tab class except to parametrise family hooks.
- No `DualEditorTab` enum; no `is None` on an editor widget in the window.

## Tests

- pyqt-reactive `tests/test_tabbed_editor_window.py`: generic window over a throwaway family.
- OpenHCS: dual-editor tests rewritten against real tab objects in place of `__new__`-built windows.

## New-case experiments

Throwaway `EditedObject` plus a throwaway `EditorTab` family hosted by `TabbedEditorWindow` unchanged;
throwaway fourth `StepEditorTab` hosted by `DualEditorWindow` unchanged.

## Done when

Guards pass, `guardrails rc=0`, `smoke rc=0`, pyqt-reactive suite passes.

## Progress

- [x] classification (this commit)
- [ ] library: `TabbedEditorWindow`
- [ ] OpenHCS port
- [ ] tests, new-case
