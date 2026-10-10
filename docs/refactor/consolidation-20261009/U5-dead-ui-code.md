# U5: Dead and misplaced UI code

**Head audited:** `openhcs` `main` at `94046ad99` (#1174). **Rules:** [00-RULES.md](00-RULES.md). **Step 2** (disjoint from step 3; see [04-ARCHITECTURE.md](04-ARCHITECTURE.md#the-ui-one-session-interface-thin-renderers-surfaces-u1-to-u5)).
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* none.

## What is wrong

**The desktop GUI carries dead modules, a copied library class, unused ABCs and forwarders, a rule-2 history converter, and 2.4k lines of desktop install, update and restart code filed under `pyqt_gui/services` (TIME-6, IMPL-3, MEMB-1).**

Re-verified at `94046ad99`, checking imports, `pyproject.toml` entry points, `napari.yaml`, launches by module name in `.github/`, `packaging/` and `scripts/`, and `iter_modules`/`import_module` discovery (none under `pyqt_gui` or `ui`):

| Item | Lines | Evidence |
|---|---|---|
| `pyqt_gui/dialogs/metadata_viewer_dialog.py` | 139 | `MetadataViewerDialog` named only in its own file; `dialogs/` has no `__init__`. A scan of every module under `pyqt_gui` and `ui` finds it and `ui/shared/pattern_file_service.py` (F1's) as the only unreferenced modules. |
| `pyqt_gui/utils/__init__.py` | 21 | Re-exports `core.path_cache`; zero importers. |
| `ui/shared/pattern_data_manager.py` | 227 | Copy of `pyqt_reactive/services/pattern_data_manager.py`. Its one product use is `dual_editor_window.py:269`, `self.pattern_manager = PatternDataManager()`, an attribute nothing reads. Only `tests/unit/test_pattern_data_manager.py` exercises it. The copy is stricter than the library for three-member tuple leaves; recorded for U3. |
| `pyqt_gui/widgets/__init__.py:8-16` | 9 | `__all__` lists seven classes the module does not define; `widgets/shared/__init__.py` has `__all__ = []`. |
| `pyqt_gui/services/history_migration.py` | 143 | `DesktopHistoryUpgrade`, a rule-2 converter for version-1 ObjectState histories, passed as `migration=` at `desktop_update.py:617`. Decision: desktop histories are runtime state and reset on upgrade. |
| `PipelineEditorWorkflowSurface`, `PlateManagerWorkflowSurface`, `SignalConnectionSurface`, `SignalEmissionSurface`, `ConfigChangeSurface` (`services/main_window_workflows.py:56-157`) | 102 | No subclass and no `isinstance`; used only as annotations at `:722-723` and `:762`. |
| `GlobalEventBus` (`services/service_adapter.py:28-121`) | ~40 dead | `step_changed`/`emit_step_changed` have no emitter; `register_window`/`unregister_window` keep a list read only by debug logging. `pipeline_changed` and `config_changed` are live (emitted by `plate_manager_workflows.py` and `pipeline_editor_workflows.py` through `GuiEventBusBroadcaster`, received by `dual_editor_window.py:834-876`), and pyqt-reactive's `AbstractManagerWidget` reads `service_adapter.get_event_bus()`: recorded for U3. |
| Dead adapter methods | ~110 | `show_dialog` (:194), `run_system_command` (:435), `open_external_editor` (:462) and `ExternalEditorProcess` (:595) have no caller; `get_current_style_sheet` (:559) has none. |
| Theme forwarders (`service_adapter.py:500-575`) | ~70 | `get_theme_manager`, `apply_color_scheme`, `switch_to_dark_theme`, `switch_to_light_theme`, `load_theme_from_config`, `save_current_theme`, `register_theme_change_callback` forward to `self.theme_manager`; every caller is in `main.py`. `get_current_color_scheme` is called by pyqt-reactive (`abstract_manager_widget.py:685`) and 13 product sites: recorded for U3. |
| Six aliases of one services object (`main.py:209-214`, `:329-335`) | 16 | `window_services`, `widget_services`, `theme_manager_services`, `window_color_scheme_services`, `theme_file_services`, `config_services` are all assigned the same `MainWindowUiServices`, plus a `service_adapter` property and setter restating them. |
| "REMOVED" comments | 10 | `plate_manager.py:1278,2347,2533,2539`, `pipeline_editor.py:856,857,1245,1706`, `step_parameter_editor.py:64,431`, `code_editor_form_updater.py:30`, `orchestrator.py:1146`, `multi_template_matching.py:743`. |
| Desktop update and restart under `pyqt_gui/services` | 2,445 | `desktop_update.py` 990, `desktop_update_worker.py` 1,058, `desktop_restart.py` 112, `desktop_restart_worker.py` 101, `zmq_version_restart.py` 184; their install-side siblings `openhcs/desktop_installation.py` 265 and `openhcs/desktop_deployment.py` 1,184 sit at the package root. |

## Target

- Delete `metadata_viewer_dialog.py`, `pyqt_gui/utils/`, `ui/shared/pattern_data_manager.py` and the dead `pattern_manager` attribute, `history_migration.py`, the five workflow-surface ABCs, the dead event-bus paths, the dead adapter methods, and the seven theme forwarders. `main.py` calls `self.service_adapter.theme_manager` directly.
- `OpenHCSMainWindow` holds one `service_adapter` attribute; the six aliases and the property are deleted. `MainWindowWidgetConnector` and `MainWindowPipelineActions` annotate `PlateManagerWidget` and `PipelineEditorWidget`.
- The two widget package initializers keep only their docstrings.
- Restoring a restart session calls `ObjectStateRegistry.load_history_from_file(path)` with no converter. A pre-version-2 history then fails loudly and the recovery files are kept by the existing restore-failure path.
- One package `openhcs/desktop/`: `installation.py`, `deployment.py`, `update.py`, `update_worker.py`, `restart.py`, `restart_worker.py`, `zmq_version_restart.py`. Contents unchanged except imports, the worker file names they copy, and rule-1b renames: `DesktopDeploymentAuthority` becomes `DesktopDeployment` (its leaves are already `WindowsDesktopDeployment` and `MacOSDesktopDeployment`), `platform_authority` becomes `runtime_platform`, and docstrings say what they mean.
- `openhcs/desktop_deployment_cli.py` keeps its module name: shipped installers (`Install-OpenHCS.ps1:704`, `install-openhcs.sh:272`) and update workers from installed versions launch `python -m openhcs.desktop_deployment_cli` in the new environment. It is the entry point, not a re-export; it imports from `openhcs.desktop.deployment`.

## Persisted state

Restart-session ObjectState histories are runtime state: no converter, pre-version-2 documents are refused. No durable format changes.

## Guards

`tests/unit/test_dead_ui_code_guards.py`:
- the deleted and moved module paths are absent;
- no module under `openhcs/` defines a deleted name (`MetadataViewerDialog`, `PatternDataManager`, `DesktopHistoryUpgrade`, the five workflow-surface ABCs, `ExternalEditorProcess`, `DesktopDeploymentAuthority`) or imports `objectstate.history_migration`;
- `PyQtServiceAdapter` and `GlobalEventBus` define none of the deleted methods or signals;
- every literal `__all__` in an `openhcs/pyqt_gui` or `openhcs/ui` package initializer names only bound names;
- no `# REMOVED` comment anywhere under `openhcs/`;
- `OpenHCSMainWindow` assigns none of the six alias attributes.

## Tests

Delete `tests/unit/test_pattern_data_manager.py` and `tests/unit/pyqt_gui/test_desktop_history_upgrade.py`. Update fakes that implement deleted methods and the imports of moved modules. Move the desktop tests to `tests/unit/desktop/`. Add an offscreen GUI smoke test (`tests/pyqt_gui/test_main_window_offscreen_smoke.py`): launch `OpenHCSPyQtApp` and its main window in a subprocess with an isolated home, XDG directories and execution port; open the plate manager and the pipeline editor as their own windows through the pane float button (the panes are permanent docks with no close button) and close each back into its dock; close the main window; assert the event loop's exit status and that no process carrying the run's marker environment variable survives.

## New-case experiments

Not a family surface. A new desktop platform today means one `DesktopDeployment` leaf in `openhcs/desktop/deployment.py`; after the move that is still the only edit.

## Done when

Every row above is resolved, the guards pass, the CI workflow and scripts import the moved modules from `openhcs.desktop`, the smoke test passes offscreen, and the recorded items are in U3's list.

## Recorded for other surfaces

| Item | Evidence | Belongs to |
|---|---|---|
| `GlobalEventBus.pipeline_changed`/`config_changed` and `get_event_bus()` | emitted by plate-manager and pipeline-editor workflows, received by `dual_editor_window.py`, read by pyqt-reactive `AbstractManagerWidget` | U3 (ObjectState change subscription) |
| `PyQtServiceAdapter.get_current_color_scheme` | called by pyqt-reactive `abstract_manager_widget.py:685` and 13 product sites | U3 (library protocol) |
| `objectstate.history_migration.HistoryMigration` and the `migration=` parameter of `import_history_from_dict`/`load_history_from_file` | no consumer left after U5 | U3 (ObjectState lockstep) |
| pyqt-reactive `PatternDataManager.extract_func_and_kwargs` returns `(None, {})` for a three-member tuple; the deleted OpenHCS copy raised `TypeError` | `pattern_data_manager.py:120` in the library | U3 |
| Tearing down the `QApplication` after the main window closes (PyQt's exit handler or interpreter finalization) segfaults with no Python frame in about one run in five, at `7b3bb889d` (before U5) as after. The smoke test therefore exits with `os._exit` after the event loop returns | measured with the smoke driver: 1 of 6 runs at the pre-U5 head, 1 of 4 after; 10 of 10 clean with `os._exit` | U3 (generic Qt lifecycle) |
| `PlateManagerCodeDocumentAuthority` (15 files) | rule-1b name imported by `desktop/update.py`, defined in `ui/shared/plate_manager_code_document.py` | U1 |
| `AgentRuntimePlatformAuthority` (12 files) | rule-1b name imported by `desktop/deployment.py`, defined in `agent/runtime_platform.py` | not assigned; the session lead names an owner |
