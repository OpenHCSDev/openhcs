# U4: formbridge, the toolkit-neutral tier

**Head audited:** `openhcs` at `c7a953030` (PR #1203, E1, on `main` `eb64b3c13`); `pyqt-reactive` `main` at `1bce7de` (0.5.0); `formbridge` `main` at `7463390` (0.0.1 placeholder). **Rules:** [00-RULES.md](00-RULES.md). **Step 4** ([04-ARCHITECTURE.md](04-ARCHITECTURE.md#the-ui-one-session-interface-thin-renderers-surfaces-u1-to-u5), row U4).
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* the `formbridge` library (repository `OpenHCSDev/formbridge`); `MainThreadDispatcher` with a queued and a Qt delivery; the bridge application declaration that replaces OpenHCS's bridge constants. *Uses:* `AutoRegisterMeta`, U2's `UiBridgeOperation` family, U3's `ScopeKey` and `FieldInspection`.

This branch is stacked on E1 (#1203): E1 edits 342 files, including every UI-bridge module this surface moves, so building on `main` would leave each move in conflict with E1. Merge E1 first.

## What is wrong

**Headless MCP imports PyQt6, because toolkit-neutral code lives inside the Qt library and the generic UI-bridge DTOs, contracts and server live inside OpenHCS's GUI and agent packages.**

Re-measured at `c7a953030`:

- **Two B5 failures (owner U4).** `test_mcp_cold_build_does_not_import_pyqt6` and `test_hosted_mcp_cold_build_does_not_import_pyqt6` (`tests/unit/agent/test_mcp_distribution_runtime.py:165,194`) fail. `build_server()` loads `PyQt6.QtCore`, `QtGui`, `QtWidgets` and `sip` through two chains:
  - `mcp/execution.py:12-18` imports `QCoreApplication`/`QEventLoop`/`QThread` and pyqt-reactive's `FutureCompletion` (a `QObject`) and `UiThreadDispatcher` (a Qt signal proxy). The headless server builds a `QCoreApplication` only to use its event loop as a main-thread queue.
  - `authoring/session/pipelines.py:20` → `pyqt_reactive.services.function_pattern_code_document` → `pyqt_reactive.protocols` (package initializer) → `protocols/log_providers.py` → `pyqt_reactive.core` (package initializer) → `debounce_timer.py` (`QTimer`) and `reorderable_list_widget.py` (`QListWidget`). The code document and the provider registries are Qt-free; package initializers bundle them with widget adapters.
- **pyqt-reactive's Qt-free tier is 10.8k lines in 64 modules** (0.5.0, measured by a static import graph: no module-level Qt import in the module or anything it imports, after dropping package initializers). It holds the form model (`forms/parameter_form_service.py` 924, `parameter_info_types.py` 350, `parameter_type_utils.py` 224, …), help documents and parameter help, the function-pattern code document (1,300), scope tokens, the pattern data manager, the provider registries in `protocols/`, the preview formatters and strategies, path cache, log discovery and streaming, the system-metrics sampler, ZMQ server scanning, and the Qt-free manager hooks in `widgets/shared/`. `animation/flash_trace.py` is an unused re-export shim of `flash_trace.py`.
- **OpenHCS's headless code imports 24 of those modules from the Qt package** (`agent/dto/ui_bridge.py`, `agent/dto/viewer.py`, `agent/services/function_catalog_service.py`, `authoring/session/{pipelines,progress,session,step_scopes}.py`, `core/function_patterns.py`, `mcp/server.py`, `processing/custom_functions/events.py`, …).
- **The generic UI-bridge tier is about 9k lines inside OpenHCS** (classified symbol by symbol from imports):
  - `agent/dto/ui_bridge.py` (2,844): about 2.55k lines of identities, connection and descriptor DTOs, catalog pages, action, window, widget-tree, snapshot, ObjectState-field, code-document, branch and operation DTOs import nothing from OpenHCS's domain; about 230 lines (plate-manager, pipeline-editor, debug and live-measurement states, the selected-plate workflow) are OpenHCS's.
  - `agent/services/ui_bridge_service.py` (1,832): the `UiBridgeOperation` family, `serves`/`UiBridgeOperationServer`, gateway ABC and errors, descriptor reading and resolution, and `UiBridgeService` are generic (about 1.73k); two operations (`selected_plate_workflow`, `session_events`), `UiBridgeEnvironment` and `viewer_launch_context` are OpenHCS's.
  - `agent/services/ui_bridge_transport.py` (164), `agent/services/object_state_field_projection.py` (161), `agent/dto/common.py` (the `AgentError`/`AgentResultEnvelope`/`AgentCliRequest` family, 180), `core/selection.py` (99) and `agent/runtime_platform.py` (364) import no domain code.
  - `pyqt_gui/services/ui_bridge_server.py` (623), `ui_bridge_contracts.py` (629), `ui_bridge_registry.py` (263) and most of `ui_agent_bridge.py` (about 1.2k of 1,916) and `ui_bridge_object_state.py` (about 780 of 1,163) import no Qt at all. They sit in the GUI package only because the DTOs did.
  - `pyqt_gui/services/ui_bridge_windows.py` (2,894): window introspection, about 2.7k lines of generic Qt.
- **OpenHCS constants stand in for an application declaration.** The protocol version `"openhcs.ui_bridge.v3"` (`ui_bridge_service.py:114`, read in five modules), `OPENHCS_ENDPOINT_APPLICATION`, `OPENHCS_ZMQ_CONFIG`, the `"OpenHCS", "ui-bridge"` runtime directory, the `OPENHCS_UI_BRIDGE_*` variable names, `"OpenHCSUiBridgeServer"`, `DEFAULT_AGENT_WINDOW_SNAPSHOT_DIR`, the hidden `"__plates__"` scope (`ui_bridge_object_state_scope_policy.py:17`) and `OpenHCSUiWindowId` aliases are read directly by generic code.
- **Identity enums restate the identity registry** (`agent/dto/ui_bridge.py:124-154`: `_identity_enum` builds `UiCodeDocumentId`, `UiStateSurfaceId`, `UiWidgetId` from the declaration registries; only tests read them; rule 1a).
- **Reassigned to U4 by U3 and U5:** the UI-bridge server and window introspection; the bridge widget id `plate_manager` and the dev client's `WorkflowTerminalStateCriterion`; `PyQtServiceAdapter.get_current_color_scheme` as a library protocol (called by pyqt-reactive `abstract_manager_widget.py:685`); the `QApplication` teardown segfault (about one run in five; the offscreen smoke test exits with `os._exit` to avoid it, `tests/pyqt_gui/test_main_window_offscreen_smoke.py:198`).
- **`DualEditorWindow._current_function_spec`** (`pyqt_gui/windows/dual_editor_window.py:925`), "compatibility wrapper for tests", has no caller; neither has the `DualEditorSession.current_function_spec` it forwards to.

## Target

**formbridge 0.1.0** (no Qt, no OpenHCS; depends on python-introspect, objectstate, metaclass-registry, zmqruntime):

- The Qt-free tier, keeping its module paths under `formbridge.` (`formbridge.forms.parameter_form_service`, `formbridge.services.help_document`, `formbridge.protocols.form_config`, …); the Qt-free manager hooks become `formbridge.managers.*`, the scope colour strategy `formbridge.theming.*`. Package initializers export nothing; every import names the defining module.
- `formbridge.services.main_thread_dispatch`: `MainThreadDispatcher` (owned calls, atomic pre-start cancellation, close) with `QueuedMainThreadDispatcher`, which a headless process drains with `run_until(future)`. pyqt-reactive's `UiThreadDispatcher` subclasses it and supplies only Qt delivery.
- `formbridge.bridge`: the generic UI-bridge tier listed above (DTOs, operation family, gateway, descriptors, transport, service, contracts, provider registry, in-process bridge and server). One `UiBridgeApplication` class declares what OpenHCS's constants restate (protocol version, endpoint application, transport config, runtime directory name, environment variable names, snapshot directory, server name); OpenHCS declares `OpenHCSUiBridgeApplication` once. Hidden scopes are a registered family; window identity aliases are declared on the identity classes. The identity enums are deleted.
- The colour-scheme protocol is a formbridge ABC that pyqt-reactive's manager widgets read and OpenHCS's service adapter implements.

**pyqt-reactive 0.6.0** depends on `formbridge>=0.1,<0.2`, deletes the moved modules (no re-exports) and receives the Qt half of the bridge: window introspection, the ObjectState code-document window providers, and the host-window declaration the introspection reads.

**OpenHCS** keeps its declarations: its bridge application, widget, document and state-surface identities, the plate-manager, pipeline-editor, debug and live-measurement surfaces, the session operations, the selected-plate workflow and session-events operations, `OpenHCSUiAgentBridgeService`, and the MCP capabilities. `mcp/execution.py` runs on `QueuedMainThreadDispatcher`; no `QCoreApplication` exists in a headless process.

Deleted: `pyqt_reactive.animation.flash_trace` (shim); `_identity_enum`, `UiCodeDocumentId`, `UiStateSurfaceId`, `UiWidgetId`; `DEFAULT_UI_BRIDGE_DESCRIPTOR_RESOLVER` and the module constants the application class replaces; `DualEditorWindow._current_function_spec` and `DualEditorSession.current_function_spec` (both unused).

## Persisted state

All runtime state, reset on upgrade (rule 2): formbridge's default data directories and log prefixes are named `formbridge` (OpenHCS configures its own); the pattern scope-token metadata key becomes `__formbridge_scope_token__`; UI-bridge descriptor files carry the application's protocol version.

## Guards

- `tests/unit/agent/test_mcp_distribution_runtime.py`: the two cold-build tests pass (stdio and hosted MCP import no PyQt6; hosted imports no `openhcs.pyqt_gui`).
- `tests/unit/test_formbridge_guards.py`: importing the MCP server (stdio and hosted) or any formbridge module loads no PyQt6, PyQt5, PySide, qtpy or pyqt-reactive module; no module under `openhcs/` defines a moved name; no OpenHCS module imports a moved `pyqt_reactive` path.
- formbridge `tests/test_no_toolkit_imports.py`: every formbridge module imports without a toolkit, and no formbridge source names one.

## Tests

- The pyqt-reactive tests of moved modules move to formbridge unchanged (14 files); the two that tested the flash-trace shim and a moved static gate are deleted or moved.
- New: `formbridge/tests/test_main_thread_dispatch.py` (owner-thread execution, pre-start cancellation, callback-owned outcome, close).
- The MCP affinity tests assert main-thread execution without Qt; the "no Qt application" case becomes "a worker call never runs on the worker".

## New-case experiments

- A second headless consumer of the form model or help documents (a web form renderer): today it imports a Qt package and loads PyQt6. After: `import formbridge.forms.parameter_form_service`.
- A second application with a running-UI bridge: today it copies 9k lines out of OpenHCS. After: one `UiBridgeApplication` subclass, its identity declarations and its state-surface providers.

## Done when

The guards pass; the formbridge and pyqt-reactive PRs are open with CI on Linux, macOS and Windows for Python 3.11–3.13 plus ruff; OpenHCS points `external/formbridge` and `external/pyqt-reactive` at their branch heads with `formbridge>=0.1,<0.2` and `pyqt-reactive>=0.6,<0.7`; the agent, UI-bridge and pyqt_gui tests pass offscreen; the structural ratchet and NRA show no regression.

## Outcome and corrections

Measured against the E1 head `c7a953030`: OpenHCS production −13,730 +736; tests −520 +578. formbridge receives 10.8k lines from pyqt-reactive and about 9k from OpenHCS (more after `ruff format`); pyqt-reactive source −11,325 +3,378 (the Qt bridge half arrives, the Qt-free tier leaves). Guards: 5/5 in `tests/unit/test_formbridge_guards.py`, plus formbridge `test_no_toolkit_imports.py` and pyqt-reactive `test_only_qt_code.py`.

- **The Qt-free UI-bridge server and most of the in-process bridge went to formbridge, not pyqt-reactive.** U3's reassignment expected the server beside the Qt code. It imports no Qt; only window introspection (`bridge.windows`) and the ObjectState code-document window providers (`bridge.object_state_documents`) are Qt, and they went to pyqt-reactive.
- **Headless dispatch without Qt.** `mcp/execution.py` built a `QCoreApplication` only to use its event loop as a main-thread queue. formbridge's `QueuedMainThreadDispatcher` replaces it (`run_until(future)`); pyqt-reactive's `UiThreadDispatcher` is the Qt delivery of the same `MainThreadDispatcher`.
- **One application declaration.** `UiBridgeApplication.current()` returns the one declared application (OpenHCS: `OpenHCSUiBridgeApplication`, imported by the OpenHCS bridge modules). Bridge envelopes carry formbridge's `SCHEMA_VERSION` (`formbridge.v1`); the bridge protocol is `openhcs.ui_bridge.v4`. Descriptor files are runtime state.
- **Wire and MCP changes (rule 1).** `openhcs_ui_get_state_surface` now requires `surface_id` (the generic request cannot name OpenHCS's default surface); the MCP contract fixture records it. The bridge widget id is `datasets` (was `plate_manager`); its document and surfaces are `datasets.orchestrator_config`, `datasets.state`, `datasets.live_measurements`. Bridge error hints name operations instead of OpenHCS tool names.
- **Rule 1a.** Window-snapshot capture scopes and frame conditions stored Qt callables in enum members; formbridge keeps the wire enums with Qt-free attributes, and each scope and observation kind has a registered Qt implementation. The dev client's `WorkflowTerminalStateCriterion` family restated `DatasetWorkflowOperation`; the terminal and failed row states now live on the operations.
- **QApplication teardown segfault: not reproducible.** The offscreen smoke driver with normal interpreter teardown exited cleanly 18 of 18 times on this branch (6 after deleting the application, 12 with it alive) and 8 of 8 on the E1 head. The smoke test no longer exits with `os._exit`, so a teardown crash fails it.
- **Found outside the brief:** `openhcs/utils/performance_monitor.py` was an unused copy of the library module (deleted); `parameter_ops_service` in pyqt-reactive had an `ImportError` stub fallback (deleted).
- **Not done here:** `openhcs/core/log_utils.py` restates parts of formbridge's `core.log_utils` (log discovery and classification); owner U5 (dead and misplaced UI code). The GUI's own "plate manager" names (`PlateManagerWidget`, `OpenHCSUiWindowId.plate_manager`) are U1's container-manager rename.
