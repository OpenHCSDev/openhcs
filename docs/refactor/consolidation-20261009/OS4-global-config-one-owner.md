# OS4: one owner of the global config

Branch `refactor/OS4-global-config-one-owner`. Libraries: ObjectState 4.0.0 (`02393c4`),
formbridge 0.1.4 (`3ddc051`), pyqt-reactive 0.8.0 (`1c0f35f`). Removed names and their
replacements: ObjectState `CHANGELOG.md` (4.0.0) and `docs/state_propagation.rst`;
pyqt-reactive `CHANGELOG.md` (0.8.0).

## What is wrong (measured at `c603c82f0`)

The global config had four holders in the GUI process and a different set in the
headless one:

- `openhcs/pyqt_gui/app.py:235-249` stored the config twice through the two 3.x
  setters and then registered a state built from the same object.
- `Session.global_config` (`session.py:338`) held a third copy; `Session.adopt_global_config`
  wrote the store again with a config the state already held; `initialize_datasets`
  (`:1030`) and its worker (`:1055`) re-stored the session's copy on every initialisation.
- The headless MCP session (`openhcs/mcp/context.py:269`) registered no state at all.
- `window_handlers.py:100` had a fallback setter on save; `main_window_workflows.py:220`
  forwarded the saved config to `adopt_global_config`.

A fact with several writers kept equal by convention is a restated relation
(PAPER-RESULTS, P1 correct-maintenance model): the copies are derived views or deleted.

## Target (done)

- The state registered at scope `""` is the holder. Reads are
  `get_live_global_config` / `get_saved_global_config`.
- ONE registration site and one owner: `Session.__init__` takes a required
  `global_config` and registers the state around it; `Session.close()` unregisters
  that state (only while it is still the one registered). There is one way to start
  a session (`Session(global_config=..., ...)`) and one way to end it
  (`session.close()`); there is no "register if nobody did".
- Whoever constructs a session closes it. The GUI main window constructs it and its
  `closeEvent` closes it. `OpenHCSAgentContext` (`mcp/context.py`) opens one lazily
  and is a context manager: it keeps a `contextlib.ExitStack`, puts `session.close`
  on it when its `session` property constructs the session, and `close()` closes the
  stack, so a session passed in as `session=` stays its giver's. The serving
  processes own the context: `mcp/bootstrap.py` (`build_bootstrapped_server` enters
  it on the required `lifetime: ExitStack` that `run_bootstrapped_server` and
  `_run_resident_socket_server` hold while they serve), `mcp/http.py::main`,
  `scripts/mcp_memory_diagnostic.py`; the benchmark CLI closes its session.
- `Session.global_config` is deleted; its eight readers ask
  `get_saved_global_config(GlobalPipelineConfig)`. `dataset_document.live_global_config`
  is deleted; its callers ask `get_live_global_config(GlobalPipelineConfig)`.
- `Session.apply_global_config(config)` is the one way to replace the config
  (`set_global_config`, which routes to the registered state).
  `Session.adopt_global_config` is deleted; what remains is
  `Session.saved_global_config_changed()`, which only publishes `DatasetConfigChanged`.
- Before the session exists (GUI start-up) the config that `config_cache` stored at
  launch is the global config; it is shadowed once the state is registered.

## Deletion certificates

| Deleted | Certificate |
| --- | --- |
| `app.py` two setter calls and the global-state registration | **derived**: `Session.__init__` registers the state; registering makes its object the global config (ObjectState 4.0.0). |
| `Session.global_config` attribute and constructor parameter | **derived**: `get_saved_global_config` reads the registered state's saved object; the attribute was only ever assigned the object last saved. |
| `Session.adopt_global_config` store write | **derived**: the state already holds the config after `mark_saved` (window save) or `set_global_config` (`apply_global_config`). |
| `session.py` setter in `initialize_datasets` and in its worker `run()` | **derived** (one config per process; the worker reads the same one). Renamed instead of deleted they would revert unsaved global edits; `tests/unit/test_one_global_config_state.py` covers add, initialise, compile, run. |
| `window_handlers.py` fallback setter on save | **derived**: `handle_save` runs after the window called `mark_saved` on the registered state. |
| `MainWindowLifecycleWorkflow.propagate_config` | **unused** after its body became one call; `on_config_changed` calls `session.saved_global_config_changed()` directly. |
| `ZMQExecutionServer._ensure_request_global_config_context` | **derived**: a one-line forward to `set_global_config`, inlined at its one call. |
| `dataset_document.live_global_config(session)` | **derived**: equal to `get_live_global_config(GlobalPipelineConfig)` with a state registered; its no-state branch read the deleted attribute. |
| `dual_editor_tabs.py` entered `config_context` block around the step form | **tests-only**: the four test files that build the step editor give 61 passed with and without it; the earlier probe saw 0 lazy resolutions inside it over 8 builds. Not exercised: step types or widgets outside those tests that would do a plain lazy read (not through a state) while the form is built. |
| `open_session(global_config=..., **session_arguments)` | **derived**: registration of the state followed by `Session(...)`; both are now `Session.__init__`. Its `**session_arguments: Any` restated the constructor's parameters untyped. |
| `close_session(session)` | **derived**: `session.close()` followed by unregistering the global state; both are now `Session.close()`. With it gone there is no second, weaker way to end a session. |
| `openhcs/authoring/session/lifetime.py` | **unused** once both functions are gone; its docstring is the `Session` class docstring. |
| `benchmark` uses of the 3.x "rebuild lazy config" helper | **derived**: it stored the global config and returned a field-for-field copy; lazy fields resolve at read time. Replaced by `set_global_config` and the config object itself. |
| `_candidate_pipeline_config(global_config=...)` parameter (benchmark) | **unused** after the above. |

## A. Per-process stored config in the execution server

Compilations cannot overlap in one execution-server process, so `set_global_config`
per request stays (`openhcs/runtime/zmq_execution_server.py`, comment at the call).
Evidence: `execute_task` is called only from `run_execution`
(`external/zmqruntime/src/zmqruntime/execution/server.py:270`), which only
`_queue_worker` calls (`:216`); one such thread is started (`:180-184`).
`execute_compiled_bundle` is synchronous (`openhcs/runtime/zmq_worker_execution.py:69-92`);
no control-thread strategy compiles (`openhcs/runtime/zmq_control.py`); workers receive
the compiled bundle. Test:
`tests/unit/test_zmq_execution_server.py::test_jobs_submitted_together_each_compile_with_their_own_global_config`
(four submitting threads, the real queue worker, a real compile).

## B. `InProcessCompileInspectionGateway`

It runs only in MCP processes (`openhcs/mcp/context.py` `artifact_plan_service`,
`openhcs/agent/capabilities.py`), never in the GUI. The MCP process now registers a
global state with its session, and a request without `global_config_id` compiles
against `GlobalPipelineConfig()`, so the two can differ: a rename would have replaced
the session's config. Fix: `ArtifactPlanInspectionService` compiles in a separate
process by default (`ChildProcessCompileInspectionGateway`, about 3-4 s more per
inspection). `InProcessCompileInspectionGateway` raises when a global state is
registered; it is used by tests and inside the child.
An in-process explicit path is not possible on ObjectState 4.0.0: steps resolve through
`ObjectState.resolve_saved_object` (`openhcs/core/pipeline/compiler.py:923`), which
takes no explicit global config and ignores an entered context. That needs an
ObjectState change (a `global_config` argument); reported, not done here.
Test: `tests/unit/agent/test_plan_inspection_keeps_the_global_config.py`.

## C. Route versus raise

Route kept. Remaining OpenHCS calls that replace the global config:

- `core/config_cache.py` `_establish_global_pipeline_config`: the config loaded at
  launch (`pyqt_gui/launch.py:188`, the only caller of `load_cached_global_config*`),
  before any state exists.
- `runtime/zmq_execution_server.py`: the request's config, in a process with no state (A).
- `authoring/session/session.py` `apply_global_config`: the deliberate replace; callers
  are `dataset_document.apply_dataset_document` (an edited code document whose global
  part differs) and tests.
- `agent/services/artifact_plan_inspection_service.py` in-process gateway: only when no
  global state is registered (B).

None runs on plate add, initialisation, compile or run.

## Found, out of scope

- More holders of the same value in the GUI: `runtime_context.pipeline_runtime_config`
  (`pyqt_gui/app.py`, `main.py`) and `service_adapter.global_config`. Candidates for the
  same treatment.
- The global config form cannot finish building: `source_spatial_domain.fill_value: Any`
  raises `UnsupportedWidgetTypeError`; predates this change.
- `PipelineCompiler` takes registry ancestors for steps (`compiler.py:912-915`), so an
  in-process inspection of a plate that is open in the session would read that
  session's dataset state.

## Gates

ObjectState submodule at the start of the gate run: `02393c4aa482da320b5c529945968020ce14adc4`.

- Guardrails (head `f8264b500`): `ratchet openhcs exit 0`, `ratchet scripts exit 0`,
  `ratchet benchmark exit 0`, `38 passed, 22 warnings in 39.42s`,
  `nra-r1 exit 0: "increased": []`, `guardrails rc=0`. Ratchet deltas:
  `GodClassExcess Session` -1, `GodClassExcess ZMQExecutionServer` -2.
- Smoke (head `f8264b500`): `smoke pytest exit 0 (105 s): 7 passed, 2 warnings in 101.83s`,
  `smoke gui exit 0 (25 s)`, `smoke rc=0`.
- `verify_branch.sh os4` (started at head `6cc3ff795`, complete):
  `suite: = 63 failed, 11646 passed, 25 skipped, 354 warnings, 2 errors, 6 subtests passed in 923.33s (0:15:23) =`,
  `collected 11733, reported 11710, crash lines 0`, `new vs known: 29`,
  `only on os4:` empty, `fails on both with a different error:` empty.
  NOT CLEAN: the 29 (ids in `/home/ts/code/projects/openhcs/.claude/verify/os4.new`)
  failed in the suite and passed in the per-file rerun. Smoke, guardrails and other
  pytest runs were going on the same machine during the suite, and several of the 29
  have 5 s timeouts; the other candidate is a global state left registered by one test
  file and read by a later one in the same worker. Not decided. Candidates for the
  leak: test files that build an `OpenHCSAgentContext` (its `session` property opens
  a session, which registers the global state) and have no registry teardown:
  `tests/unit/agent/test_knowledge_base_service.py`, `test_mcp_plate_stream_progress.py`,
  `test_mcp_server.py`, `test_native_presentation_mcp_451452.py`,
  `test_neurite_body_gate_authoring.py`, `test_official30_knowledge_examples.py`,
  `test_owned_runtime_bootstrap.py`, `test_plate_streaming_service.py`,
  `test_progressive_authoring_context.py`, `test_ui_bridge_service.py`,
  `tests/unit/test_benchmark_control.py`, `test_catalog_endpoint_incarnation.py`,
  `test_function_catalog_zmq.py`, `test_napari_reset_transitions.py`,
  `test_native_viewer_presentation.py`, `test_viewer_receipt_replay.py`
  (scan: a text match, not a trace). Seven of these files are among the 29.

- Official30 parity (heavy slot, `official30.lock`, head `f8264b500`):
  `1 passed in 726.83s (0:12:06)`, `parity rc=0` (the test asserts the 30 cases).
  ObjectState submodule at the end: `02393c4aa482da320b5c529945968020ce14adc4`
  (same as at the start).

## Order-dependent errors in a replayed worker order

- `fixture 'restart_session' not found` (four tests of
  `tests/unit/desktop/test_desktop_restart.py`) is not a leaked session and not ours.
  Minimal order: `tests/unit/desktop/test_desktop_restart_worker.py
  tests/unit/test_orchestrator_lane_planning.py tests/unit/desktop/test_desktop_restart.py`
  as explicit file arguments (any desktop file, any file of another directory, then a
  desktop file that uses the conftest fixture). A bare three-file project reproduces
  it with plugin autoload off. Cause, pytest 9.1.1: conftest fixtures are attached to
  the first `Directory` node collected for the conftest's directory
  (`_pytest/fixtures.py`, `_pending_conftests.pop`) and matched by node identity
  (`_matchfactories`); when a file of another directory comes between two files of
  one directory on the command line, the second file gets a new `Directory` node and
  no longer sees them. The suite passes directories (`pytest tests/unit tests/core
  -n 2 --dist loadfile`); every xdist worker collects those same arguments, so each
  directory is one node and the error cannot occur there. A worker's order is
  therefore replayed with directory arguments and a reordering plugin
  (`.claude/os4b/replay_order.py`, untracked), not with file arguments.
- `tests/unit/desktop/test_desktop_update.py` imported `headless_session` from the
  directory's `conftest`; it now lives in `tests/unit/desktop/sessions.py`. (This was
  not the cause of the error above.)
- `tests/unit/test_family_registries_restored.py` failed at import on this branch
  (two ObjectState 3.x names and a fixture removed in `c7bde7c74`): a collection
  error for the suite. Its last test now runs `restored_object_states`.

## Not done, candidates

- `build_server(context=None)` (`openhcs/mcp/server.py`) and
  `build_http_server(context=None)` (`openhcs/mcp/http.py`) still create a context
  nobody can close when called without one (test call sites only; production passes
  one). Traced over the 66 unit test files that build a server, a context or a
  session: no test leaves a session open.
- `ObjectStateRegistry.unregister(state)` removes whatever is registered under the
  state's scope, not that state; `Session.close()` therefore checks identity first.
  The check belongs in ObjectState.
- `empty_registry` in `tests/unit/test_one_global_config_state.py` and
  `test_replaced_global_config_reaches_registered_states.py` is a fixture that does
  nothing since `restored_object_states`.
- `OpenHCSMainWindow.on_session_event` is a `singledispatchmethod` over event types.

## Remaining (for the next agent)

1. Decide the 29: rerun the suite with nothing else running; if they persist, find the
   test that leaves a global state registered (an autouse fixture that fails a test
   leaving `ObjectStateRegistry.global_config_state(GlobalPipelineConfig)` set would
   name it) and give the headless context an end (done: `OpenHCSAgentContext.close`).
2. `tests/unit/test_bioformats_microscope_handler.py::test_openhcs_output_subdirectory_initializes_from_metadata_root`
   failed in a sub-run (`MetadataNotFoundError`); it is not in the 29, so it either is
   in `known.fail` or passed in the suite. Check.
3. The plan-inspection gateway receives the child's objects through `singledispatch`;
   the coordinator is replacing that with a message family the child constructs.
4. Open the PR (non-draft) once the suite is clean. Do not merge.

## Session-owner sub-job: observed results (head `b752458d3` plus this receipt)

- Unit set (`-n 2 --dist loadfile`: `test_one_global_config_state.py`, `tests/unit/desktop`,
  `agent/test_mcp_server.py`, `test_mcp_http.py`, `test_mcp_stdio_transport.py`,
  `test_mcp_bounded_discovery.py`, `pyqt_gui/test_main_config_propagation.py`,
  `test_application_cleanup.py`, `test_ui_agent_bridge.py`, `test_benchmark_control.py`,
  `test_replaced_global_config_reaches_registered_states.py`): `514 passed, 1 skipped`.
- Integration (`test_session_journey.py`, `test_compiled_artifact_inspection.py`,
  `test_agent_observation_export_zmq.py`, `tests/pyqt_gui/test_session_gui_journey.py`):
  `15 passed`.
- Replay of the first 158 files of worker gw0's order, one process, directory
  arguments plus the reordering plugin: `2 failed, 4222 passed, 4 skipped, 7553 deselected`;
  the two are the ids in `known.fail`. The same order with file arguments gave
  19 failed and 4 errors before this sub-job.
