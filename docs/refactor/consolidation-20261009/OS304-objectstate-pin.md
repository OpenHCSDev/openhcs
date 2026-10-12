# OS302: ObjectState 3.0.2

Branch `refactor/OS302-objectstate-pin`. Gates are not run by this branch's author; the
coordinator runs them from the worktree.

## What changed

- `external/ObjectState` moved from `731b125` (v3.0.1) to tag `v3.0.2`; `pyproject.toml`
  requires `objectstate>=3.0.2,<4`.
- `openhcs/authoring/session/session.py`: `Session.__init__` registers the global state
  (scope `""`) when none is registered. `apply_global_config` always writes the new config
  through that state (the `if global_state is not None` branch is gone).
- `openhcs/authoring/session/dataset_document.py`: `live_global_config` reads the global
  state; the `session.global_config` branch for a missing state is gone.
- `docs/archive/architecture/configuration_framework.rst:149`: said scope first; now says
  class first and points to ObjectState's `context_system.rst`, "Precedence Order".

## Tests added

`tests/unit/test_pipeline_states_resolve_from_registered_ancestors.py` (4 tests, pass on
3.0.2). Steps and their function states are built before they are registered; an inherited
field (`dtype_config.default_dtype_conversion`) is then read on each step state and each
function state, live value, reported source and saved value, after load, add, paste, move
and delete. Declared at global: source `("", DtypeConfig)`. Declared at plate: source
`(plate, DtypeConfig)`. Declared on the step: the function state reads it with the step
scope as source.

On 3.0.1 (submodule checked out at `731b125`, same test file): 3 pass, 1 fails.
`test_function_state_inherits_from_the_step_it_was_built_under` fails at the first load:
the function state reads the plate's `UINT16` instead of the step's `FLOAT32`. That is the
behaviour 3.0.2 corrects in OpenHCS.

`tests/unit/test_replaced_global_config_reaches_registered_states.py` (1 pass, 1 strict
xfail), see the two answers below.

## Compensating code deleted

None, because none exists. Evidence:

- grep over `openhcs/`, `external/formbridge/src`, `external/pyqt-reactive/src` for
  `invalidate_cache`, `invalidate_field`, `invalidate_self_and_nested`,
  `invalidate_by_type_and_scope`, `_live_resolved`, `_saved_resolved`, `_invalid_fields`,
  `_ensure_live_resolved`, `_compute_resolved_snapshot`: no call on an ObjectState outside
  ObjectState itself.
- `ObjectStateRegistry.increment_token()` (`step_parameter_editor.py:272`,
  `dual_editor_window.py:135`) only bumps a token and notifies listeners; it does not drop
  a state's resolved snapshot, so it could not have corrected the stale value.
- `step_parameter_editor.py:244` (`QTimer.singleShot(0, refresh_with_live_context)`, from
  2025-12) repaints placeholders, enabled styling and flash registrations after the form is
  built. It reads the state; with 3.0.1 the stale value was in the state's own snapshot, so
  this refresh could not have corrected it either. Not deleted: not proved unneeded.
- The 3.0.1 run above shows the stale value reaching a plain read, so nothing in the
  build path corrected it.

Deleted in this PR, with certificates:

- `session.py` `apply_global_config`: `if global_state is not None` guard. **derived**:
  `Session.__init__` registers the global state, so a session always has one.
- `dataset_document.py` `live_global_config`: `if state is None: return
  session.global_config`. **derived**, same mechanism. What tests do not cover: a caller
  that clears the registry after building a session and then applies a global config or
  renders a dataset document now gets an `AttributeError` on `None` instead of the
  session's config.

`openhcs/pyqt_gui/app.py:245-249` still registers the global state for the GUI before the
main window builds its session. That is now a second registration site for the same
state; candidate to delete once it is checked that nothing between `setup_application`
and `OpenHCSMainWindow.__init__` (`main.py:238`) reads scope `""`.

## Claim (a): the headless MCP session never registers the global scope

**True** on `origin/main`. The only registration of scope `""` under `openhcs/` was
`pyqt_gui/app.py:249`; `mcp/context.py:269` builds `Session(global_config=
GlobalPipelineConfig(), ...)` and `Session.__init__` registered nothing. Probe with a real
`Session` and `CallerThread`: `ObjectStateRegistry.get_by_scope("")` is `None` after
construction and after `set_pipeline`.

**It produced a wrong resolved value.** `apply_global_config` (reached headless through
`dataset_document.py:188`) skipped the missing state and only replaced the thread-local
config. Observed: a step and its function state built before kept `UINT8` (live and
saved), the dataset state too, while `orchestrator.get_effective_config()` and a step
added afterwards read `UINT16`. Two steps of one pipeline disagreed.

**Fixed here** (the session registers the global state).
`test_headless_session_global_config_reaches_existing_step_states` checks live value,
saved value and source for states built before and after the replacement.

## Claim (b): `session.py:468` calls `ensure_global_config_context` on every global config save while states exist

**True.** `adopt_global_config` calls it; callers are `apply_global_config` and
`pyqt_gui/services/main_window_workflows.py:220` (the config window's save participant).
`ensure_global_config_context` is `set_global_config_for_editing`: it replaces the saved
and live thread-local configs and tells no state.

That call alone does not produce the wrong value when the global state was edited first
(the edit invalidates the descendants): live values are right after
`apply_global_config` with a registered global state.

**A wrong value does exist on the GUI save path, from the same kind of unannounced
replacement.** `pyqt_reactive/windows/config_window.py:844` calls `mark_saved()` on the
global state, which resolves the descendants' saved values while the saved thread-local
config is still the old one; `:848` (`publish_saved_global_config`) and then
`session.py:468` replace it afterwards. Observed through a real `OpenHCSConfigWindow`
save: step and function states read live `UINT16`, saved `UINT8`, and stay dirty. Same
result on 3.0.1, so it is not a regression of this bump. With the thread-local replaced
before `mark_saved()` the saved values are right.

Not fixed here: the order is in pyqt-reactive and the missing announcement is ObjectState
issue #53 item 2. Recorded as strict xfail
`test_saved_global_config_reaches_saved_values_of_existing_step_states`; it must be
un-xfailed when #53 item 2 is fixed.

Also observed: for a global-typed field the thread-local config wins over the registered
global state's object (thread-local replaced without editing the state: a step added
afterwards reads the thread-local value, steps built before keep the state's).

## States built or re-resolved inside a caller's `config_context` (for ObjectState 3.0.3)

Method. grep for `config_context(` and `build_context_stack(` over `openhcs/` and the
library sources; and a runtime trace: a pytest plugin patched `ObjectState.__init__`,
`_compute_resolved_snapshot` and `_recompute_invalid_fields` to record every outermost
call made while `get_context_layer_stack().layers` is non-empty, with the layers, the
calling frames, and the fields whose value differs when the same snapshot is computed in
an empty `contextvars.Context`. A self-test (a state built and read inside
`config_context(PipelineConfig(...))`) was recorded with the differing field, so the
plugin records.

Runs: `tests/unit/pyqt_gui`, `tests/unit/agent`, `test_compilation_session.py`,
`test_u1_session_guards.py`, `test_mcp_dev_client_persistent_session.py` and the two new
test files (2396 passed, 2 failed, 1 skipped, 1 xfailed); and the seven entries of
`tests/smoke_tests.txt` (7 passed). **Recorded events: none in either run.** Limits: the
trace sees the pytest process only, not execution-server or CLI child processes; it sees
entered contexts, not the thread-local global config.

The two failures in the traced unit run are
`tests/unit/agent/test_agent_services.py::test_viewer_window_service_snapshots_running_viewer_explicitly_immediate`
and `::test_viewer_window_service_reports_malformed_viewer_response`
(`agent_path_policy_rejected`). The trace run set `TMPDIR` under the hidden `.claude/`
directory; not rerun without it, so whether they fail in the gate environment is not
known.

Sites by grep (three `config_context` entries in `openhcs/`, none in formbridge,
pyqt-reactive, pycodify, zmqruntime):

| Site | What the context supplies | State built or re-resolved inside | 3.0.3 |
|---|---|---|---|
| `openhcs/pyqt_gui/windows/dual_editor_tabs.py:52` `with config_context(pipeline_config), config_context(edit.step)` around `StepParameterEditorWidget(...)` | the plate's `PipelineConfig` and the step being edited, both entered without a scope id | No state is built: the widget takes the registered step state (`step_parameter_editor.py:168`). The form build reads resolved values, which re-resolves the step state only if it has no snapshot yet or has invalid fields. Not observed in the traced runs. | Also in the registered hierarchy: the plate config is the dataset state's delegate at the plate scope, and the step is the state at `edit.scope_id` (staged steps are registered by `stage_step`). By reading, nothing changes; not confirmed by a run. |
| `openhcs/interop/cellprofiler/pipeline_import.py:324` `with config_context(pipeline_config)` | the imported pipeline's `PipelineConfig` | None. It resolves a `LazyStepSourceBindingsConfig` object, not an ObjectState. | Not affected. |
| `openhcs/core/config.py:1470` `with config_context(PipelineConfig())` at import | a default `PipelineConfig` | None. Resolves `EMPTY_SOURCE_BINDINGS`, a lazy config object. | Not affected. |
| Headless MCP session (`openhcs/mcp/context.py:269`) | No `config_context` is entered. Global values came only from the thread-local config set by `ensure_global_config_context` (`session.py:1035`, `:1060`, `:475`); no scope `""` was registered. | Dataset, step and function states | Before this PR: context (thread-local) only. With this PR the global state is registered by `Session.__init__`, so the value is also in the registered hierarchy. |

No site was found where a value comes only from an entered `config_context`.

## Not done

- Gates (`verify_branch.sh os302`, `smoke_local.sh`, `guardrails_local.sh`, official30
  parity): not run. `origin/main` was not merged into the branch after it was cut from
  `d927ce673`.
- No PR opened.
- The untraced unit suite was not run on the `Session` change; the traced subset above is
  the only run that covers it.

## Coordinator correction (2026-10-12): pinned to 3.0.3, session change reverted

- The `Session.__init__` registration and the two deleted `None` branches are reverted.
  They made `test_restart_reconciles_saved_document_after_history_materialization` fail
  (`'NoneType' object has no attribute 'to_object'`: a session whose registry is cleared
  after it is built), raised the `Session` god-class ratchet by 5, and registered the
  global state conditionally in a second place (`pyqt_gui/app.py` being the first).
- The branch now pins ObjectState 3.0.3 (`9e711f8`). With 3.0.3 a replaced global config
  reaches existing states on their next read, so both wrong values found here (headless
  session, config-window save) are fixed with no OpenHCS change; their two tests pass
  and carry no expected-failure marker.
- The first gate run on this branch does not count: verify_branch's "also fails on main"
  check was wrong for the desktop restart test, because a stale `openhcs.egg-info` from
  2026-09-30 in the main checkout shadowed the installed metadata (it lacks
  `openhcs-basicpy`, so discovery raised there). It is moved to
  `.claude/stale-openhcs.egg-info-20260930`. The submodule in this worktree had also
  been moved to 3.0.3 during that run.
- Still open, for the job that follows ObjectState 3.0.4: one owner for the global
  config in OpenHCS (the registered global state), one registration site, and removal of
  `Session.global_config` as a second holder.

## Pinned to 3.0.4 (2026-10-12)

3.0.4 (`01f3a5d`): a state's resolved values no longer read a `config_context` the caller
has entered (owner decision: values depend on the object's place in the registered
hierarchy, not the caller), and saving the global state stores the saved global config
itself, so the result no longer depends on whether the caller saves or sets first.
Measured by the ObjectState agent on OpenHCS main: in the dual editor's normal path 0 of
58 state resolutions happen inside an entered context and values are identical; they
differ only when the step state has an unresolved change while the form is built, where
3.0.3 kept the entered config's value with source `None`.

Caller clean-up this enables, not done in this pin (see ObjectState #56):
`session.py:468`, `:1030`, `:1055`; `pyqt_gui/app.py:235-249`;
`pyqt_gui/services/window_handlers.py:100`; `pyqt_gui/windows/dual_editor_tabs.py:52`;
pyqt-reactive `config_window.py:182`, `:214-226`.
