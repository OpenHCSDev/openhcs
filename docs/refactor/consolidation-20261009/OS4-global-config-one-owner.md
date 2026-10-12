# OS4: one owner of the global config

Branch `refactor/OS4-global-config-one-owner`. Libraries: ObjectState 4.0.0 (`02393c4`),
formbridge 0.1.4 (`3ddc051`), pyqt-reactive 0.8.0 (`1c0f35f`).

## What is wrong (measured at `c603c82f0`)

The global config had four holders in the GUI process and a different set in the
headless one:

- `openhcs/pyqt_gui/app.py:235-249` stored the config twice (`set_global_config_for_editing`,
  `ensure_global_config_context`) and then registered a state built from the same object.
- `Session.global_config` (`session.py:338`) held a third copy; `Session.adopt_global_config`
  wrote the store again with a config the state already held; `initialize_datasets`
  (`:1030`) and its worker (`:1055`) re-stored the session's copy on every initialisation.
- The headless MCP session (`openhcs/mcp/context.py:269`) registered no state at all.
- `window_handlers.py:100` had a fallback setter on save; `main_window_workflows.py:220`
  forwarded the saved config to `adopt_global_config`.

P1: a fact with several writers that are kept equal by convention is a restated
relation; the copies are derived views or deleted.

## Target

- ObjectState 4.0.0: the state registered at scope `""` is the holder. Reads are
  `get_live_global_config` / `get_saved_global_config`.
- ONE registration site: `openhcs/authoring/session/lifetime.py::open_session`
  registers the state and starts the session; `close_session` ends the session and
  unregisters the state. GUI (`pyqt_gui/main.py`), headless MCP (`mcp/context.py`),
  the benchmark CLI and the test harness all start their session there. Whoever
  starts the session's lifetime registers the state; there is no "register if
  nobody did".
- `Session.global_config` is deleted; readers ask `get_saved_global_config(GlobalPipelineConfig)`.
- `Session.apply_global_config(config)` is the one way to replace the config
  (`set_global_config`, which routes to the registered state).
  `Session.adopt_global_config` is deleted; what remains of it is
  `Session.saved_global_config_changed()`, which only publishes `DatasetConfigChanged`.

## Status

See the sections below; filled in as sub-jobs finish.
