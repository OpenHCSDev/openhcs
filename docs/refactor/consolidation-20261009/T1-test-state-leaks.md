# T1: tests that fail in the suite and pass alone

Measured on `origin/main` d927ce673 (after MR1 #1226). Evidence: the 40 suite
logs in `.claude/verify/*_suite.txt`, per-file reruns, a mechanical bisect of
predecessors, and a leak scanner run over the whole suite. The scanner, the
scripts and the scan output are in `.claude/verify/t1-tools/` (not committed).

## What is wrong

Of the 42 ids in `known.fail`, 40 pass when their file runs alone. Three
separate pieces of process-wide state explain all 40 and the one recurring
failure outside `known.fail`.

| # | Leaker | Victims | State | Owner | Fix |
|---|---|---|---|---|---|
| 1 | Collection itself. `tests/unit` had no `__init__.py`, so pytest imported `tests/unit/test_x.py` as module `test_x`, while 26 test modules import each other as `tests.unit.test_x`. Every such module was executed twice, as two module objects. | `test_source_round_trip.py` (10 ids), `test_classification_two_vector_authoring.py` (collection error) | `sys.modules`: two identities for one file; every class in it exists twice and registers twice | The test tree (module identity is declared by the package structure) | `__init__.py` in `tests/unit`, its six subdirectories and `tests/core`. One file, one module, one name. |
| 2 | 13 test modules and 2 test support modules that declare members of production families at module level (for example `_IndependentPriorConsumerModule` in `test_classification_interop_boundaries.py`, a `CellProfilerModule`). Importing them during collection registers the member for the rest of the process. | 21 ids in `test_cellprofiler_{backend_public_api,comparison,compatibility_matrix,export_to_database,generic_special_input_binding,library_loading,processing_backend,special_io_declarations}.py`: every test that walks all registered modules meets a stand-in with no callable. Intermittent with file order: `test_cellprofiler_label_hull.py` (5), `test_object_measurement_empty_labels.py` (1), `agent/test_config_schema_authority.py` (1) | `Family.__registry__` of metaclass-registry families (300 registries, about 1470 members in a full session) | Legitimately process-wide (a class registry). Tests had no owned way to add to it: 20 tests hand-rolled `try/finally: del X.__registry__[k]`, the rest leaked. | `tests/family_registries.py`, wired in `tests/conftest.py`: members a test module declares at import are withdrawn after the import and are members only while that module's tests run; after every test each registry is put back (declared members removed, removed or replaced members returned). |
| 3 | Any test that sets the ObjectState global config and does not unset it. Bisected: `test_routed_composite_execution.py::test_reduced_channel_stack_is_the_next_steps_only_input[...]` | `test_source_binding_workspace.py::test_prepared_workspace_admits_declared_source_universe_without_rewriting_provenance[*]` (3 ids, failed in 7 of the last 11 suites, exactly the runs where the leaker ran earlier on the same worker) | `objectstate.global_config._saved_global_config_contexts` / `_live_global_config_contexts` (thread-local value per config type) | ObjectState: a process-wide value with no scope. Not changed here (library release); see Remainder 1. | Autouse fixture `restored_global_configs` in `tests/conftest.py`: captures every config type's saved and live value before a test and applies it after, with the library's own `GlobalContextValues.capture/apply`. |
| 4 | A pipeline worker run inside the pytest process (`worker_execution.py` calls `configure_native_thread_count(1)`, which writes `NUMBA_NUM_THREADS=1` and seven more variables into `os.environ`) in a test whose environment is restored afterwards. Not narrowed to one test: reproduced by replaying the worker's 323-file order of suite t1a in one process. | `test_skan_axon_artifact_contract.py::test_skan_axon_returns_columnar_rows_and_exact_label_plane_stack` (r1z, t1a): `RuntimeError: Cannot set NUMBA_NUM_THREADS to a different value once the threads have been launched (currently have 1, trying to set 12)` | `os.environ` plus Numba's launched thread pool, which cannot be changed once started | `openhcs.core.native_threading`: correct for a worker process, but tests run workers in the host process | `tests/conftest.py` calls the owner's `configure_native_thread_environment(1)` before anything is imported: the pytest process is an execution process from the start, so the worker's `setdefault` changes nothing. The same replay then passes. |

How each was established:

* Row 1 and 2: `pytest tests/unit tests/core -k <known files>` in one process
  reproduces 35 of the 42 with no test having run before them, so the state is
  set at import. With the `__init__.py` files 24 remain; with the registry
  mechanism 2 remain (both fail alone).
* Row 3: `predbisect.py` halves the predecessor list (1 file, then 1 test);
  the scanner diff of that one test names the two dicts; with the fixture the
  pair passes.

### Classes

Counted over ids that failed in a suite since the known-failure list was last
rebuilt (runs k1..r1z) plus `known.fail`:

* (a) order/state dependent: 44 ids (40 from `known.fail`, 3 in
  `test_source_binding_workspace.py`, 1 in `test_skan_axon_artifact_contract.py`).
  All fixed here.
* (b) load/timing dependent: 10 ids seen once to three times each, never alone
  (not all have a traceback, so some may be class (a) with a rare order).
  Not fixed; see Remainder 2.
* (c) fail alone on main: 2 ids,
  `test_bioformats_microscope_handler.py::test_openhcs_output_subdirectory_initializes_from_metadata_root`
  (`MetadataNotFoundError: No declared OpenHCS projection contains .../images_results`)
  and `test_installed_mcp_demo.py::test_portable_source_normalization_defers_catalog_and_execution_runtimes`
  (`pipeline normalization requested full catalog discovery`). Real defects,
  not state leaks. `test_k8_materialization_guards` and
  `test_declaration_selected_discovery` failed alone only on the branches
  that were being verified.

## Target

Membership of a family is declared once, by the class statement; removing a
test's member is derived from the same fact (the class was declared by a test)
and done in one place. No test carries cleanup code for a registry or for the
global config.

## The guard

The brief asked for an autouse fixture that fails the test that leaks. For the
two carriers fixed here the fixtures restore instead: a test cannot leak a
registry member or a global config, so there is nothing left to fail on, and
no test needs cleanup code. Failing would have required each of several
hundred tests to restate the cleanup.

Cost, measured with every `openhcs` module imported (300 registries, 1474
members): 0.95 ms per test for snapshot and restore of registries and global
configs, about 11 s over 11.7k tests. The class graph is walked again (43 ms)
only when a test imports a new module.

`tests/unit/test_family_registries_restored.py` tests the mechanism.

Known holes, kept with their own cleanup: a production class a test registers
under a new key (`test_produced_plate_source_selection.py:47`), and members
imported from a package a test writes to `tmp_path`
(`agent/test_declaration_selected_discovery.py:55,147`). Classes made with
`type(name, bases, ns)` are covered (their `__module__` is `abc`; no
production member is made that way, checked over all 1399 members).

## Deleted

All **derived** (the conftest mechanism now does what the copy did), tests only:

* Registry cleanup in 21 test files: `try/finally` with `del`/`pop` on
  `X.__registry__`, two `monkeypatch.setattr(X, "__registry__", dict(...))`,
  one `stand_in_members(X)` without released keys.
* Global-config save/restore in 6 test files, including the fixtures
  `preserve_global_pipeline_context` and `restore_benchmark_global_context`.

`stand_in_members(member, *keys)` with keys stays: freeing a production key
for a stand-in is the test's own statement, not cleanup.

No production code changed. Row 4's production question (a worker that runs
in the host process changes that process's environment and thread pools) is
Remainder 5.

## `known.fail` after this PR

Pass in the full suite (40): all ids of `agent/test_config_schema_authority.py`,
`test_cellprofiler_backend_public_api.py`, `test_cellprofiler_comparison.py`,
`test_cellprofiler_compatibility_matrix.py`, `test_cellprofiler_export_to_database.py`,
`test_cellprofiler_generic_special_input_binding.py`, `test_cellprofiler_label_hull.py`,
`test_cellprofiler_library_loading.py`, `test_cellprofiler_processing_backend.py`,
`test_cellprofiler_special_io_declarations.py`, `test_classification_two_vector_authoring.py`,
`test_object_measurement_empty_labels.py`, `test_source_round_trip.py`.
Still failing (2): the two class (c) ids above.

## Remainder, ranked

From the scanner run over the fixed branch (`t1-tools/scan2-summary.txt`;
number = tests that left the state changed). None of these is tied to an
observed failure yet except item 2.

1. **ObjectState global config has no scope** (production owner, library).
   The fixture here contains it for tests; in the product the same value
   crosses plates and sessions in one process. Same question for
   `ObjectStateRegistry` (`_states` 73 tests, `_change_callbacks` 260,
   `_snapshots` 55, `_timelines` 50, `_token` 449): about 50 hand-written
   `ObjectStateRegistry.clear()` calls in tests are the copies to delete once
   it has an owner.
2. **Wall-clock deadlines on child-process start (class b).**
   `test_mcp_dev_client_terminal_input.py` (`child.wait(timeout=5)`, 8 sites;
   failed in r1z and in two runs here), `agent/test_mcp_server.py::test_mcp_stdio_*`
   (`wait_for(session.initialize(), timeout=5)`; failed in the scanner run),
   and probably `pyqt_gui/test_function_catalog_projection.py` (3 ids),
   `pyqt_gui/test_ui_agent_bridge.py::test_two_ipc_ui_bridges_route_each_descriptor_to_its_exact_instance`
   (twice, both while the other worker ran `agent/test_mcp_server.py`),
   `test_axis_family_witness.py::...[zmq]`, `test_cellprofiler_closing_hotpath.py::...[numba]`
   (this one may be row 4 instead: it compiles with Numba).
   166 literal timeouts in `tests/unit`.
   Proposed owner: one session deadline (`pytest-timeout` is installed locally
   but not declared and not used in CI); declare it, set it in `pytest.ini`,
   delete the per-test start deadlines. Not done: needs a dependency and lock
   change, and tracebacks for the last five (all suite logs are `--tb=no`).
   B7's private socket root does not apply: these are CPU waits, not shared paths.
3. **Registry-derived caches are cleared from a hand-written list.**
   `CellProfilerModule.__init_subclass__` lists nine `cache_clear()` calls for
   eleven `lru_cache`s in `module_measurement_features.py`; they are cleared
   when a member is declared, never when one leaves. metaclass-registry has the
   mechanism (`_family_projection`, `_invalidate_family_projections`) but
   private; `tests/family_registries.py` imports the private name. Owner:
   metaclass-registry should publish the projection cache, the list of
   families and the test restore, and `tests/family_registries.py` should
   shrink to a call.
4. **Qt widgets left open**: 454 tests in 55 files leave top-level widgets
   (`test_plate_compile_connection_action.py` 176). Likely carrier of the
   order-dependent Qt segfaults seen earlier. With them:
   `ServiceRegistry._services` (261), `_GlobalFlashCoordinator` state (about 250),
   `ScopeColorService._scheme_cache` (269), `ScopeTokenService` caches (92).
5. **`os.environ` written in-process by production code**: thread-count
   variables (`OMP_NUM_THREADS` and seven more) after
   `test_routed_composite_execution.py` and `test_source_tile_geometry.py`;
   `OPENHCS_CPU_ONLY=true`, `OPENHCS_LOG_LEVEL`, `MPLCONFIGDIR`,
   `POLYSTORE_SUBPROCESS_NO_GPU` after `test_benchmark_control.py`;
   `JAX_PLATFORMS` after `pyqt_gui/test_gui_startup_progress.py`.
6. **Storage backends**: `polystore.base.storage_registry` and its aliases
   change in 168 tests (instances cached process-wide);
   `PreparationOperation._completed` grows in 107;
   `RegistryService._resolved_reference_callables` in 46.
7. Smaller: file descriptors grow in 71 tests (21 in
   `test_routed_composite_execution.py`), daemon threads left by 6,
   root/`openhcs` logger level changed by 3, `sys.path` changed by 2,
   context variables left set by Qt tests (`current_temp_global`,
   `context_layer_stack`).
8. The two holes of the registry mechanism listed under The guard, and the
   non-registry class containers tests add to (`MeasurementDialect._shared_instances`,
   `NapariControlAction._registry`, `CustomFunctionRuntimeRegistry`).

## Done when

Two consecutive suites and one in another order show no id outside
`known.fail`; smoke and guardrails pass. Results are in the PR.
