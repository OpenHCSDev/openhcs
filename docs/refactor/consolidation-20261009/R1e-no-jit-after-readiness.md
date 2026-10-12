# R1e: nothing is JIT-compiled after readiness

Branch `refactor/R1e-no-jit-after-readiness`. Follows R1d (#1225).

## Owner requirement

Every one-time cost is paid during function-catalog preparation, before the server
reports ready. After readiness no process (the server, its execution workers, the client
that converts and submits a pipeline) compiles a Numba kernel, and pipeline compilation
contains no one-time cost, because benchmarks time compilation and execution.
Compilation stays in preparation; a kernel found compiled late is moved into
preparation, never to first use.

## How it was measured

A `sitecustomize` module on `PYTHONPATH`, enabled by an environment variable, with no
product change: it registers a listener for Numba's `numba:compile` event (fired only
for a real compilation) and wraps `numba.core.caching.Cache.load_overload` (a disk-cache
lookup, hit or miss), and logs pid, role, function, signature and seconds per process.
The server's readiness and each request's compile and execute windows are marked by
wrapping `ZMQExecutionServer.prepare_runtime_capabilities`,
`ZMQExecutionServer._execute_pipeline` and `ZMQCompilationRequest.resolve`. Imports are
timed by wrapping each module loader's `exec_module`. Every run starts from an empty
`NUMBA_CACHE_DIR` and an empty catalog cache (`XDG_DATA_HOME`) with `OPENHCS_CPU_ONLY=1`.
The scratch version lives in `.claude/` (not committed); the counting part is committed
as `tests/integration/helpers/numba_trace/sitecustomize.py` for the guard.

## What is wrong (measured on main `557eb99b4`, Linux, Ryzen 5 5500, 12 threads)

Each row is one cold `run-well-throughput` run of `official30_portable_axis1.json`
(last row: `tests/integration/test_main.py`, ImageXpress 3D over ZMQ).

| Pipeline | Compiled after readiness | Disk-cache loads after readiness |
| --- | --- | --- |
| ExampleHuman, 1 worker | 0 in server, 12 workers, client | client 107 kernels, 0.74 s |
| ExampleHuman, 4 workers | 0 | client 107, 0.79 s |
| ExampleFly | 7 in the server process during execution, 0.91 s | client 178, 0.69 s; with 2 workers each worker loads the late kernel, 0.01 s |
| ExampleColocalization | 7 in the server process during execution, 0.77 s | client 92, 0.96 s |
| ExampleCometAssay | 0 | client 116, 0.50 s |
| cp_tutorial_3d_monolayer | 0 | client 112, 0.53 s |
| ExampleSpeckles | 0 | client 60, 0.59 s |
| stock OpenHCS pipeline (not CellProfiler) | 0 | 0 in every process |

1. **A kernel no preparation reaches.** The 7 compilations are
   `_linear_costes_sorted_events_numba`, its 5 callees and Numba's `max`.
   `NumbaNumpyColocalizationCostesBackendStrategy.linear_costes` branches on the data
   (`slope > 0`), and its `prepare_backend` passed only anti-correlated arrays, so the
   other branch was first compiled inside timed execution. A warm-up that calls a
   public method covers one data-dependent path.
2. **It is not the only one.** Asking every first-party `cache=True` dispatcher, after a
   full preparation, whether it has any compiled signature in memory or in Numba's disk
   index: 52 of 298 had none (8 more are `inline="always"` and never have one), in 22
   modules. Some are dead (never called); the rest are branches, 3D variants or dtype
   variants no warm-up reaches, and each would compile at first use.
3. **The client prepares kernels it never runs.** Converting a `.cppipe` built each
   callable's contract with `CallableContract.from_prepared_callable`, and so did
   `normalize_function_pattern`. In a process that has not run catalog preparation
   that runs every preparation hook of the callable: 60 to 178 kernels loaded from the
   disk cache (0.5 to 1.0 s), or compiled if the client gets there before the server
   has filled the cache. `run-well-throughput` does this in workspace preparation,
   before its pipeline clock; the GUI's pipeline editor calls the same function.
   Preparation changes no signature: computed before and after a full preparation, the
   canonical and runtime signatures of every catalogued callable are identical.
4. **Workers are forked before readiness and inherit what the server had loaded**, so
   R1c's observation ("each of 4 workers compiled the same 2 thresholding kernels")
   does not reproduce on main: the 12 workers are forked 0.25 s before readiness and
   compile and load nothing. They do not inherit what the server first imports later.
5. **Late imports.** After readiness the server first-imports 44 modules setting up the
   first request (0.06 s), 2 during compilation (0.01 s) and 60 during first execution
   (0.04 s); every worker repeats them on its first task (45 to 102 modules, 0.09 to
   0.13 s per worker). The first pipeline compile in a server session took 0.30 s and
   the second 0.28 s (ExampleHuman; 0.35 s and 0.44 s for ExampleFly, so within noise).

Not measurable here: pyclesperanto and CuPy program builds (no GPU on this machine).
`matplotlib.font_manager` did not appear among the late imports.

## Done

- **Kernels no preparation reached.** Each of the 52, plus the 6 Costes kernels the
  first measurement had already compiled late, was either deleted because nothing calls
  it or is now reached from its owner's existing preparation, through the public method
  real execution uses and with the dtypes and layouts its callers pass. No list of
  kernel names was added and no kernel body changed.
  - Covered: linear Costes with positively correlated data (`slope > 0`); alignment
    with a partial mask; granularity with `subsample_size=0.25` (the default) for
    float32 and float64; dense 3D object intensity (labels filling the volume); sparse
    parent/child relationships in the four layout pairs callers produce; `filter_objects`
    "parent with most overlap" (new `@processing_prepare(filter_objects)`); scikit-image
    region orientations (new `prepare_backend`, strided and contiguous columns);
    grayscale closing/opening for float32 and float64, writable and read-only; the Numba
    smoothing provider, masked and unmasked; weighted Otsu with repeated values (the
    counted branch, 7 kernels); the minimum threshold; the worm thinning kernel (new
    `@processing_prepare` for the three `untangle_worms` callables).
  - `label_geometry._numpy_124_svml_arccos` (added by #1224) exists only where the CPU
    has the SVML symbol; `prepare_arccos_kernels`, called by the size/shape kernel
    preparation, compiles the kernel this CPU uses and the portable one (a process
    started with AVX-512 disabled shares the cache and uses it).
  - Deleted: see certificates.
- **Authoring prepares nothing.** `CallableProjection.declared_contract()` reads the
  contract from the declaration without running a hook; `.cppipe` conversion
  (`module_artifact_contracts`, `module_artifact_declarations`, `primary_objects`) and
  `NormalizedFunctionGroup.from_chain` use it. The compiler's entry is
  `normalize_prepared_function_pattern` (used by `CompilationSession`): it prepares
  every enabled callable and then lowers, so a process with no catalog preparation (an
  in-process orchestrator) still prepares at compile time, before execution, as before.
  The client now compiles 0 and loads 0 kernels. It still imports the modules of the
  callables it converts (1.0 to 1.6 s, before the benchmark's clock): it needs the
  callable objects to build the pipeline it submits, and a separate process cannot
  inherit them. Published signatures are not sent from the server: the client reads the
  same signature from the annotations, which the census showed is identical.
- **Late imports.** `FunctionCatalogExecutionServer.prepare_runtime_capabilities` now
  also builds the storage backend registry (`polystore.base.ensure_storage_registry`)
  and completes the domain-extended family registries
  (`dataset_sources.discovery.discover_domain_registries`, which follows the registries
  as they are created; no module list), before the worker fork. Function-local imports
  with no cycle in `zmq_execution_signature`, `zmq_orchestrator_environment` and
  `zmq_execution_server` became module-level.

## Measurements (same machine; other agents' jobs were running, so wall times are noisy; counts are exact)

| | main | this branch |
| --- | --- | --- |
| Compilations after readiness, ExampleFly / ExampleColocalization | 7 / 7 (0.91 s / 0.77 s, in execution) | 0 / 0 |
| Compilations after readiness, ExampleHuman 1 and 4 workers, CometAssay, 3D monolayer | 0 | 0 |
| Kernel loads in the client | 60 to 178 (0.5 to 1.0 s) | 0 |
| Kernel loads in workers (ExampleFly, 2 workers) | 1 per worker | 0 |
| First-party kernels with no compiled signature after preparation | 52 of 298 | 0 of 278 (13 of them are `inline="always"` and have none by design) |
| Server imports after readiness: request setup / compile / execute (ExampleHuman) | 44 (0.059 s) / 2 (0.010 s) / 60 (0.043 s) | 0 / 2 (0.002 s) / 57 (0.029 s) |
| Imports per worker on its first task | 45 to 102 (0.09 to 0.13 s; 0.44 s when PolyStore's registry cache misses) | 1 to 58 (0.002 to 0.034 s) |
| Pipeline compile, first / second in one server session, ExampleHuman | 0.302 / 0.282 s | 0.181 / 0.176 s |
| Same, ExampleFly | 0.350 / 0.436 s | 0.296 / 0.273 s |
| Cold preparation, traced, six runs | 48.7 to 55.8 s, mean 52.3 (one 72.4 s outlier excluded) | 47.3 to 53.3 s, mean 51.0 |

Cold preparation is not measurably slower: the added warm-ups cost about 40 CPU-seconds
of compilation when timed alone and cold, spread over the cache children, and 17 dead
kernels fewer are compiled. The before/after compile times were taken hours apart under
different load; only "first equals second" within a session is a claim.

## Guards

`tests/integration/test_no_jit_after_readiness.py` (integration tier: a cold preparation
is the thing under test, about 90 s here; counts only, no wall-clock). One cold run, in a
child process, of the stock pipeline (`test_main.py`, ImageXpress 3D) and an imported
`.cppipe`, each over a real execution server, with
`tests/integration/helpers/numba_trace/sitecustomize.py` on `PYTHONPATH`.

- `test_no_kernel_is_compiled_or_loaded_after_readiness`: preparation compiled at least
  one kernel (so the counter works), and no process compiled or loaded a kernel after
  its server's readiness; a client may not at any time.
- `test_preparation_compiles_every_kernel`: derived from the code, not from a pipeline.
  At readiness every `openhcs` Numba dispatcher that is not `inline="always"` has a
  signature in memory or in Numba's disk index. Seen failing: with the worm hook's call
  removed it names `worm_geometry._skeletonize_loop_numba`.

What they cannot see: a kernel that has one prepared signature but is reached at run
time with another (dtype, rank, layout, read-only); only a pipeline that does so shows
it, and the two guard pipelines are small. Known candidates, not established as
reachable: grayscale closing/opening on integer images with the Numba provider; the
dense 3D intensity kernels and the threshold primitives are prepared for float32 and
writable float64 only. Kernels in a module nothing has imported by readiness are not
enumerated. The first guard was not run against main; main's behaviour there is the
table above. GPU program builds are not covered.

## Deletions (certificates)

**unused** (no reference outside the definition and re-exports):
`_scaled_second_channel_costes_numba`, `_scaled_second_channel_costes_sorted_events_numba`,
`_scaled_second_channel_costes_grouped_events_numba`, `_prefix_pearson_from_group_count_numba`,
`quantized_unit_interval_event_summaries` and their re-exports; in
`intensity_object_quantiles_numba`: `_group_starts_numba`, `_median_from_sorted_numba`,
`_quartiles_from_sorted_numba`, `_quantile_from_sorted_group`,
`_quantile_from_dense_sorted_group`, `_object_intensity_std_3d_numba`;
`shape._maximum_position_of_labels_numba`, `shape._radius_features_from_distance_image_numba`;
`zernike._score_intensity_zernike_moments_batch_numba` with `intensity_zernike_moments_batch`
(an exported name) and its three strategy methods;
`distance_propagation_numba._propagate_labels_numba`; `illumination._rank_median_uint16_2d_numba`,
`_select_uint16`, `_partition_uint16`; `morphology._fill_labeled_holes_from_components_numba`,
`_first_adjacent_foreground_label_numba`, `_seed_points_from_components_numba`,
`_restore_removed_declump_basins_numba` with the three `restore_removed_declump_basins`
methods; `_threshold_weighted_variance_unmasked_finite_numba`;
`_minimum_cross_entropy_threshold_numba`.

**tests-only** (a Numba override removed; the strategy now inherits the NumPy/SciPy
implementation for inputs production does not pass; tests of those inputs pass through
the inherited one):
- `morphology._block_labels_2d_numba`: the Numba `block_labels` override. Production
  reaches it only for images of 4 or more dimensions.
- `morphology._fill_labeled_holes_single_label_components_numba`,
  `_record_component_boundary_label_numba`: the non-boolean branch of
  `fill_labeled_holes_below_size`; the one production caller passes a boolean mask.
- `morphology._relabel_sequential_3d_numba`: both production callers are 2D.
What the interface admits and tests do not vouch for: the speed of those inputs, and bit
equality of the inherited implementation with the removed kernel on them.

## Not done, ranked

1. PIL plugin and imagecodecs loading at the first image read or write: 57 modules,
   0.03 s in the server's first execution and in each worker. The owner is PolyStore's
   disk backend: PolyStore PR #40 adds `BackendBase.prepare_process` and
   `prepare_storage_backends`; after its release the server calls that in place of
   `ensure_storage_registry`.
2. `openhcs.interop.cellprofiler.runtime.module_execution`: 0.002 s at first compile
   and per worker; a function-local import in `interop/cellprofiler/runtime/adapter.py`
   with a real import cycle.
3. First request setup is 0.014 to 0.021 s slower than the second with no import
   involved; cause not traced.
4. An in-process orchestrator (no server, no readiness) prepares at compile time what
   its pipeline uses; a function called directly, outside a pipeline, compiles at first
   use. Unchanged.
5. Signature variants listed under "What they cannot see".

## Gates (run on `4ff20c10d` plus this section)

- `verify_branch.sh r1e` (heavy slot): 11656 passed, 34 failed, 2 errors, 25 skipped;
  collected 11714, reported 11691, no crash lines; new failures against the known list: 0.
- Official30 parity (heavy slot, `official30.lock`, empty Numba and catalog caches,
  traced): `1 passed in 716 s`, the one test that compiles, executes and compares all
  30 cases. The trace of that run: after the first server's cold preparation, 0
  compilations and 0 cache misses in any process across the 30 cases; each of the 29
  later servers loads exactly the 286 signatures its own preparation loads
  (8294 = 29 x 286) and nothing after; the 360 workers and the client load nothing.
- `smoke_local.sh`: `smoke rc=0` (7 passed, GUI smoke exit 0).
- `guardrails_local.sh`: `guardrails rc=0`.
- Guards: `tests/integration/test_no_jit_after_readiness.py`, 2 passed (88 s).
- Touched unit tests: `test_callable_abi_preparation`, `test_processing_preparation`,
  `test_preparation_admission`, `test_function_catalog_zmq`: 117 passed.
