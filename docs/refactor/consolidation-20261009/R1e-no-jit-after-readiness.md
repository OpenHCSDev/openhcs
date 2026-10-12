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
