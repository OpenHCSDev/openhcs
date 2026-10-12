# R1c: cold start of function-catalog preparation

Branch `refactor/R1c-cold-start`. Continues item 2 of `R1-release-blockers.md`.

## What is wrong

`RegistryService.prepare_in_current_process` is what an execution server runs before it binds, and what the GUI's catalog child runs. It discovered the catalog and then ran the preparation hook of every registered callable, which JIT-compiles every Numba kernel in the tree. On a first start that is minutes of compilation for callables the session may never run, and nothing can be listed or executed until it ends.

Measured locally (Linux, 12 CPUs, serial, empty Numba cache and empty catalog cache, `.github/r1-debug/cold_prep.py`):

| Phase | Before | After |
| --- | --- | --- |
| import of the registry service | 0.7 s | 0.8 s |
| discovery (import 68 backend modules, probe skimage functions) | 18.5 s | 20.1 s |
| kernel preparation | 102 s of Numba compile self time, 665 compilations of 321 functions | 0 compilations |
| signatures, configuration declarations | 1.7 s | 0.3 s |
| total | 123.8 s | 21.1 s |

The "compiling" phase is Numba JIT only. No single kernel dominates (largest function 4.7 s over 48 signatures). `python -X importtime` shows no import above 0.7 s cumulative locally. A cProfile of discovery shows the rest: skimage behaviour probes (`rolling_ball` 5.6 s, `hough_ellipse` 3.5 s, `denoise_nl_means` 2.4 s), module imports about 6 s, and 63 138 `packaging.Requirement` parses (B6d's `_openhcs_requirements`, re-parsed for each of 613 queries).

Intel runner (`macos-15-intel`, previous agent, run `38155492658`): 69.7 s discovery, about 222 s kernels, 301 s total against a 300 s deadline.

PR #1217 does not shorten this: it changes what preparing one callable imports; serving readiness still prepared every callable.

## Target

Readiness is the catalog. A callable's kernels are prepared when a pipeline first uses it: `CallableContract.from_prepared_callable` already owns that (it prepares every target whose signature is not published). Every Numba kernel in the tree is `cache=True`, so Numba's own on-disk cache, keyed by source stamp, signature and CPU, carries a kernel compiled in the server to the forked workers and to later starts. No second cache is added.

## Done

- `prepare_in_current_process` discovers the catalog and prepares configuration declarations. It no longer runs callable hooks, forks cache workers or publishes signatures.
- `_openhcs_requirements` parses the installed metadata once per process.
- Checked that no hook changes a catalog signature: all 1035 prepare targets of the 269 callables resolve to the same canonical and runtime signatures before and after every hook ran (`.claude/prof/sigcheck.py`, local).

## Guards

- `tests/unit/test_catalog_readiness_work.py`: in a fresh interpreter, readiness performs 0 Numba compilations and completes 0 preparation operations; first use of `create_composite` completes at most one operation per target and compiles OpenHCS kernels from `numpy_processor` only. Counts, no wall clock.
- Rewritten to the first-use rule: `test_preparation_admission.py`, `test_processing_preparation.py`, `test_execution_server_startup_preparation.py`, `test_callable_abi_preparation.py`, `test_registered_configuration_source_readiness.py`.

## Behaviour removed (certificates)

- Whole-catalog kernel compilation before bind: **tests-only**. What the tests do not exercise: a worker forked before a kernel was compiled now loads it from Numba's disk cache instead of inheriting it; where no cache directory is writable each worker compiles for itself. A broken kernel now fails at first use, not at server start.
- Signature publication at readiness: **derived** (`from_prepared_callable` snapshots the signature after preparing).

## Remains

1. Intel timings. Runs queued on the debug workflow: `38218985682` (before, head `2e5ab83a`) and `38220080786` (after, head `16e2cc64`, also times first use of four callables). Read with `gh run view <id> --log`; step A prints `TOTAL wall` and the largest gaps.
2. **Official30 parity has not passed.** One run under flock ended `1 failed` in 436 s: the first case (`ExampleColocalization`) raised `OpenHCS ZMQ client entered without a connected endpoint` and the other 29 were skipped, so no value was compared. That message is the known symptom of another worktree's server on the same port, but this change alters server startup, so it is not ruled out as the cause. Next step: read the execution-server log of that run under `.claude/pytest-parity`, then rerun `.claude/prof/parity.sh` (it needs `OPENHCS_CP_NATIVE_REFERENCE_ROOT` and `OPENHCS_REFERENCE_EXPORT_PIPELINES_ROOT`; without them the test skips and exits 0). Do not merge before 30/30.
3. Delete `.github/workflows/r1-debug.yml` and `.github/r1-debug/` once item 1 is read.
4. `PreparationCacheBatch`, `PreparationCacheWorker`, `can_prepare_in_child`, `cache_operations` and `cache_preparation_operations` in `openhcs/core/processing_preparation.py` have no production caller now; delete with their tests.
5. Discovery itself (20 s locally, 70 s on Intel) is untouched apart from the requirement parse. Candidates: the slow skimage probes; on macOS check `matplotlib.font_manager` in step E of the debug run.
6. The branch carries merges of B6d (#1221, needed for discovery on Intel where `openhcs-basicpy` is not installed). It conflicts with #1217 in `prepare_in_current_process`: keep #1217's registry completion, drop its per-callable preparation.

## Done when

The Intel debug run shows cold readiness well under 300 s, parity is 30/30, and the debug workflow is deleted.
