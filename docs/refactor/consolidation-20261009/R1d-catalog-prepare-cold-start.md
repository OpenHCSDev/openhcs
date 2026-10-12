# R1d: cold start of function-catalog preparation, with compilation kept in preparation

Branch `refactor/R1d-catalog-prepare-cold-start`. Replaces the closed PR #1222 (R1c).

## Owner decision

Every Numba kernel is compiled during catalog preparation
(`RegistryService.prepare_in_current_process` and its forked cache children), never at
first use. R1c deferred compilation and its own measurements showed first pipeline runs
18 to 33 s slower; that is rejected. This surface makes cold preparation faster while it
still compiles the whole catalog before readiness. Nothing here changes when a kernel is
compiled; the cache-worker machinery stays.

## What is wrong (measured on main `ac19abb49`, Linux, Ryzen 5 5500, 6 cores / 12 threads)

Probe scripts are scratch (`.claude/prof/`, not committed). Cold means an empty
`NUMBA_CACHE_DIR`, an empty catalog cache (`XDG_DATA_HOME`) and `OPENHCS_CPU_ONLY=1`.

1. **No cache child forks unless `NUMBA_CACHE_DIR` is set.**
   `PersistentNumbaKernelPreparation.can_prepare_in_child` required a non-empty
   `numba.config.CACHE_DIR`. Only the desktop launcher scripts and the benchmark
   harnesses set that variable; no CI workflow does, nor does a plain server start. In
   that case the server compiled all 665 kernel signatures on one CPU: 94.5 s here, 0
   children (the 222 s on `macos-15-intel` is this path). Numba was caching all along:
   it wrote 614 cache files into `__pycache__` beside the sources during that run.
2. **Discovery, 18.6 s.** Wall-clock attribution, no profiler:
   - `SkimageRegistry` 10.4 s, of which 10.2 s is `classify_function_behavior`. skimage
     declares no dimensionality, so each of 164 functions is run on a 3x20x20 stack and
     a 20x20 plane to learn whether it accepts a stack, a plane, and the rank it
     returns. Three calls are 9.6 s: `rolling_ball` 5.1 s, `denoise_nl_means` 2.3 s,
     `hough_ellipse` 2.3 s. The other 161 take 0.5 s together. The cost comes from
     default parameters applied per pixel (a radius-100 ball, 7x7x7 patches in a
     21-wide search, all pixel pairs), so it scales with the probe array.
   - `OpenHCSRegistry` 7.3 s: `_openhcs_requirements` re-parsed the installed metadata
     on each of 619 calls (63 138 `packaging.Requirement` parses), and each module
     source was parsed to an AST about four times (529 parses for 141 modules).
3. **Cache children (with the directory set), 23.1 s.** 31 children, one registry
   operation each, at most 12 at a time, mean concurrency 9.0 of 12; 198 CPU-seconds,
   195 of them Numba compilation. The longest child is 19.8 s, so the window is within
   3 s of its floor: the batch partitioning already saturates the machine.
4. **Serial tail, 9.5 s.** After the children the server compiled 86 more kernel
   signatures on one CPU: 75 inside 26 callable hooks declared with
   `@processing_prepare` (8.1 s) and 11 in two registry families that compile Numba
   kernels but never declared it (`EdgeEnhancementStrategy`,
   `ImagePayloadUint8Strategy`; 0.8 s). A cache child only ever ran registry-family
   operations; a callable hook had no way into one.

## Done

- `can_prepare_in_child` no longer requires `NUMBA_CACHE_DIR`. Numba always persists a
  `cache=True` kernel (the configured directory, else `__pycache__` beside the source,
  else its per-user directory) and refuses to define the kernel otherwise, so the
  conjunct restated a fact Numba owns, wrongly.
- `_openhcs_requirements` parses the installed metadata once per process (ported from
  R1c; the only thing taken from that branch). `_parsed_source` parses each module
  source once for the three questions discovery asks of it.
- The behaviour probe runs on a 3x8x8 stack and an 8x8 plane
  (`RuntimeTestingRegistryBase.PROBE_STACK_DEPTH`, `PROBE_PLANE_EDGE`). The probe stays
  the one source of each contract; no table of answers was added. Checked: all 164
  skimage functions classify identically at plane edges 20, 16, 12, 10, 8, 6 and 4
  (50 rejected, 74 flexible, 32 pure 2D, 2 pure 3D, 6 volumetric-to-slice), and with
  different random arrays. A stack depth of 2 does change six `max_tree` functions, so
  the depth stays 3. Editing `unified_registry.py` invalidates existing catalog caches
  through the source-mtime signature.
- `PreparationCacheBatch` runs declared hooks in cache children after the registry
  children finish, so a hook loads what the registries cached and compiles only what is
  its own. Hooks share one child per CPU: a child costs about a second of CPU before it
  does anything, and one child per hook (26 children) measured 14 child-seconds more for
  no shorter a window. A hook bound to a declared operation
  (`ObjectSizeShapeKernelPreparation().execute`) is that operation and is not run twice.
- `EdgeEnhancementStrategy` and `ImagePayloadUint8Strategy` inherit
  `PersistentNumbaKernelPreparation`, so their kernels are compiled by children.
- The server process now compiles 0 kernels itself on a cold start (was 86, or 665
  without the directory). A second start compiles 0 in the server and 0 in all 45
  children.

## Measurements

Cold preparation, 12 threads, `NUMBA_CACHE_DIR` set:

| Phase | main | this branch |
| --- | --- | --- |
| import of the registry service | 0.9 s | 0.6 s |
| discovery | 18.6 s | 7.8 s |
| kernel cache children | 23.1 s (31 children) | 27.7 s (33 registry + 12 hook children) |
| kernels compiled by the server, serial | 9.5 s (86 compilations) | 1.3 s (0 compilations) |
| signatures, configuration declarations | 0.8 s | 0.5 s |
| total | 52.9 s | 37.9 s |

| Other cold cases | main | this branch |
| --- | --- | --- |
| `NUMBA_CACHE_DIR` unset (CI, plain server start) | 0 children; 94.5 s serial compile, 103.6 s total measured with this branch's discovery fixes and the old rule (R1c measured 123.8 s on main) | 37.6 s, 45 children |
| restricted to 4 physical cores (`taskset -c 0-3`) | 60.4 s | 49.5 s |
| second start, warm caches | 9.8 s | 7.7 s |

`run-well-throughput`, ExampleHuman, `official30_portable_axis1.json`, wall time of the
whole command (server start, preparation, run, shutdown), caches emptied before the
first run:

| Workers / wells | main first | main second | branch first | branch second |
| --- | --- | --- | --- | --- |
| 1 / 1 | 64.7 s | 22.1 s | 46.6 s | 19.0 s |
| 4 / 4 | 69.4 s | 22.4 s | 50.7 s | 20.0 s |

Pipeline `total_seconds` inside those runs is unchanged (1.14 to 1.22 s with 1 worker,
1.52 to 1.66 s with 4): nothing is compiled during execution on either tree.

## Guards and tests

- `test_declared_hooks_run_in_cache_children_before_the_server_runs_them`: module and
  callable hooks each run once in a child, a hook shared by two callables once, and
  none without CPU-only mode.
- `test_new_declarations_populate_children_then_share_parent_hook_readiness` (existing):
  a hook bound to a registered operation is not run a second time.
- `test_installed_requirements_are_parsed_once_per_process`.
- Two existing assertions changed with the rule they stated: with `CACHE_DIR` empty a
  persistent family now can prepare in a child.

## Behaviour changed (certificates)

- The `NUMBA_CACHE_DIR` requirement for cache children: **derived**. Numba's cache
  locator owns whether a kernel persists, and it always does for a kernel that could be
  defined. What tests do not exercise: a source tree and home directory that are both
  read-only make Numba raise when the kernel module is imported, before any child.
- Probe array size 20 to 8: **tests-only**. Checked on the installed scikit-image only;
  CuPy and pyclesperanto (the other two runtime-tested registries) are not installed
  here, so their classification at edge 8 is unverified.
- Hooks now also run in children. In fixture-capture mode
  (`OPENHCS_CAPTURE_CELLPROFILER_FIXTURES_DIR`, a developer option) a hook that calls a
  capturing function writes its warm-up arrays from the child as well as from the
  server. `CellProfilerCallableKernelPreparation` keeps its own capture check.

## Not done, and why

- **Persisting the Numba cache in CI.** Numba validates each cache index against the
  source file's `(mtime, size)` and absolute path (`numba/core/caching.py`). The jobs
  that start a server install freshly built wheels, so every restored entry would be
  stale. Making it work needs the installed sources' mtimes normalised in each job and
  an exact key over all kernel sources (a prefix fallback would run stale machine code
  after a cross-file kernel edit, which Numba does not track). That key misses on every
  PR that touches `openhcs/**/*.py`. The CI gain in this PR comes from the first item
  under "Done": those jobs never set the variable, so they compiled serially.
- **Compiling shared kernels once.** 56.5 of 195 compile seconds are the same kernel
  compiled by several children at once (26 s is
  `DenseArrayObjectLabelStorageStrategy.prepare_coordinates` in 10 children). Removing
  it needs a declared order between operations; it moves that work in front of the same
  children, so the longest chain is not shorter and the expected gain is under 2 s.
- **Children outside CPU-only mode.** Without `OPENHCS_CPU_ONLY` no child forks and the
  server compiles serially (the 94.5 s path above). The rule predates this surface,
  presumably because forking after CUDA initialisation is unsafe; not changed, and not
  measured separately.
- **Discovery remainder (7.8 s)**: about 4 s importing 165 backend modules (under the
  profiler) and 3 s of probes, of which `rolling_ball` is still 1.4 s. `matplotlib.font_manager`
  was not attributable in wall time on Linux; macOS was not measured.
- Intel macOS was not re-measured; no debug workflow was added.

## Done when

Gates in the PR description.

## Probe size on the GPU libraries (checked on the desktop, read-only, 2026-10-12)

Run against the desktop's installed libraries (cupy-cuda12x 13.3.0, cucim-cu12 25.6.0,
pyclesperanto 0.19.0, RTX 2070 SUPER) with the registries of its checkout (`97bc871cb`),
classifying every candidate function at several probe sizes and comparing with 3x20x20:

| Registry | Functions | Differ at 3x8x8 | Differ at 3x6x6 | Differ at 2x8x8 |
| --- | --- | --- | --- | --- |
| pyclesperanto | 273 (168 flexible, 24 volumetric-to-slice, 2 pure 3D, 79 rejected) | 0 | 0 | 0 |
| CuPy / cuCIM | 133 (70 flexible, 25 pure 2D, 5 volumetric-to-slice, 1 pure 3D, 32 rejected) | 0 | 0 | 0 |

The smaller probe did not make pyclesperanto discovery faster in that run (5.2 s at edge
20, 27.7 s at edge 8, run in that order in one process); not investigated, the sizes ran
once each.
