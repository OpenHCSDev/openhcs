# R1d: cold start of function-catalog preparation, with compilation kept in preparation

Branch `refactor/R1d-catalog-prepare-cold-start`. Replaces the closed PR #1222 (R1c).

## Owner decision

Every Numba kernel is compiled during catalog preparation
(`RegistryService.prepare_in_current_process` and its forked cache children), never at
first use. R1c deferred compilation and its own measurements showed first pipeline runs
18 to 33 s slower; that is rejected. This surface makes cold preparation faster while it
still compiles the whole catalog before readiness.

## What is wrong (measured on main `ac19abb49`, Linux, Ryzen 5 5500, 6 cores / 12 threads)

Probe scripts are scratch (`.claude/prof/`, not committed). Cold means an empty
`NUMBA_CACHE_DIR`, an empty catalog cache (`XDG_DATA_HOME`) and `OPENHCS_CPU_ONLY=1`
(the mode in which cache children fork).

| Phase | Wall |
| --- | --- |
| import of the registry service | 0.9 s |
| discovery | 18.6 s |
| kernel preparation in cache children | 23.1 s |
| kernel preparation left to the server process, serial | 9.5 s |
| signatures, configuration declarations | 0.8 s |
| total | 52.9 s |

1. **Discovery, 18.6 s.** Wall-clock attribution (no profiler):
   - `SkimageRegistry` 10.4 s, of which 10.2 s is `classify_function_behavior`: 164
     functions are each run on a 3x20x20 stack and a 20x20 plane to learn whether they
     accept a stack, a plane, and the rank they return. Three calls are 9.6 s of it:
     `rolling_ball` 5.1 s, `denoise_nl_means` 2.3 s, `hough_ellipse` 2.3 s. The other
     161 take 0.5 s together.
   - `OpenHCSRegistry` 7.3 s, of which 4.5 s is `_openhcs_requirements` re-parsing the
     installed metadata: 63 138 `packaging.Requirement` parses over 619 calls.
2. **Cache children, 23.1 s.** 31 children, one operation each, at most 12 at a time;
   mean concurrency 9.0 of 12; 198 CPU-seconds, 195 of them Numba compilation. The
   longest child is 19.8 s (`ShapeMeasurementBackendStrategy`), so the window is within
   3 s of that floor. 1091 compilations of 561 distinct kernel signatures: 56.5 s is
   the same kernel compiled by more than one child at once (9 children each compile
   `DenseArrayObjectLabelStorageStrategy.prepare_coordinates`, about 30 s of it).
3. **Serial tail, 9.5 s.** After the children the server compiles 86 more kernels on one
   CPU: 75 in 26 callable hooks declared with `@processing_prepare` (8.1 s) and 11 in two
   registry families that never declared persistent kernel work
   (`EdgeEnhancementStrategy`, `ImagePayloadUint8Strategy`; 0.8 s). A cache child only
   ever ran registry-family operations; a callable hook had no way into one.
4. **CI.** No workflow persists `NUMBA_CACHE_DIR`; every job compiles from nothing.

## Target

- Installed metadata parsed once per process.
- The behaviour probe stays the single source of each skimage contract (no table of
  answers), on the smallest arrays that give the same answers.
- Every preparation operation that compiles kernels runs in a cache child first; the
  server process loads what they cached.
- CI restores the Numba cache between runs.

## Guards

Written below under "Done" as they land.

## Done when

Cold preparation is measurably faster per phase, a second start compiles nothing, first
and second `run-well-throughput` runs are not slower than main, parity is 30/30.

## Progress notes (for a resumed run)

- [x] baseline measured
- [ ] requirement parse once
- [ ] probe size
- [ ] hooks in cache children
- [ ] families that compile but never declared it
- [ ] CI cache
- [ ] gates
