# R1: platform-specific CI failures that block a release

**Status: checkpointed mid-work on 2026-10-12. Nothing is merged, no PR is open, and items 1 and 2 are unverified on macOS and Windows.** Four branches from `origin/main` `a751b0eba`, one per failure. Fresh agents continue from the Handoff section.

## What is wrong

At the last completed CI run (`38155492658`, B6 head `d43533f90`):

- `official30-headless-parity` fails on macOS 3.14 and Windows 3.14 (Zernike values).
- `desktop-candidate-live-mcp` and `desktop-installer-source-test` on `macos-15-intel` exceed the smoke's 300 s deadline.
- `unit-tests` is cancelled at 45 minutes.
- `test_examplehuman_selected_source_uses_same_declaration_owner` fails on main.

## Target

Each failure fixed at its cause, in its own PR. No global loosening of the parity tolerance.

## Guards

- Item 4: `tests/unit/test_callable_contract.py::test_only_serving_readiness_reads_the_members_of_a_registry` (preparing a family never reads registry members); the previously failing test is the behavioural guard.
- Item 3: `test_collection_under_the_frozen_heap_still_reclaims_new_cycles`.
- Items 1 and 2: not written yet.

## Handoff

### Shared facts

- **B6's PR #1195 is still open.** Every log from run `38155492658` comes from B6's branch, which carries fixes main does not have.
- **`workflow_dispatch` cannot start a workflow that is absent from the default branch.** `.github/workflows/r1-debug.yml` therefore also runs on a push to `refactor/R1-*` whose head commit message contains a tag: `[r1 parity-macos]`, `[r1 parity-windows]` or `[r1 cold-intel]`. Trigger with, for example, `git commit --allow-empty -m "WIP: rerun [r1 parity-macos]" && git push`. Once the file is on main, `gh workflow run r1-debug.yml --ref <branch> -f target=parity-macos` (or `parity-windows`, `cold-intel`; optional `-f case="<names>"`) works too.
- Read results with `gh run view <id> --log` and `gh run download <id> -n r1-parity-macos` (or `r1-parity-windows`, `r1-cold-intel`).
- **Delete `.github/workflows/r1-debug.yml` and `.github/r1-debug/` before a PR is final.** They exist on the zernike and cold-start branches only.
- Actions was stalled for most of the session. At checkpoint, run `38196784224` (zernike branch) had finished its Windows job and its macOS job was still queued; run `38198397594` (cold-start branch, `cold-intel`) was queued. **Check both first.**
- The local machine had load average 24 to 28; local wall times are inflated. CPU seconds are the usable local measure.

### Item 1: Zernike parity off Linux — branch `refactor/R1-zernike-parity`, debug tooling only, no fix yet

**Found**

- The CI logs and artifacts of run `38155492658` name the columns but carry no values. macOS: ExampleHuman `cells/zernike_N_M` and `cytoplasm/zernike_N_M` (all 30 orders, 60 differences); ExampleImagingFlowCytometryObjectsInGrid `bf_cells_on_grid` shape Zernikes, `zernike_magnitude_*` and `zernike_phase_*` (103 differences). Windows: `ssc/zernike_phase_N_M_df_image` for m ≠ 0 only, magnitudes equal. **Both platforms also fail `cp_tutorial_translocation_final` `sample/thumbnail_raw_dna` and `thumbnail_raw_gfp`, which B6's table does not mention.**
- The default backend (`NativeNumpyShapeZernikeBackendStrategy`, `openhcs/processing/backends/cellprofiler/zernike.py`) zeroes the radial term where `radius_squared > 1`. The two or three pixels that define each enclosing circle sit at radius 1 ± one ulp, so a last-bit change in the circle moves a pixel in or out of the disk.
- The circle (`minimum_enclosing_circle_from_labels`, `label_geometry.py`) uses only exact IEEE operations except `arccos`, which decides ties. With AVX512 disabled (as parity requires) `arccos` is the platform libm's `acos`.
- **Linux reproduction (a hypothesis for macOS, not yet confirmed there):** on the labels the two workflows produce, perturbing `arccos` results by ±1 ulp at random changes 1 to 3 circles per image by a relative 1e-15, and shape Zernikes of those objects move by 1.6e-3 to 2.0e-2 (tolerance 1e-6). That would make this a magnitude difference caused by a discontinuity, not phase wrapping. Script: `.github/r1-debug/real_sens.py <directory of circle dumps>`.
- glibc `acos` is not correctly rounded: it differs from round-to-nearest on 301 of 209,874 distinct inputs recorded from the two workflows (`.github/r1-debug/cmp_dump.py`), and those 301 flip no decision there.
- A round-to-nearest `arccos` built only from `+ - * /` (double-double Newton step on `cos(y) - x`, Taylor `sin`/`cos`, three-part π/2, iterated to a fixed point) gave 0 wrong results in 70,000 inputs against mpmath, independent of the seed. Prototype: `.github/r1-debug/cracos.py` (run its self-check with `uv run --no-project --with mpmath python .github/r1-debug/cracos.py 40000`).
- **Windows cannot be debugged from main yet:** the Windows debug job on main fails before any Zernike with `ValueError: queue_rows must be a C-contiguous 1-D array with format I and writable` (fixed on B6's branch by `47724ccd4`). Cherry-pick that commit onto the debug branch, or wait for #1195.
- The Windows phase-only failure is probably a different cause: the phase of a near-zero moment is ill-conditioned (magnitude within 1e-6, phase free). Not examined.

**Done**

- `.github/workflows/r1-debug.yml`, `.github/r1-debug/run_case.py` (runs named cases, prints environment, `np.show_config()`, libm probes and a per-column value diff) and `.github/r1-debug/sitecustomize.py` (records labels, ids, centers, radii and every `arccos` input with the kernel's, `math.acos`'s and `np.arccos`'s result into `circles/*.npz`). Verified locally on Linux: both cases equivalent, 18 circle dumps, 9 intensity traces.
- The per-column diff in `run_case.py` compares rows by position and is wrong for wide tables such as `BF_cells_on_grid.csv`; diff the uploaded CSVs locally instead.

**Remains**

1. Get the macOS artifact. Compare its `arccos_libm` with glibc on the same inputs, and its `labels` with Linux, to confirm or refute the `acos` hypothesis.
2. If confirmed: replace the libm branch of `_numpy_124_arccos` with the round-to-nearest implementation (Numba), run the full 30-case parity under flock on Linux (it must stay 30/30, since round-to-nearest differs from glibc on about 0.14% of inputs), then rerun the macOS job.
3. Cherry-pick `47724ccd4`, rerun Windows, and examine the `ssc` phase columns with the intensity traces (`OPENHCS_ZERNIKE_INTENSITY_DEBUG_TRACE_DIR` is already set by the workflow).
4. Find the cause of the `thumbnail_raw_*` differences.
5. Add the Linux sensitivity test, remove the debug files, run guardrails, open the PR.

### Item 2: Intel macOS cold start — branch `refactor/R1-cold-start`, measurements only, no fix yet

**Found** (Intel runner, run `38155492658`)

- `desktop-candidate-live-mcp` (no `NUMBA_CACHE_DIR`, kernels compile serially in the server): 301 s total = 3.3 s import + **69.7 s "Discovering registered callables"** (about 35 s importing 68 modules, 24 s probing skimage functions, 17 s of that in `skimage.restoration`) + **about 222 s compiling kernels** + 5 s loading the catalog. Largest gaps: watershed 42.5 s, medial_axis→threshold 28.7 s, threshold→closing 26.3 s.
- `desktop-installer-source-test` (launcher sets `NUMBA_CACHE_DIR`, so B6's `ded24279e` forks workers): discovery 90 s, then 24 one-family workers ran for more than 193 s without finishing. **Forked workers were no faster than serial on the 4-CPU runner.**
- Local serial cold run: 196 CPU-s; Numba compile self time is spread over 665 compilations of 321 functions, the largest single function 9.7 s (`_weighted_projection_numba`, 48 signatures). There is no single hot kernel.
- Local forked run (12 logical CPUs): 81.7 s wall but 254.5 CPU-s against 196 serial. Each one-family worker recompiles shared callees, which would explain why 4 CPUs gain nothing.
- `PersistentNumbaKernelPreparation.can_prepare_in_child` requires `OPENHCS_CPU_ONLY` and a set `NUMBA_CACHE_DIR`. Only the installed launchers export the cache directory (`openhcs/desktop/deployment.py`); `pip install` users and the GUI smoke always compile serially.
- On main, macOS never forks workers (`os.sched_getaffinity` is missing); `ded24279e` is cherry-picked on this branch as `d32ae6731`.

**Done**: `cold-intel` job and `.github/r1-debug/cold_prep.py` (wall and CPU time per status row; `R1_NUMBA_EVENTS=1` for per-function compile time, `R1_NO_CHILDREN=1` to force serial, `R1_PROFILE=1` for a cProfile of discovery). Steps A to D measure serial, forked, warm and discovery.

**Remains**

1. Read run `38198397594` for the Intel numbers of steps A to D. Step B sets `HOME` to a fresh directory and may need adjusting.
2. Candidate speedup, untested: in `PreparationCacheBatch.populate_child_caches`, give each of the `worker_capacity` workers a batch of families instead of one family per worker, so shared callees compile once per worker. Compare total CPU seconds locally, then on Intel.
3. Candidate, untested: have the application set the Numba cache directory itself (after `ensure_source_checkout_external_paths()` in `openhcs/__init__.py`, before Numba is imported) so the launchers stop restating it.
4. If neither brings the Intel cold start clearly under 300 s, raise the deadline for that runner only, citing the step A measurement.

### Item 3: `unit-tests` time — branch `refactor/R1-gc-test-cost`, fix done, PR not opened

**Found**: the four `test_qt_adapter_mixed_native_lifetime_orders[*]` cases did not merely run slowly; **each hit the 120 s pytest timeout** (`Timeout (0:02:00)!`), 527 s for the file. Each case makes about 37 full `gc.collect()` calls, and a full collection walks the whole session heap (more than 3 s per call at 50% of the suite).

**Done**: an autouse fixture freezes the pre-existing heap (`gc.freeze()` / `gc.unfreeze()`) so collections cover exactly what the test allocates; no assertion changed. Locally the file went from 21.4 s to 1.67 s (11 passed); one collection from 0.05–0.19 s to 30 µs. Mutation check: removing `self.destroyed.connect(subscription.cancel)` from `signals.py` still fails 5 tests under the fixture. A canary test shows a new cycle is still reclaimed.

**Remains**: guardrails, PR. **Findings for B6b:** approximate seconds per file in the cancelled run: `test_custom_function_events.py` 527, `agent/test_agent_services.py` 166 (one case also timed out at 120 s: `test_repository_catalog_finds_nucleus_segmentation_from_callable_owner`), `test_cellprofiler_kernel_preparation.py` 111, `test_configuration_mirror_deletion.py` 103, `test_cellprofiler_static_deletion_gates.py` 99, `agent/test_mcp_server.py` 94. A session heap that costs more than 3 s per full collection suggests tests leak tracked objects across the session.

### Item 4: unowned failing test — branch `refactor/R1-selected-source-discovery`, fix done, PR not opened

**Found**: the test is not stale. `91f05c26b` (issue #763, 2026-10-05) made `CellProfilerModule` a `CompilerPreparedAutoRegisterFamily` whose hook reads every registry member, and `_scan_module_registries` also counted the members of every prepared family. Preparing any callable whose module imports `CellProfilerModule` therefore imported all 91 declarations. Pipeline import prepares callables since `5c3e12ecd`, so retrieving one knowledge-base example discovered the whole family (about 1.5 to 2.5 s extra locally; 73 backend modules loaded instead of 35).

**Done**: `RegistryService.prepare_in_current_process` now completes the registries its callables' modules use (`AutoRegisterRegistryPreparation.discover_module_registries`, previously uncalled), which keeps #763's requirement "discovered before READY". Preparing one callable only runs family hooks. `CellProfilerModule.prepare_registered_family` and its `CompilerPreparedAutoRegisterFamily` base are deleted (**derived**: readiness discovery now owns it); `AutoRegisterRegistryPreparationReport` and its counts are deleted (**unused**: only a test read `prepared_family_count`). 158 tests passed across the eleven preparation and discovery test files, including the target test.

**Verified on merged main `ae6ddace5` (2026-10-12)**: guardrails rc=0, smoke rc=0. Parity under flock: 27 of 30 equivalent in the full run; `ExampleYeastPatches`, `cp_tutorial_advanced_segmentation_final` and `cp_tutorial_beginner_segmentation_final` ended "Execution was cancelled" while two other worktrees started execution servers on the same port (7849); those three, rerun alone under the lock on another port, were equivalent with 0 differences. **Finding (owner: the parity test or the dispatch rules):** the lock covers parity runs only, and `_free_zmq_port_pair` picks the same first free port as every other ZMQ test on the machine, so an unlocked ZMQ test in another worktree can cancel a parity case. **Remains**: The readiness step discovers every registry referenced by callable modules, about 60 lazy registries; locally each took under 0.01 s and no new top-level package was imported in CPU-only mode. Not checked with GPU libraries installed.

## Done when

All four PRs merged, the three target jobs green on their runners, and the debug workflow deleted.
