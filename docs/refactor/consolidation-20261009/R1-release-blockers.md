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
- **Delete `.github/workflows/r1-debug.yml` and `.github/r1-debug/` before a PR is final.** Deleted on the zernike branch (Item 1); the cold-start branch still carries its copy.
- Actions was stalled for most of the session. At checkpoint, run `38196784224` (zernike branch) had finished its Windows job and its macOS job was still queued; run `38198397594` (cold-start branch, `cold-intel`) was queued. **Check both first.**
- The local machine had load average 24 to 28; local wall times are inflated. CPU seconds are the usable local measure.

### Item 1: Zernike parity off Linux — branch `refactor/R1z-zernike-parity` (surface R1z)

**Cause.** CellProfiler's minimum enclosing circle (`minimum_enclosing_circle_from_labels`, a port of centrosome's) picks the hull vertex with the smallest value of `pi - arccos(a) - arccos(b)`. Vertices that subtend equal angles (mirror images, co-circular points) are separated only by the last bit of that expression. The pick changes the radius by one ulp. CellProfiler's Zernike basis then zeroes pixels with `r**2 > 1`, and the pixels that define the circle sit at `r**2 = 1 ± one ulp`. The portable path called the platform `acos`, so each platform's rounding made its own pick.

**CellProfiler's own choice is ill-conditioned.** Its result at such a tie is rounding noise; the fixed references record what glibc produced. A robust rule (exact integer comparison, no pixel of the object outside its own enclosing circle) cannot match the references, because it would disagree with CellProfiler wherever CellProfiler dropped a defining pixel.

**Fix.** `_numpy_124_portable_arccos` is now `arccos` rounded to nearest, built from IEEE add, multiply, divide and square root only (series estimate, Newton steps on `cos(angle) - value` in double-pair arithmetic to a fixed point). No math-library call and no fused multiply-add takes part, so every platform computes the same bits. The AVX-512 SVML path is unchanged. The global tolerance is unchanged.

**Observed**

- Windows runner, before (run `38218984347`): ExampleImagingFlowCytometryObjectsInGrid not equivalent; 25 columns `ssc/zernike_phase_N_M_df_image` (every m ≠ 0). One object of 900 (row 636) differs: same centre, radius one ulp apart (3.6e-15). Its magnitudes differ by at most 4.8e-7 (inside 1e-6; the moments are about 1e-5), its phases by up to 0.52. No difference is a 2π wrap. The Windows `acos` differs from round-to-nearest on 4262 of 92866 distinct recorded inputs (glibc: 136).
- Windows runner, after (run `38220967518`): `equivalent=True` in both steps; that object's magnitudes equal Linux exactly and phases agree to 4.4e-16. The job is red only because `tests/conftest.py` called `os.getpgid` at teardown, which main has since fixed.
- Linux, after: the two cases equivalent; full 30-case parity under flock passed (1 passed, 673 s). glibc differs from round-to-nearest on 301 of 209890 distinct inputs of the two cases, and none of them decides a tie there.
- Synthetic labels: a consistent one-ulp change of one `arccos` value moves a shape Zernike of a 17-pixel object by 0.135 (two of its 17 pixels leave the unit disk). This is the unit test.
- macOS: **not observed.** The macOS jobs of runs `38218984347` (before) and `38220967518` (after) were still queued when checked on 2026-10-12; no macOS runner has executed the fix. The claim for macOS rests on the kernel using only IEEE add, multiply, divide and square root, and on the pinned bits in the unit test, which the regular macOS unit job runs.

**Guards**: `test_portable_arccos_is_rounded_to_nearest_where_math_libraries_disagree` (bits pinned, including six inputs glibc rounds the other way) and `test_enclosing_circle_tie_does_not_follow_the_platform_math_library` (forces another platform's rounding of one value and shows the 0.135 move; pins our circle).

**Supply map** (`--focus Zernike`): 21 classes matched; the existing owners of tolerance are `ZernikeDescriptorSparseNumericTolerance` and the `CellProfilerEquivalencePolicy` fields, which this change does not touch.

**Deleted** (runner experiments; nothing on main referred to them)

- `.github/workflows/r1-debug.yml`: **unused** (existed on this branch only; no workflow, script or test names it).
- `.github/workflows/r1-debug-case.yml`: **unused** (same; it also failed the guardrail that requires a `concurrency` key).
- `.github/r1-debug/` (`cmp_dump.py`, `cracos.py`, `probe.py`, `real_sens.py`, `sitecustomize.py`): **unused** (imported only by the two workflows above).
- `tests/integration/test_r1_debug_case.py`: **unused** (ran only when the debug workflow set `R1_CASES`; the 30-case parity test runs the same cases). The unit test that forces another platform's rounding stays.

**Thumbnails (not this cause, not fixed here).** In run `38155492658`, `cp_tutorial_translocation_final` also differed on macOS and Windows in `sample/thumbnail_raw_dna` and `sample/thumbnail_raw_gfp`. These are ExportToDatabase's `Image_Thumbnail_*` columns: the base64 text of a whole 200x200 PNG file (`_thumbnail_png_base64` in `openhcs/interop/cellprofiler/analyst_export.py`), compared as text. No `arccos` and no label geometry is involved. The encoder is integer work after an IEEE division (scale to uint8, Pillow resize, PNG save), and no other measurement of that case differed, so the input pixels were the same. Re-encoding the recorded pixels with the local Pillow (Linux x86-64) reproduces the recorded bytes exactly. The likely difference is therefore the compressed byte stream that the Pillow wheel's bundled zlib writes on each platform, not the picture; this was inferred, not observed, because the runner's thumbnail bytes were not kept. It is a parity-comparison question (compare decoded pixels instead of file bytes) and belongs to the surface that owns the equivalence policy. **The macOS and Windows 30-case parity jobs will stay red on this case after this PR.**

**Gates on head `6a835c3cf`** (origin/main `d927ce673` merged)

- `verify_branch.sh r1z`: `suite: = 36 failed, 11651 passed, 25 skipped, 359 warnings, 2 errors, 6 subtests passed in 1070.26s (0:17:50) =`; `collected 11711, reported 11688, crash lines 0`; `new vs known: 2`; `only on r1z:` (empty). The two new ones (`test_mcp_dev_client_terminal_input.py::test_long_terminal_command_reuses_original_parser_and_client[...]`, `test_skan_axon_artifact_contract.py::test_skan_axon_returns_columnar_rows_and_exact_label_plane_stack`) passed when rerun alone on this branch.
- `smoke_local.sh`: `smoke pytest exit 0 (131 s): 7 passed, 2 warnings in 128.05s (0:02:08)`; `smoke gui exit 0 (30 s):`; `smoke rc=0`.
- `guardrails_local.sh`: ratchet openhcs, scripts, benchmark exit 0; `38 passed`; `nra-r1 exit 0: "increased": []`; `guardrails rc=0`.
- 30-case parity under the official30 lock: `1 passed, 2 warnings in 810.30s (0:13:30)`, `rc=0`.
- The same four gates also passed on the previous head `01d1326d2` (parity `1 passed ... in 677.30s`), except guardrails, whose pinned tools could not import that hour because `metaclass-registry` 0.4.0 had just been published; the shared script now bounds it.

**Remains**

1. macOS: read the two queued runs if they ever start (`gh run view <id> --json jobs`), or read the macOS job of the next full matrix run.
2. Thumbnail comparison, above.
3. Hosts with AVX-512 enabled still use SVML's `arccos`, by the documented design. Parity disables AVX-512.

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
**Verified on `origin/main` `77bf7e803` merged in**: the file and `test_custom_function_lifecycle.py` pass (66 passed, 5.2 s); local guardrails end `rc=0`. PR opened; it remains to merge. **Findings for B6b:** approximate seconds per file in the cancelled run: `test_custom_function_events.py` 527, `agent/test_agent_services.py` 166 (one case also timed out at 120 s: `test_repository_catalog_finds_nucleus_segmentation_from_callable_owner`), `test_cellprofiler_kernel_preparation.py` 111, `test_configuration_mirror_deletion.py` 103, `test_cellprofiler_static_deletion_gates.py` 99, `agent/test_mcp_server.py` 94. A session heap that costs more than 3 s per full collection suggests tests leak tracked objects across the session.

### Item 4: unowned failing test — branch `refactor/R1-selected-source-discovery`, fix done, PR not opened

**Found**: the test is not stale. `91f05c26b` (issue #763, 2026-10-05) made `CellProfilerModule` a `CompilerPreparedAutoRegisterFamily` whose hook reads every registry member, and `_scan_module_registries` also counted the members of every prepared family. Preparing any callable whose module imports `CellProfilerModule` therefore imported all 91 declarations. Pipeline import prepares callables since `5c3e12ecd`, so retrieving one knowledge-base example discovered the whole family (about 1.5 to 2.5 s extra locally; 73 backend modules loaded instead of 35).

**Done**: `RegistryService.prepare_in_current_process` now completes the registries its callables' modules use (`AutoRegisterRegistryPreparation.discover_module_registries`, previously uncalled), which keeps #763's requirement "discovered before READY". Preparing one callable only runs family hooks. `CellProfilerModule.prepare_registered_family` and its `CompilerPreparedAutoRegisterFamily` base are deleted (**derived**: readiness discovery now owns it); `AutoRegisterRegistryPreparationReport` and its counts are deleted (**unused**: only a test read `prepared_family_count`). 158 tests passed across the eleven preparation and discovery test files, including the target test.

**Verified on merged main `ae6ddace5` (2026-10-12)**: guardrails rc=0, smoke rc=0. Parity under flock: 27 of 30 equivalent in the full run; `ExampleYeastPatches`, `cp_tutorial_advanced_segmentation_final` and `cp_tutorial_beginner_segmentation_final` ended "Execution was cancelled" while two other worktrees started execution servers on the same port (7849); those three, rerun alone under the lock on another port, were equivalent with 0 differences. **Finding (owner: the parity test or the dispatch rules):** the lock covers parity runs only, and `_free_zmq_port_pair` picks the same first free port as every other ZMQ test on the machine, so an unlocked ZMQ test in another worktree can cancel a parity case. **Remains**: The readiness step discovers every registry referenced by callable modules, about 60 lazy registries; locally each took under 0.01 s and no new top-level package was imported in CPU-only mode. Not checked with GPU libraries installed.
**Remains**: full 30-case parity under flock (readiness preparation changed), guardrails, PR. The readiness step discovers every registry referenced by callable modules, about 60 lazy registries; locally each took under 0.01 s and no new top-level package was imported in CPU-only mode. Not checked with GPU libraries installed.

## Done when

All four PRs merged, the three target jobs green on their runners, and the debug workflow deleted.
