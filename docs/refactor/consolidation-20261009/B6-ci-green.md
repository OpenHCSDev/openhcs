# B6: main's CI green

**Head audited:** `openhcs` `main` at `84e7a2904` (#1193). **Rules:** [00-RULES.md](00-RULES.md). **Input:** the last completed runs on main: Integration Tests 38116770859 (`b468e7359`), Website 38110269836 and Documentation 38116770933. Integration Tests last passed on main at `fc1f94632` (2026-09-24). Documentation had not passed in the last 1,000 main runs.

## What was wrong

**Three workflows were red on main because of about twenty independent causes.** Most of them only CI exposes: the installed wheel with `--import-mode=importlib`, Windows, Intel macOS, xcb under Xvfb, path filters, and jobs nobody watched. The table gives each cause, its fix, and its certificate where something was deleted.

| Job(s) | First cause | Fix |
|---|---|---|
| Website | The job installed a five-package roster, then imported `openhcs`, whose import graph needs numba. The `paths:` filter only listed `openhcs/__init__.py`. | Install the candidate through `install_ci_candidate` with the `dev` extra, because `pytest.ini`'s addopts need pytest-xdist. Trigger on `openhcs/**` and `external/**`. |
| Documentation (`validate_docs`) | 950 findings: 141 of 155 pages had stale editorial audits (828 changed and 78 deleted authorities), plus 10 false "missing path" findings. | The path regex now matches whole repository paths and covers `packaging/`. All 141 pages were re-read against the diff of each stale authority since its reviewed version, wrong claims were corrected (see the commit), and digests were pinned after review. B6's own later edits were compared and re-pinned. |
| Documentation (sphinx `-W`) | PolyStore and pyqt-reactive had agent run logs outside every toctree. zmqruntime's API page listed members removed by L3. | Deleted the logs (**contract**: Q4, validation logs nothing links to). zmqruntime's page derives its members with plain `:members:`. |
| unit-tests (collection) | 14 test modules imported a sibling test module by bare name, which fails under importlib mode. | Import through the `tests` package; guard in `test_ci_import_guards.py`. |
| unit-tests (abort, exit 134) | An in-process MCP transport created a `QCoreApplication`, so a later `QWidget` aborted. | The session creates its `QApplication` first (`tests/conftest.py`). |
| code-quality | 412 unformatted files since the last success. A test used Python 3.12-only f-string quote reuse, which is a syntax error on 3.11. | Black over this PR's changed files; quote fixed. Main's baseline becomes this PR's green head. |
| structural ratchet | Black wrapping and B6 fixes grew six classes past their budget. | Cohesive method groups moved into inherited mixins: `MainOutputSliceProjectionMixin`, `FunctionCoreDebugMixin`, `CustomFunctionSourceFilesMixin`, `SessionDebugMixin`. Catalog policy moved to module functions. Four unused main-window theme methods and `SourceImageProvenance.source_component_identity` were deleted (**unused**: no caller, menu, bridge or string reference). |
| Windows (every ZMQ job) | `tests/conftest.py` used `os.getpgid`. zmqruntime's `startup_owner` reopened the lock file that portalocker holds (mandatory locks give PermissionError). | Process-group reaping only on POSIX. zmqruntime reads and writes the owner record through the held handle (0.6.2). |
| Windows | NumPy exports uint32 as format `'L'`; custom-function sources were written in text mode, which changes their hashes; SIGINT can't be sent to a child; chmod doesn't make a directory read-only and `os.access` ignores ACLs; autocrlf rewrote checksummed `.cppipe` files; packaged knowledge paths were longer than MAX_PATH. | Native granularity accepts both formats. Sources are persisted as exact bytes. The CLI treats Ctrl+Break as Ctrl+C. Writability is decided by an actual file-creation attempt, and the test denies writes with an ACL. `.gitattributes` keeps committed bytes (`* -text`). Recipes are placed by case name within a declared path budget. |
| Intel macOS | `openhcs-basicpy` is excluded by marker, but the catalog imported its module. The kernel cache compiled serially because macOS has no `sched_getaffinity`. | Modules declare `REQUIRED_DISTRIBUTIONS`, and the catalog excludes those whose package markers leave them out. Workers come from `os.cpu_count()` where affinity is unavailable. |
| python-314 | ObjectState read a class's own annotations through `__dict__`, which 3.14 no longer populates. mahotas sat only in an extra, but core catalog modules need it. | ObjectState uses `inspect.get_annotations` (2.1.1). mahotas is a core dependency. |
| gui-tests (13) | Stale tests after U1/U5. | Rewritten against the session-backed plate manager and the current stubs. |
| backend-microscope, boundary, OMERO | STEP_INPUT filters matched virtual names instead of stored source paths. Passthrough outputs dropped their producer's filename qualifier. BaSiC read `.metadata` off plain arrays. `OMEROLocalBackend` had no `is_dir`. The metadata document was written to local disk for a virtual backend. Viewer tests used `ViewerType` members. The GUI journey test ran in headless jobs. Several integration tests had gone stale. | Fixed at each owner: `SourceImageIdentity.filter_paths`, producer qualifiers, `ImagePayload.of`, `OMEROLocalBackend.is_dir`/`is_file` (PolyStore 0.6.1), `OpenHCSMetadataTarget.hosts_metadata_document` (not for a `VirtualBackend`), viewer families, and the GUI journey moved to gui-tests. |
| Official30 real-viewer smoke | `required_scalar_components` pooled contributors across runtime planes and dropped `site`, so napari rejected the stack. | Contributors are grouped per plane (`contributor_groups`). |
| Installed demo (Windows, Intel macOS) | The one-plane label projection (#477) lived only on `MatchImageStackLabels`; the skeleton step used `SliceAlignedLabels`. | The projection is owned by `ObjectLabelInputExecutionMode` (**derived**: `MatchImageStackLabels`' copy deleted). Dataset rows carry the finished execution's error. |
| desktop live MCP | The smoke read the catalog before the GUI's endpoint was up. Requestless UI-bridge operations received the connection in the request slot. | `execution_services_prepared` future; connection passed by keyword. |
| wheel-integration | The MCP smoke sent `wells` (G2 renamed it `partition_values`). Bio-Formats tests ran without the declared Fiji bundle. | `partition_values`; the job restores and prewarms the bundle. |
| pypi-dependency-readiness | Pinned submodule sources differ from their release tags. | Version bumps: zmqruntime 0.6.2, PolyStore 0.6.1, ObjectState 2.1.1 (pycodify's change shipped in main's 0.2.0). Floors raised. **The job stays red until the owner merges and tags the three library PRs.** |

## Guards

- `tests/unit/test_ci_import_guards.py`: no test module imports a test-tree module by bare name.
- `tests/unit/test_ci_package_boundaries.py`: the website job installs the candidate with the dev extra.
- `tests/unit/test_build_website.py`: the website job triggers on `openhcs/**`.
- `tests/unit/test_validate_documentation_audit.py`: repository paths match only whole paths.
- `tests/unit/test_build_mcp_knowledge_assets.py`: every packaged resource fits the Windows path budget.
- `tests/unit/test_library_registry_discovery.py`: marker-excluded distributions are left out of the catalog, while a required but missing one fails.
- `tests/unit/test_dataset_access.py`; `external/zmqruntime` held-handle owner-record test; `external/PolyStore/tests/test_omero_virtual_paths.py`.

## Done when

Website, Documentation and Integration Tests are green on this PR's head, or each remaining red job names its exact cause and owner (see the PR's final status).

## Lockstep library PRs (owner merges and tags)

- OpenHCSDev/ZMQRuntime#29 (0.6.2; docs; startup lock)
- OpenHCSDev/PolyStore#38 (0.6.1; OMERO `is_dir`; docs logs)
- OpenHCSDev/ObjectState#26 (2.1.1)
- OpenHCSDev/PyQT-reactive#21 (docs logs)

## Handoff

**Branch `refactor/B6-ci-green`, head `abf42ae1b` plus this receipt commit, merged with main `625150118`. PR #1195. GitHub Actions stalled before any job ran on this head, so nothing after `f419cb3bb` has a completed CI run.**

### Last completed CI runs

- **`f419cb3bb` (merged with main `eb64b3c13`): 36 jobs passed, 7 failed.** Website, Documentation and Refactor Guardrails were green. This is the last trustworthy picture.
- **`2e0deafe6` (merged with main `44980dfe2`): 27 jobs failed.** Fixed since, unverified (see below).

### Root causes fixed, with commits

| Cause | Commit |
|---|---|
| Docs path regex matched inside longer paths | `c9de5fab0` |
| Website installed a package roster; needs dev extra; path filter; shared `pages` concurrency group | `6bccc4d6d`, `5544c445f`, `ce529e459` |
| Sibling test-module imports under importlib mode | `6bccc4d6d` |
| `os.getpgid` on Windows; top-level import in GUI smoke | `62752cf33` |
| 141/126/127 stale documentation pages (three rounds, after each main merge) | `e59901e76`, `b2fb1bcd2`, `297a423d5` |
| Library docs: orphaned logs, removed zmqruntime members | `6669b3401`, `f3eb57aa9` |
| zmqruntime startup-owner lock on Windows | `333d3e0ab` (library PR ZMQRuntime#29) |
| Windows uint32 format; custom-function bytes | `47724ccd4`, `d5172f398` |
| Stale GUI tests; catalog race; requestless UI-bridge call; `partition_values` | `f59da9b8f`, `03ca14cc9`, `c3ab99415`, `87e4df3ff` |
| Marker-excluded distributions in the catalog (Intel macOS basicpy) | `c1013dd51` |
| BaSiC `.metadata`; STEP_INPUT filter paths; viewer families; GUI journey job | `c00a652d4`, `35abb00d6`, `4b1dec1e2`, `2eb48fb9d`, `dbae3e0b4` |
| mahotas core dependency; measured CLI child environment | `5e519401f`, `42f51b7a7` |
| OMERO `is_dir` (PolyStore#38); metadata document for virtual backends | `54e87d5b4`, `956326e3e` |
| Passthrough filename qualifier; adapter config; watchdog; stale synthetic tests | `89269b9a8`, `0f0ad9f7c`, `0d83e1e16`, `34556a1ac` |
| ObjectState own annotations on 3.14 (ObjectState#26) | `fac0519e5`, re-based to 2.1.1 in the first main merge |
| Ratchet: mixins, dead theme methods, catalog policy functions | `239953c4c`, `ab03ba7ba` |
| Packaged recipe paths over MAX_PATH; macOS serial kernel preparation | `35833f3a5`, `ded24279e` |
| Runtime-plane axes dropped from streams (napari settle) | `7066af9f3` |
| Windows read-only datasets, Ctrl+Break, one-shot write probe | `433b26fef`, `e1a1719d3`, `c74b2bd55` |
| Wheel job Fiji bundle; `.gitattributes` exact bytes | `e82ae3398`, `fbe17e02d` |
| One-plane label projection; demo error surfaced; `ViewerType.value` | `5de70ef71`, `88e22432e` |
| Unit session QApplication before MCP transports | `f322e395b`, `a5ce88b63`, `d43533f90` |
| `PARTITION_COUNT` in observation-export test | `b14856fbd` |
| E1 boundary: export scope and UI action status | `7379deb90`, `f0498a630` |
| Unit job split into three serial groups | `542f7ffeb` |

### Still red at the last completed run (`f419cb3bb`)

| Job | First cause | Owner |
|---|---|---|
| pypi-dependency-readiness | Pinned ObjectState 2.1.1, PolyStore 0.6.1 and zmqruntime 0.6.2 have no release tags | owner: merge and tag ObjectState#26, PolyStore#38, ZMQRuntime#29 |
| unit-tests | Cancelled at the 45-minute limit with 63% run. `test_custom_function_events.py` alone took 9 minutes (200 `gc.collect()` calls on a large heap). Of 48 failures before the cut, 29 are in `known.fail`; 18 pass locally on the merged tree; `test_declaration_selected_discovery.py::test_examplehuman_selected_source_uses_same_declaration_owner` fails on main `44980dfe2` too and is not in `known.fail` | job time: B6 (split unverified); the test: unowned, needs an owner |
| official30-headless-parity (macOS 3.14) | ExampleHuman `cells/zernike_*` values differ from the native reference; Linux 3.12 and 3.14 pass | parity owner (Zernike numerics off Linux) |
| official30-headless-parity (Windows 3.14) | ExampleImagingFlowCytometryObjectsInGrid `ssc/zernike_phase_*` values differ | same |
| official30-parity-required | Aggregates the two above | same |
| desktop-candidate-live-mcp and desktop-installer-source-test (macos-15-intel) | Cold function-catalog preparation runs past the smoke's 300-second deadline (it passed once at about 200 s) | owner decision: performance work or the budget |

### Unverified because CI stalled

- The E1 boundary fixes (`7379deb90`, `f0498a630`); locally the four integration tests and the GUI journey pass.
- The three-group unit job (`542f7ffeb`). The earlier xdist attempt (`f8062d2cd`) lost a worker in `test_mcp_server.py` under xcb and was replaced.
- The Website per-ref concurrency group (`ce529e459`).
- The third documentation round and re-pins after `44980dfe2` and `625150118`; `validate_docs.py` passes locally on every target and the OpenHCS Sphinx `-W` build passed locally after round two.
- Windows-only fixes confirmed by one run each but not on this head: read-only probe (`c74b2bd55` never ran on Windows), `.gitattributes`.
- An earlier CI-only segfault in `tests/unit/pyqt_gui` teardown under xcb was not reproduced or root-caused; it has not recurred since `f322e395b`.

### Why 27 jobs failed after merging main `44980dfe2`

**E1 left two boundaries half-migrated on main, and every job that runs a dataset or the GUI smoke hit one of them:**

- `DatasetRunRequest.runtime_observation_export_scope` is an enum-view field, but the measured CLI passed the family class into it, and `RunDatasets` passed the enum member to `Session.observation_export_params`, which expects the family. Every `run_datasets` call failed: four integration tests in all 17 backend, boundary and OMERO jobs, the wheel MCP smoke and the GUI journey.
- `scripts/smoke_installed_gui.py` read `UiActionInvocationStatus.ACCEPTED`, which E1 replaced with the `ActionAccepted` class: all desktop installer and live-MCP jobs.
- The unit job failed separately on the xdist worker crash described above.

Main's own run at `625150118` had not started, so "main is red the same way" is inferred from the code being identical on main, not observed.

### Standing problem for the owner

**The documentation audit gate goes red on every surface merge.** Each merge changes authority files, which invalidates about 125 pages; B6 re-reviewed them three times in one day. Unless each surface re-reviews its dependent pages in its own PR, Documentation will be red again after the next merge.

### Also found, not fixed

- `openhcs/agent/services/config_service.py` `_default_value_repr` prints family-class defaults as `<class ...>` in the generated config reference.
- `openhcs/mcp/bootstrap.py` `--surface` help says the desktop surface hides headless tools; it does not.
- `scripts/check_basicpy_source.py` expects a `jax_func` decorator the module no longer uses.
- `polystore/atomic.py` `_try_acquire_lock` retries `PermissionError` until its 30-second timeout.
- About 20 pages still say "Plate Manager" where the window title is now "Datasets".
