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
