# W: The non-microscopy witness

**Head audited:** `openhcs` `main` at `01bc87913` (#1192; G1 to G7 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 5.**
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "Witness" and "End state". *Uses:* G1 `AxisFamily` and its roles, G4 `OpenHCSDatasetSource` and the openhcsdata writer, G6 wire-declared viewer axes, G7 runtime words and `RUNTIME_FOREIGN_NAMES`. *Builds:* the end-to-end witness, the kernel-wide ratchet, the dataset vocabulary (G7 handoff).

## What is wrong

**"Microscopy is one instantiation" was a claim: the remote-sensing witness ran only in-process, and the kernel still spoke plate and well outside the runtime modules.**

- The witness (`tests/unit/test_axis_family_witness.py`, `remote_sensing_witness_pipeline.py`) compiled and ran a pipeline with the orchestrator in one process and a thread pool. Nothing ran it over the ZMQ execution server, in worker processes or into a viewer.
- Run over ZMQ, it failed in the server: `LazyProcessingConfig.variable_components must hold values from ['site', 'channel', 'z_index', 'timepoint']; got RemoteSensing.Tile`. Every process the kernel spawns (the execution server through the import-authority bootstrap, `spawn` workers, viewers) imports the product package, and `openhcs/__init__.py:27` activated `Microscopy` unconditionally. The submitting process's family did not travel; only the microscopy family could be served.
- `AxisFamily` declared `__registry_key__ = "family_name"`, but `family_name` is assigned after registration, so the registry was always empty and `family_name` had no reader.
- Census at `01bc87913`, an AST scan of the kernel packages (`openhcs/core`, `runtime`, `constants`, `formats`, `serialization`, `utils`) for identifiers and identifier-shaped literals whose words include a microscopy word (`plate(s)`, `well(s)`, `site(s)`, `timepoint(s)`): **121 (module, identifier) pairs in 37 files.** Largest: `plate_image_inventory.py` 16, `openhcs_format.py` 11, `vfs_protocol.py` 9, `compiler.py` 9, `path_planner.py` 7, `compilation_session.py` 5. By name: `plate_path` 14 modules, `plate_root` 11, `PLATE` 10 (`FunctionStepExecutionScope.PLATE`), `plate_folder` 5, `CompilationPlateScope`/`PlatePathDeclaration`/`plate_scope` 3 each.
- The G7 handoff items, by occurrence in `openhcs/`: `plate_folder` 47 lines in 8 files, `plate_root` 153/17, `CompilationPlateScope` 11/3, `PlatePathDeclaration` 18/3; `plate_path` 999/45 (most of it the agent and UI layers' own plate vocabulary).
- `openhcs_format.py` carried verbatim copies of PolyStore's `get_subdirectory_name` and `resolve_subdirectory_path`.

## Target (as built)

- **The family travels to child processes.** `AxisFamily.activate()` (`core/axes.py:520`) also exports the family's `family_name` (`module:qualname`) in `OPENHCS_AXIS_FAMILY` (`core/axes.py:427`), so children inherit it as they inherit `sys.path`. A domain entry point calls `activate_entry_point()` (`core/axes.py:533`): the inherited family if there is one, else its own. `AxisFamily.from_family_name()` (`core/axes.py:545`) decodes the spelling by importing the declaring module. `openhcs/__init__.py:27` calls `Microscopy.activate_entry_point()`. The dead registry declaration is deleted; `family_name` now has its reader.
- **The witness domain is declarations only:** `tests/unit/remote_sensing_witness_domain.py` declares `RemoteSensing` (`Scene(PartitionAxis)`, `Band(ColourAxis)`, `Tile(TileAxis)`, `Date(TimeAxis)`, no stack axis) and its measurement dialect, and nothing else. The test module and the pipeline script import it (the test's duplicate declaration is deleted).
- **The witness runs three ways** (`test_pipeline_runs_end_to_end_through_the_kernel[direct|zmq|zmq+napari]`): in-process; submitted to a ZMQ execution server the script spawns, with two `spawn` worker processes; and the same with the middle step streaming to a napari viewer, whose window state is read back over its control port (one layer, stack axes `tile, band, date, scene`, 24 items with exactly the written scene/tile/band/date values). Each run checks the outputs, their maxima, the written `scenes/tiles/bands/dates` metadata keys and labels, the measurement header named by the domain's dialect (`reading,…`), and that no microscopy or CellProfiler module was imported. `test_child_processes_serve_the_parent_family` checks inheritance directly.
- **Dataset vocabulary** (G7 handoff), renamed with every caller, no aliases:
  - `DatasetSource.plate_folder` and the `plate_folder`/`plate_path`/`plate_root` parameters of the dataset-source and metadata-handler families (`dataset_sources/interfaces.py`, `source.py`, `openhcs_format.py`, `source_bindings_source.py`, `choice.py`, and their overrides in `microscopes/`) → `dataset_root`; `current_plate_folder` → `current_dataset_root`; `_resolve_plate_root` → `_resolve_dataset_root`.
  - `OpenHCSMetadataGenerator.create_metadata(plate_root=…)` → `dataset_root=`.
  - The path planner's `plate_path`/`plate_root`/`plate_scope`/`materialized_plate_root`/`main_plate_root` → `dataset_root`/`dataset_scope`/…; `MaterializedOutputPlan.plate_root` and `OpenHCSMetadataTarget.plate_root` → `dataset_root`.
  - `WorkspaceSourceProjections.plate_path` (and `VirtualWorkspaceSourceProjectionBuilder`, `projections_by_plate_path`) → `dataset_root`.
  - `CompilationPlateScope` → `CompilationDatasetScope`; `CompilationSession.plate_scope`/`plate_path` → `dataset_scope`/`dataset_root`; the compiler's `plate_path` → `dataset_root`.
  - `PlatePathDeclaration` → `DatasetPathDeclaration`.
  - In touched files: `AtomicMetadataWriter.reconcile_completed_plate` → `reconcile_completed_dataset`; the compiler's partition-filter locals and log text (`wells` → partition values).
- Two collisions the mechanical rename would have merged keep distinct names: `analysis_result_directories` (`workspace_root` is the source-workspace root, not the dataset root) and `OpenHCSDatasetSource.initialize_workspace` (`metadata_root` is the root the metadata walk resolves). PolyStore's own names are untouched (`VirtualWorkspaceBackend(plate_root=…)`, `StreamingSourceIdentity.plate_path`).
- `openhcs_format.get_subdirectory_name`/`resolve_subdirectory_path` are deleted; the three callers import PolyStore's.
- Census after: **72 pairs in 27 files** (−49). The remainder is pinned by the ratchet (Guards) and owned as listed under Handoff.
- **Docs:** 04-ARCHITECTURE "End state" records the owner's decision: the kernel distribution is **arraypipe** (`OpenHCSDev/arraypipe`, PyPI name reserved with 0.0.1); the stale "a separate kernel library is not warranted" line now points to it.

Production (Python under `openhcs/`): −641 +656. The +15 is the inheritance mechanism (`activate_entry_point`, `from_family_name`, the variable); the rename is line-neutral.

## Findings: kernel fixes the witness forced

| Kernel assumption | Where | Fix |
|---|---|---|
| Every spawned process serves microscopy | `openhcs/__init__.py:27` (`Microscopy.activate()`), reached by the execution-server bootstrap (`runtime/import_authority.py:50`) and `spawn` workers (`core/orchestrator/worker_execution.py:491`) | `AxisFamily.activate()` exports the family (`core/axes.py:520`); `activate_entry_point()` honours it (`core/axes.py:533`); `from_family_name()` decodes it (`core/axes.py:545`) |

No other kernel edit was needed: compile, the ZMQ submission (pycodified pipeline naming `RemoteSensing.Tile`), worker execution, metadata writing, the dialect-named measurement rows and the viewer's layer axes all followed the declaration.

Not a microscopy assumption, recorded for its owner: the napari viewer refuses Qt's `offscreen` platform and forces `xcb` (`runtime/viewer_protocol.py:866`, `QtPlatformName.OFFSCREEN` has `supports_interactive_viewer=False`), so the `zmq+napari` case needs an X server. CI's unit job runs under `xvfb-run`; without `DISPLAY` that one case skips. A headless viewer mode belongs to **L7** (streamviewer).

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Compiled plans (`MaterializedOutputPlan`, compilation sessions), ZMQ submissions, worker state | runtime | reset |
| `openhcs_metadata.json`, saved pipelines and configs | durable | unchanged: no stored key or saved name was renamed |
| `OPENHCS_AXIS_FAMILY` | process environment | set by `activate()`; never persisted |

## Deletion certificates

| Deleted | Certificate |
|---|---|
| `plate_folder`, `plate_root`, `plate_path`, `plate_scope`, `CompilationPlateScope`, `PlatePathDeclaration`, `reconcile_completed_plate`, `_resolve_plate_root` and the other renamed names | **contract** (renamed in lockstep; no backwards compatibility) |
| `AxisFamily.__registry_key__`/`__skip_if_no_key__` | **unused** (the registry was always empty; nothing read it) |
| `openhcs_format.get_subdirectory_name`, `resolve_subdirectory_path` | **derived** (`polystore.metadata_writer` owns both; the bodies were identical) |
| The test module's own `RemoteSensing` declaration; the integration conftest's process reaper | tests (moved: the domain module; root `conftest.py` `reap_spawned_processes`, which integration still applies to every test) |

**Tests-only** (behaviour the interface admits that no test exercises):
- Family inheritance is exercised for the execution server (import-authority bootstrap), `spawn` process-pool workers and a direct child. Not exercised: `forkserver` workers, prepared fork workers with a non-microscopy family, Windows, servers launched by the OMERO plugin or the MCP launcher, and a user shell that exports `OPENHCS_AXIS_FAMILY` (that process now serves the named family).
- The `zmq+napari` case runs only where an X server exists (CI unit job; locally it was run under a private Xvnc display).

## Guards

`tests/unit/test_axis_family_guards.py`:
- `test_kernel_domain_references_only_shrink` (new): over `KERNEL_MODULE_ROOTS` (defined in the test until P creates `openhcs/kernel/`), the set of (module, identifier) whose words include a microscopy word (each axis's one-word `name` and `metadata_collection_field`, and `plate(s)`; `channel(s)` is excluded as the NGFF/ImageJ dimension name) **equals** `KERNEL_DOMAIN_REFERENCES` (72 pairs), and the pin may not exceed `KERNEL_DOMAIN_REFERENCE_CEILING = 72`. A new name fails; a removed name fails until the pin shrinks.
- `test_kernel_ratchet_covers_the_runtime_guard` (new): the runtime modules are kernel modules and `RUNTIME_FOREIGN_NAMES` ⊆ the pin.
- `test_renamed_dataset_names_do_not_exist` (new): none of the old dataset names appears in `openhcs/`, `tests/`, `benchmark/` or `scripts/`.
- `RUNTIME_FOREIGN_NAMES` shrinks to P's four entries (`config.py` `PlateOutputDirectory`/`PlateOutputFile`, `PLATE` in `bundle_execution.py` and `worker_execution.py`); the two orchestrator entries are gone.

## Tests

Run one file per process. The guards (`test_axis_family_guards.py` 10, `test_g7_runtime_protocol_guards.py` 5, `test_dataset_source_guards.py` 5) and the witness (`test_axis_family_witness.py`: 13 pass, `zmq+napari` skipped without a display and passing under a private Xvnc display). 84 unit files touching the renamed code; 12 integration files; official30 parity (30/30). Failures that also fail on `origin/main` (same tests, same errors) are not regressions; they are listed in the PR body.

## New-case experiments

- A new domain today needs its axis family, its dialect, and an entry point; served over ZMQ it also needed a kernel edit (the server activated microscopy). After: the declarations module only; the family reaches every child by activation.
- A new kernel module that names a plate or a well today passes CI. After: the ratchet fails until the name is a dataset or partition word.

## Handoff

- **P:** `FunctionStepExecutionScope.PLATE` (10 kernel modules) and the `Plate{Input,Output}{File,Directory}` declarations (`vfs_protocol.py`, `config.py`); the plate-named modules `core/plate_image_inventory.py`, `core/plate_file_inventory.py` and `core/synthetic_plate_generation.py` (25 pinned names; their callers are the agent's plate inspection services); `debug_session_projection.py` `NoPlateDebugSessionPhase`; `path_cache.py` `PLATE_IMPORT`; `parser_metaprogramming.py` `plate_name`/`include_site`; `openhcs_format.py` `get_plate_name`/`get_plate_acquisition_datetime`/`PLATE_NAME`; `source_tile_geometry.py` `site`/`sites`.
- **L7 / PolyStore:** `StreamingSourceIdentity.plate_path` (spelled by `viewer_streaming_service.py`, `stream_component_semantics.py`, `streaming_config_factory.py`), `VirtualWorkspaceBackend.plate_root` and `metadata_writer`'s `plate_path` parameters; a headless (offscreen) napari mode.
- **P1:** the execution server's capability warm-up imports `processing/backends/cellprofiler` for any domain.
- **Compiler:** `PipelineCompiler` writes `zarr_config = {"all_wells": …, "needs_initialization": True}` that nothing reads beyond a `None` check (`compiler.py:509`, `materialization_flag_planner.py:109`); for the session lead to assign.
- The agent and UI layers (`agent/`, `mcp/`, `pyqt_gui/`, `ui/`, `authoring/`) keep "plate" where it is user-facing microscopy vocabulary (plate manager, plate inspection, `MainFlowMaterializationPlanSummary.plate_root`); they are not kernel modules.

## Done when

The guards pass; the witness passes direct and over ZMQ (and with napari where an X server exists); the touched test files show no failure that `origin/main` does not.
