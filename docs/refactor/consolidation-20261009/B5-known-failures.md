# B5: main's known test failures to zero

**Head audited:** `openhcs` `main` at `01bc87913` (#1192). **Rules:** [00-RULES.md](00-RULES.md). **Input:** `.claude/verify/main_01bc879.fail`, 273 failing or erroring tests in 95 files.

## What was wrong

**The suite on main had 273 known failures, so central verification could only say "nothing got worse".** I re-measured one file per process (`-p no:randomly --timeout=300`, offscreen Qt, worktree `--basetemp`). The failures split into five causes:

- **Stale tests (most).** Production moved and the tests did not. B1b's `owns_module` stopped the registry claiming probes defined in test modules (5 files). Stubs lacked fields that new code reads. G1/G3/G5/G6/G7 renamed or reshaped types. Behaviour changed on purpose in #395, #419, #440, #536, #547, #785 and bee5f223a. Each stale case was traced to the commit that changed it, by bisection where the log did not say.
- **Production bugs:**
  - presets that could not compile
  - receipt replay that always raised
  - a code-document validator that rejected its own renderer's output
  - CellProfiler parameter help missing from a cached catalog
  - image-set expansion dropping every anchor
  - QA sidecars counted as terminal outputs
  - a contract that could not be built
  - unsynced release metadata
  - stale script imports
- **Isolation:**
  - AF_UNIX sockets under a deep `tmp_path`
  - a shared `/tmp` visible-source root
  - subprocesses that imported first-party libraries from the venv `.pth` checkout instead of the source under test
  - a path meant to be outside the checkout that was inside it
- **Environment.** The native extensions were not built in the measuring checkout. This accounts for about 23 tests.
- **External.** torch is not installed, and vispy needs native OpenGL, which offscreen Qt lacks.

## Target

- **Every test has an outcome.** It either passes in its own process, or it names its owning surface and a reason below. No skip or xfail hides a failure.
- **External requirements are declared:**
  - `requires_framework(MemoryType.X)` (`tests/unit/framework_requirements.py`) and the `native_opengl` fixture (`tests/unit/native_opengl.py`) skip with a stated reason.
  - `tests/conftest.py` stops the session with a build instruction when a native extension declared by its `_*_native.cpp` source is not built.
- **Shared isolation lives in one place**, `tests/conftest.py`: `unix_socket_dir` (a short socket directory) and the autouse `visible_source_root` (a private visible-source root).

## Production changes (`openhcs/`, −56 +209)

The additions are new mechanisms that close a missing relation, not copies: catalog-declaration preparation, literal `get_function` admission in code documents, the `inspection_only` sidecar role, loose-input calibration, and missing parameter docs. Each change appears in the table with its cause.

- **`OpenHCSFunctionCatalogDeclaration.prepare_declared_callable`.** Fresh scans and cached reconstruction both call it. `CellProfilerModule` implements it with its setting help. Before this, that code was `_install_callable_parameter_help`, which only `require_callable` reached.
- **`SourceBindingMatchedImageSet.expand`.** With no file-selecting binding, it keeps every anchor, as the candidate matcher declares.
- **Presets.** `materialization_results_path` is plate-relative, and `LooseOperaPhenixNeuriteInputs` gains `source_voxel_spacing`.
- **Merged CellProfiler, interop and viewer batches.** The table covers these changes:
  - return-slot uniqueness
  - `inspection_only`
  - code-document `get_function` admission
  - receipt-replay `declared_axes`
  - removal of the unused `save_images.context`

## Guards

This surface adds no new structural guards; it restores the suite. Some existing guards were rewritten against the current mechanisms:

- The MCP cold-build PyQt6 guard is unchanged; it stays failing and is owned by U4.
- The runtime-resolution cache guard now admits only the identity-bound cache family.
- The static deletion gates follow the rule 1a and rule 1b renames.
- The configuration-consumer audit derives role-declared slot fields and classmethod receivers.

## Done when

Every file in the list passes in its own process, or each remaining failure has an owning surface and reason in the table.

**Final run on this branch:**

- 84 of the 95 files pass.
- The remaining 35 tests in 11 files are listed below, each with an owner.
- 238 of the 273 known failures are fixed. Of those, 5 are now declared external skips: 4 need native OpenGL, and the torch NLM file is the fifth (its jax cases run).

## Remaining failures (owned)

| test | owner | reason |
|---|---|---|
| agent/test_mcp_distribution_runtime.py (2) | U4 | headless MCP imports PyQt6 (`mcp/execution.py` QtCore, `pyqt_reactive.core` QtWidgets) |
| test_installed_mcp_demo.py (1) | F1 | rendered `get_function(key)` resolves through the prepared catalog and imports runtimes |
| test_template_crop_pipeline_execution.py (16), test_volume_projection_fixture.py (4), test_derived_role_publication_435.py (2), test_cellprofiler_static_deletion_gates.py (1) | G3 | singleton selected-plane identity (#395); payload axis and provenance derivation; parallel projection branches |
| test_registered_object_output_boundaries.py (2) | K3 | row-ordinal shape vectors misassign values when the declared ids include empty labels (7ce29a1d2) |
| test_artifact_publication_journey.py (4) | K2 | empty-document reconciliation, then untyped object-label addresses |
| test_bioformats_microscope_handler.py (1) | G4 | opening a results directory under projection-scoped metadata (a8ab61dc5) |
| test_cellprofiler_identify_tertiary_output_abi.py (1) | K5 | one spec in two positional return slots (larger == smaller) cannot form a contract since cbf1857f7 |
| test_neurite_outgrowth.py (1) | owner decision | since 4b4f6e611 the crossing core is unowned; the test expects it to be owned |

## Per-test receipt

| test | class | action | cert |
|---|---|---|---|
| agent/test_agent_services_package.py::test_agent_services_package_does_not_import_service_graph | isolation | subprocess dropped PYTHONPATH and imported whatever `openhcs` the venv's editable finder points at (a deleted temp tree); now sets PYTHONPATH to the source tree under test | - |
| agent/test_declared_callable_documentation.py (4) | stale test | probes defined in the test module are no longer claimed by `OpenHCSRegistry.metadata_for_declared_callable` (B1b `owns_module`, 2517d0960); probes now project through the custom-function path `project_custom_function`, the real route for out-of-package declarations | - |
| agent/test_compile_selector_authoring.py::test_new_declaration_composes_independent_settings_without_consumer_edits | stale test | same cause; the new declaration is projected and published as an ephemeral custom function (removed in finally) so the rendered `get_function` key round-trips | - |
| agent/test_knowledge_base_service.py::test_knowledge_base_retrieves_canonical_image_source_guide | stale test | the image-sources guide grew to 22.6k chars (b57afe146); the request asked for 20k and then asserted non-truncation; request now uses the service cap `MAX_DOCUMENT_CHARS` (assertion unchanged) | - |
| agent/test_mcp_distribution_runtime.py (2 cold-build PyQt6) | production (owned) | `openhcs.mcp.execution` imports QtCore and `pyqt_reactive.core.__init__` eagerly imports QtWidgets; a headless MCP server without PyQt6 is U4's stated target ("MCP DTOs no longer need PyQt6; second consumer: the MCP server, including hosted HTTP"). Left failing, owner U4 | - |
| agent/test_mcp_affine_inspection_progress.py (2), agent/test_mcp_plate_stream_progress.py (1), agent/test_mcp_process_resource_lifetime.py (1) | isolation | AF_UNIX sockets were bound under `tmp_path`; with a worktree `--basetemp` the path exceeds `sun_path` (~108 bytes): `OSError: AF_UNIX path too long`. New fixture `unix_socket_dir` (tests/unit/agent/conftest.py) gives a short private temp dir | - |
| agent/test_mcp_self_description_contracts.py::test_openhcs_metadata_preserves_null_component_labels | stale test | monkeypatched private `_load_metadata`, which no longer exists; now writes a real `openhcs_metadata.json` and reads it through a real handler | - |
| agent/test_mcp_startup_feedback.py::test_registered_catalog_tool_routes_original_pending_control_statuses_without_native_launch | stale test | stub faked `is_connected()`; since ab9b591e4 the catalog requires the connection handshake (`connected_endpoint`) and answers a PING; stub now attaches a real `AttachedEndpointConnection` and answers PING | - |
| agent/test_official30_knowledge_examples.py::test_mcp_capabilities_discover_examples_architecture_and_function_docs | stale test | default context's catalog requires a live execution endpoint (825eec2d1); test now passes the in-process `FunctionCatalogService` (endpoint transport is covered by test_function_catalog_zmq) | - |
| agent/test_plate_inspection_service.py::test_plate_inspection_reads_no_main_openhcs_output_subdirectories | stale test | `get_pixel_size` requires declared physical calibration (source_metadata spacing, #440); fixture gained `source_metadata` with 0.65 um spacing; OK status and 0.65 assertions unchanged | - |
| agent/test_progressive_authoring_context.py (2, first_use/pipeline) | stale test | custom-function guide grew to 15k chars (b57afe146) past the default 12k read; request now asks for `MAX_DOCUMENT_CHARS`; capability search used `query`, the request field is `text` | - |
| agent/test_public_callable_enum_ingress.py (22 errors) | stale test | probes defined in the test module are no longer registry-owned (B1b `owns_module`); fixture publishes them as ephemeral custom functions and removes them after | - |
| agent/test_synthetic_plate_mcp_progress.py::test_real_mcp_generation_survives_post_inspection_inactivity_window[True] | stale test | heartbeats repeat the latest reported phase (4ab076890); assertion matches `Generate synthetic plate: <phase>: still running` | - |
| agent/test_user_facing_help_projection.py::test_repository_catalog_has_actionable_parameter_help | production bug | 80 CellProfiler callables lacked parameter help on the cached-catalog path: setting help was only installed by `require_callable`, which cached reconstruction skips (regression from 6927a02a1). New `OpenHCSFunctionCatalogDeclaration.prepare_declared_callable` hook called by both fresh scan and cached reconstruction; `CellProfilerModule` implements it (renamed from `_install_callable_parameter_help`). Added missing Args docs: `neurite_outgrowth_metaxpress_pixels`, `export_to_database` workspace settings, `save_images.context` | - |
| agent/test_user_facing_help_projection.py::test_preprocessing_guidance_projects_from_callable_owners | stale test | compared catalog doc to the memory wrapper's docstring; since #461 the catalog serves the raw declaration's prose; compares against `resolve_raw_runtime_callable()` | - |
| test_completed_output_publication_lifecycle.py (5) | stale test | step-plan and metadata-handler stubs lacked fields the worker and workspace projection now read (`visualize`, `streaming_configs`, `artifact_outputs`, `future_artifact_inputs`, `requires_main_flow_checkpoint`, `source_workspace_root`); stubs completed, assertions unchanged | - |
| test_configuration_consumer_coverage.py::test_every_visible_config_leaf_has_typed_production_consumer | stale test | the static consumer audit missed (a) `ClassName.factory(...)` receivers (PolyStore reads `shared_ack_port` through `ViewerStreamBackendKwargs.from_kwargs(...)`), and (b) G1's role-declared viewer slot fields read by name in `AxisRoleModeDisplayConfig.slot_for_axis`. Audit now infers classmethod receivers and derives slot-field consumption from `role_mode_fields()` (asserting the reader still uses it) | - |
| test_czi_brain_axon_cellbody_demo.py::test_czi_contributor_samples_only_declared_crop_planes, test_loose_operaphenix_neurite_example.py::test_neurite_example_compiles_with_declared_loose_file_identities | production bug | presets set `materialization_results_path=output_root / "results"`, outside the output plate root; the path planner has rejected that since 6f8c327c8, so both presets could not compile. Presets now use plate-relative `Path("results")`; the two tests that pinned the old value assert the new one | - |
| test_loose_operaphenix_neurite_metaxpress_example.py::test_compact_example_compiles_the_full_ordered_channel_stack | production bug | the MetaXpress recipe needs physical calibration (#440) and loose TIFFs copied away from `Index.xml` carry none, so the preset could never compile. `LooseOperaPhenixNeuriteInputs.source_voxel_spacing` (default: uncalibrated) now flows into `SourceBindingsConfig`; the compile test declares 0.65 um | - |
| test_installed_mcp_demo.py::test_portable_source_normalization_defers_catalog_and_execution_runtimes | production (owned) | since F1 a rendered pipeline names callables as `get_function(key)`; loading the portable source resolves keys through the prepared catalog and imports the CellProfiler/neurite implementation modules (scipy, skimage). Deferring both needs lazy callable references in the rendered format. Left failing, owner F1 (rendered pipeline format) | - |
| test_funcstep_contract_validator.py::test_registered_flexible_contract_preserves_explicit_false_override | stale test | test-module declaration no longer registry-owned (B1b); projected with `project_custom_function` | - |
| test_function_artifact_outputs.py::test_source_bound_artifact_keyword_uses_the_exact_selected_image | stale test | `SimpleNamespace` execution plan lacked `main_input_dependency`; now a real `CompiledStepPlan` | - |
| test_function_runtime_source_projection.py (7) | stale test | metadata-handler stub lacked `source_workspace_root` (6 tests); auxiliary binding in `test_main_flow_input_owns_runtime_binding_scope_with_auxiliary_source` now declares `origin=PIPELINE_START`, since an unstored STEP_INPUT binding is a current-pixel carrier (8c1ef0527); assertions unchanged | - |
| test_invocation_input_source_context_identity.py::test_primary_workspace_role_does_not_override_compiled_input_ownership | stale test | since bee5f223a a named source binding owns an unstored input even when the edge carries a main-flow projection; the expected `ValueError` no longer applies. Rewritten (and renamed `test_named_source_binding_owns_unstored_input_over_main_flow_projection`) to assert the binding's payload is returned | - |
| test_master_multi_plate_demo.py (3), test_mcp_assay_showcase.py (1 error) | production bug (scripts) | scripts imported deleted `FunctionStepOutputProducerIdentityRequest` (now `CompiledStepPlan.ARTIFACT_OUTPUT_KIND`, 74693f589); master demo read row field `plate_scope_id`, renamed `scope_id` by U1; showcase set results outside the plate root. Fixed in scripts | - |
| test_master_multi_plate_demo.py::test_plate_manager_projects_the_current_scope_color_owner | stale test, deleted | tested `PlateManagerStateProjectionService`, deleted by U1 (adb91bec9); the accent projection now lives in `PlateManagerStateSurfaceProvider._project` | tests-only: the lowercased accent-colour projection in `PlateManagerStateSurfaceProvider._project` has no remaining unit test (owner U1/U2) |
| test_metadata_namespace_327.py (2) | isolation | worker deliberately imports PolyStore before OpenHCS; in any checkout but the one the venv `.pth` names, it loaded a different PolyStore and failed the stale-externals guard. Worker env now puts this process's PolyStore source first | - |
| test_mcp_memory_diagnostic.py (2) | production bug (scripts) | `scripts/mcp_memory_diagnostic.py` imported `python_introspect` before `openhcs`, loading first-party libraries from the venv `.pth` checkout; now imports `openhcs` first | - |
| test_mcp_release_workflow.py::test_source_candidate_jobs_run_independently_from_publication_readiness | stale test | parity job is gated by the `parity-scope` relevance job (969270e26); invariant now: candidate jobs need at most `parity-scope`, which needs nothing | - |
| test_sync_mcp_release_metadata.py::test_checked_in_mcp_release_metadata_matches_package_version | production bug | release metadata still pinned 0.8.6 after the 0.8.7 bump; regenerated with `scripts/sync_mcp_release_metadata.py` | - |
| test_plane_nlm_declaration.py (2) | stale test | test-module declarations no longer registry-owned (B1b); projected with `project_custom_function` | - |
| test_nlm_slice_contract.py (collection error) | external | module imported the torch NLM backend at collection; torch is an optional extra. New `tests/unit/framework_requirements.py` (`requires_framework(MemoryType.X)` marker with stated reason, `framework_module` lazy import); the two torch cases are marked, the jax cases run | - |
| test_native_worker_durable_evidence.py (4) | stale test | `_invoke_native_worker` gained required `timeout_seconds`, and the bridge now admits only a complete `NativeBatchRequest`; tests pass the timeout and write a complete request (worker finds its root from the request path) | - |
| test_neurite_outgrowth.py::test_filled_two_neuron_crossing_keeps_the_same_owners_as_final_traces | needs owner decision | bisected to 4b4f6e611 (Oct 6, "Carry resolved crossing relationships through neurite signal repair"), which makes resolved crossing cores temporary support that "is not a pixel owner"; the final trace pixel at the crossing is now 0. The test asserts it is owned. Which is intended is an analysis-design decision (neurite analysis owner, no refactor surface). Left failing | - |
| test_path_planner_materialization.py::test_artifact_managed_regular_pattern_uses_declared_owner_scope | stale test | bisected to ed17bba00 (#785): a generic runtime adapter whose callable takes main-flow pixels follows the main-flow domain. The test callable took `image`; it now declares no raw image parameter, which is the case the declared-owner rule covers | - |
| test_persisted_semantic_metadata.py::test_retained_corrupt_provenance_fails_at_admission | stale test | provenance planes are now serialized as `{"identities", "planes"}`; corruption injected into `planes[0]`; the rejection message is "Unknown provenance plane fields" (rejection still asserted) | - |
| test_registered_configuration_source_readiness.py | stale test | the registry now calls the plural `prepare_dataclass_declarations`, so patching the singular recorded nothing; the test records each declaration the pass prepares | - |
| test_source_provenance_constructor_defaults.py (2) | stale test | `SpatialGraph` gained required `coordinate_spacing`; constructor case passes a 2-D spacing | - |
| test_runtime_callable_resolution.py::test_runtime_callable_resolution_has_no_scan_fallback_or_cache_mirror | stale test (guard) | #419 added one identity-bound process cache (`CallableContractRuntimeCache(IdentityBoundProcessCache)`) to resolution; guard now forbids any other cache name in `resolve_runtime_callable` and asserts that cache's family | - |
| test_source_binding_workspace.py (2) | stale test | #440: an uncalibrated source cannot provide a physical pixel size; the uncalibrated parameter case now expects rejection, and the subdirectory test asserts the numeric view `get_metadata_pixel_size` | - |
| test_source_bindings.py::test_source_set_without_matched_bindings_preserves_anchor_candidates | production bug | bisected to 210f9c99c: expanding per alias returned `()` when no binding selects files, dropping every anchor. `SourceBindingMatchedImageSet.expand` now returns the matcher's no-binding result (all anchors) in that case | - |
| test_runtime_values.py::test_pure_2d_auxiliary_aggregator_preserves_image_payload_metadata | stale test | PURE2D image stacks stay deferred `ProducedImageStack` slices (70a79fa38); asserts the `ImagePayload` family plus the unchanged shape and per-plane metadata | - |
| test_registered_object_output_boundaries.py (2, declared id 1 empty) | production (owned, K3) | bisected to 7ce29a1d2: shape features default to the `ROW_ORDINAL` array domain, so with declared ids (1,2,7) and measured (2,7) the label lookup assigns area 6 to empty label 1 and 20 to label 2. Whether CellProfiler's compact vector or the label lookup should change is a measurement-dialect decision that affects parity; owner K3 (measurement rows) | - |
| test_ci_package_boundaries.py::test_installed_test_runner_removes_checkout_paths_from_parent_and_children | isolation | the "installed" path came from `tmp_path`, which is inside the checkout when `--basetemp` is in the worktree, so the runner rightly removed it; the path is now a sibling of the checkout | - |
| test_template_crop_pipeline_execution.py (16) | production (owned, G3) | bisected to bb76b5e44 (#395): a selected-plane image output now becomes its source plane (`for_leading_source_plane`), so per-channel crops persist under the source plane's filename (`A01_s001_w1_z001_t001.tif`) instead of the declared output's (`..._cropped_stack.tif`). Same singleton-selection mechanism as test_volume_projection_fixture; which identity names a selected-plane output is a G3 payload decision. Left failing | - |
| test_derived_role_publication_435.py (2, aggregate cases) | production (owned, G3) | for one persisted occurrence the main-flow record declares a `colour_samples` axis at position 0 while the artifact record declares none, and `source_spatial_domain` no longer has the asserted mapping shape; payload axis declarations disagree between the two publication paths. Left failing | - |
| test_bioformats_microscope_handler.py::test_openhcs_output_subdirectory_initializes_from_metadata_root | production (owned, G4) | opening an output plate's `images_results` directory now raises "No declared OpenHCS projection contains ..." because metadata access is scoped to declared projections (a8ab61dc5); the results dir is declared only as `results_dir` of `images`. Whether a results dir opens its owning projection is a dataset-source decision. Left failing | - |
| test_artifact_publication_journey.py::test_converted_checkpoint_has_typed_address_on_final_reconciliation (4) | production (owned, K2) | first publication into an empty metadata document fails in `reconciliation_directories_from_document` ("No subdirectories found"); with that tolerated, object labels saved under `results/` still lack typed produced addresses. Recorded as pre-existing in a8ab61dc5's message. Left failing | - |
| test_cellprofiler_backend_public_api (2), _compatibility_matrix (10), _export_to_database (1), _generic_special_input_binding (1), _library_loading (2), _processing_backend (4), test_settings_binder (3 of 4) | environment | pass once the native extensions (`_tabular/_granularity/_median/_font_raster_native`) are built. `tests/conftest.py` `pytest_sessionstart` derives the module list from the tracked `_*_native.cpp` sources and stops the session with a build instruction when one is missing | - |
| test_native_tabular.py (13) | stale test | CSV export takes `ColumnarRows` (4017f7e85); rows built with `MeasurementSparseColumnarRows.from_rows`; assertions unchanged | - |
| test_benchmark_visible_source.py (1), test_runner_cellprofiler_compatibility.py::test_native_reference_lookup_* (2) | isolation | aliases went to the shared `/tmp/openhcs_benchmark_visible_sources`. Autouse `visible_source_root` fixture (tests/conftest.py) gives each test a private visible root; tests create their dataset dir, since `resolve_visible_source_path` rejects a missing target | - |
| test_cellprofiler_comparison.py (1) | stale test (benchmark) | processing contract `.value` -> `.key` after G5 | - |
| test_official30_lab_meeting_demo.py (collection error) | stale benchmark | `benchmark/demos/official30_lab_meeting.py` used deleted `FunctionStepOutputProducerIdentityRequest`; now `CompiledStepPlan.ARTIFACT_OUTPUT_KIND` (74693f589) | - |
| test_cellprofiler_identify_tertiary_output_abi.py::test_tertiary_same_object_probe_preserves_both_input_and_output_roles | production (owned, K5) | IdentifyTertiaryObjects with larger == smaller declares one relationship spec in two positional return slots; since cbf1857f7 the callable ABI rejects duplicate return refs at declaration, so the contract cannot be built. Moving the rejection to value resolution (tried in 976ab94f5) dropped the executor-time rejection that test_cellprofiler_module_execution_semantics protects and would still fail this module at run time, so it was reverted. Admitting repeated positional slots end to end is a callable-contract decision. Left failing | - |
| test_cellprofiler_artifact_declarations.py (2) | stale test | bisected: #785 (per-object group scope is the object input) and 94a634bdc (Math domain is the first required object operand) | - |
| test_settings_binder.py (1), test_colocalization_metric_setting_authority.py (1) | stale test | 497e553a7 (#536) keeps the full object-set roster on one invocation; tests assert that | - |
| test_cellprofiler_display_manual_projection_declarations.py (1) | stale test | compares `ModuleSetting.value`, not the record | - |
| test_cellprofiler_export_measurement_outputs.py (1), test_cellprofiler_runtime_adapter.py (4) | stale test | stubs gain `source_workspace_root`; test context `plate_path` -> `dataset_root` (G7) | - |
| test_cellprofiler_output_recording.py (1) | stale test | observes dispatch order at `SpatialGridOutputRecorder.record`; order assertion unchanged | - |
| test_cellprofiler_object_measurement_subject.py (4) | stale test | Classify's object input bound to its declared `labels` parameter; missing or ambiguous subjects still rejected, now at declaration | - |
| test_cellprofiler_reference_exports.py (3) | production bug | QA checkpoint sidecars were counted as terminal CellProfiler outputs; `ArtifactSidecarRole.inspection_only`, skipped by `cellprofiler_terminal_artifact_specs` | - |
| test_cellprofiler_special_io_declarations.py (1) | stale test | asserts the declared image-set context relation from #547 | - |
| test_cellprofiler_runtime_callable_introspection.py (1) | stale test | ObjectState private `_signature_defaults` -> public `signature_default()` | - |
| test_cellprofiler_watershed_provider.py (2) | stale test | unpacks the trailing QA diagnostic planes | - |
| test_classification_two_vector_authoring.py (1) | stale test | passes an `ImagePayload` (G3) | - |
| test_exported_relationship_equivalence.py (17) | stale test | frozen snapshots edited with `dataclasses.replace` | - |
| test_cellprofiler_static_deletion_gates.py (4 of 5) | stale guard | `CellProfilerPipelineImporter` -> `CppipeImporter`; test-only identifiers renamed; `runtime_stores` compares (type, name); `project` methods that project nothing renamed `scoped_path`/`channel_output` (rule 1b); MRO guard admits `issubclass` (rule 1a nominal membership) | - |
| test_cellprofiler_static_deletion_gates.py::test_cellprofiler_projection_enters_only_runtime_slice_projection | production (owned, G3) | two parallel projection branches remain: `interop/cellprofiler/runtime/invocation.py:222 source_provenances` (66a4959e3) and `measurement_execution_support.py:70`. Fixing them changes per-plane provenance and needs a parity run. Left failing | - |
| pyqt_gui/test_code_document_catalog_imports.py (3) | production bug | since F1 rendered pipelines call `get_function('<key>')`, and the code-document validator rejected its own renderer's output; it now admits exactly one literal catalog id, bound through the catalog reference (`RegistryFunctionReference.registry_lookup`); tests cover non-literal and unknown ids | - |
| pyqt_gui/test_function_catalog_form_materialization.py (1) | production bug | plain `save_images` kept a `context` parameter it deleted on entry (injection disabled in 9df6b96ca) and the function pane could not render it; parameter and its `runtime_context_parameter(None)` removed | unused |
| pyqt_gui/test_ui_bridge_lifecycle_config.py (1) | isolation | IPC socket path under `tmp_path` exceeded `sun_path`; uses `unix_socket_dir` | - |
| test_ack_return_route_journey.py (2) | isolation | the file doubles as the producer script and imported polystore before openhcs (stale-externals guard); now imports openhcs first; IPC under `unix_socket_dir` | - |
| test_capture_media_gallery.py (2) | stale test | capture default is "render complete", which needs an observed frame; the fake observes a painted frame through `request_capture` | - |
| agent/test_viewer_render_snapshot.py (1) | stale test | `request_viewer_capture` removed (7d68e26fe); uses `request_capture` + `snapshot_reply` | - |
| agent/test_ui_bridge_service.py (1) | isolation | default path policy allows only /tmp; test declares `tmp_path` writable | - |
| test_napari_roi_manager_integration.py (1) | stale test | manifest gained a Spatial Planes widget; test checks the ROI manager is contributed and every widget command imports | - |
| test_napari_streaming_handlers.py (8) | stale test | partial servers (`__new__`/fakes) lacked the display pipeline, routed items and settle replies; tests use a real `NapariViewerServer` over a `ViewerModel` (no socket opened) | - |
| test_napari_accepted_work_settlement.py (4) | external | these render real layers through vispy, which needs native OpenGL; offscreen Qt has none, `add_image` fails inside vispy and `viewer.close()` then raises, leaving the window alive (the order-dependent segfault). They request the declared `native_opengl` fixture (tests/unit/native_opengl.py), which skips with a stated reason when no GL context can be made; CI with Xvfb+mesa runs them | - |
| test_native_viewer_presentation.py (1) | stale test | `SimpleNamespace` server replaced by a real server | - |
| test_streaming_service.py (11) | stale test | fake metadata handler inherits `MetadataHandler` defaults; backend from `config.viewer_family` (G6); colour axis asserted as an item field (G3) | - |
| test_viewer_listener_binding.py (6) | stale test | teardown closed `server.ack_socket`, which servers no longer own | derived (servers no longer own an ack socket) |
| test_viewer_receipt_replay.py (10) | production bug | `_receipt_source_projection` omitted the `declared_axes` argument G6 made required, so every receipt replay raised `TypeError`; passes the active axis family | - |
| agent/test_plate_streaming_service.py (10) | stale test | fake handlers gain a metadata owner; launch failures built with `viewer_family` (G6) | - |
| test_viewer_result_element_selection.py (2) | stale test | harness uses a real display pipeline; one precondition asserted a napari bug that napari 0.9.2 fixed (selecting off-slice shapes no longer raises) | contract (external napari behaviour changed; OpenHCS assertions unchanged) |
| test_routed_channel_selection.py (1) | stale test | a failing axis returns `ExecutionResult.error` instead of raising (53d708b16); asserts the failed result and message | - |
| test_volume_projection_fixture.py (4) | production (owned, G3) | (a) selecting one plane through `MainFlowPlaneProjectionOutputSpec` yields a 2-D payload where the declaration returns a (1,Y,X) stack, with different provenance planes; (b) re-contextualizing through `ImageArtifactType.contextualize_output` -> `derive_payload` gives source identity metadata `{}` instead of `None`. Fix belongs in `runtime_image_values._derived_metadata` / `artifacts.py` image contextualization. Left failing | - |
