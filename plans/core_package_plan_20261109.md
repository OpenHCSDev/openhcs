# openhcs/core: from 114 flat modules to packages

**Status:** plan only, nothing applied. Moves run through NRA
(`--codemod-refactor-goal package_move` plus a DestinationTable), the same tool and
procedure that moved 103 agent-comms modules in one batch on 2026-11-09
(agent-comms 669acfa7: 553 files, ~3,450 import lines, 0 import failures).

## Where core is now

- `openhcs/core` holds **114 flat modules** (about 75,000 lines) beside 12 subpackages.
- The file names already carry the missing packages as prefixes: `runtime_` 29, `source_` 14,
  `measurement_` 5, `function_` 5, `image_` 4, `debug_` 4, `config_` 4, `component_` 3.
  A package name written into every file name is the package, unnamed (IDEN-3).
- Modules sit flat next to the package they belong to: `measurement_row_materialization.py`
  next to `materialization/`, `function_reference.py` next to `steps/` (which already
  holds nine `function_*` modules), `component_set.py` next to `components/`.
- The biggest files are cycles, not just big. A file's classes reference each other through
  one strongly connected component (Tarjan over class-to-class references):

  | file | lines | in one cycle |
  |---|---|---|
  | `materialization/core.py` | 5,101 | 49 of 57 families, ~4,470 lines (88%) |
  | `runtime_image_values.py` | 2,487 | 8 of 10 families, ~2,200 lines |
  | `callable_contract.py` | 2,435 | 5 of 16 families, ~1,930 lines |
  | `measurement_row_materialization.py` | 2,550 | 6 of 15 families, ~1,430 lines |

  Moving a file does not touch these numbers (AGENT-6): they are the second phase.

## Destinations

Placement comes from each module's import edges to the existing subpackages (both
directions), its name family and its docstring.
A new package name is never a flat module's name, or it would shadow that module:
so `configuration/`, not `config/`; `debugging/`, not `debug/`.

| Package | Modules |
|---|---|
| `values` (new): typed runtime payload values | `runtime_image_values.py`, `runtime_object_labels.py`, `runtime_object_label_aggregation.py`, `runtime_object_label_building.py`, `runtime_object_label_domains.py`, `runtime_sparse_labels.py`, `runtime_tabular_values.py`, `runtime_spatial_graph.py`, `runtime_spatial_grid.py`, `runtime_relationships.py`, `runtime_array_values.py`, `runtime_slice_alignment.py`, `runtime_slice_projection.py`, `runtime_plane_projection.py`, `aligned_image_payload.py`, `payload_axes.py`, `image_shapes.py`, `source_spatial_domain.py` |
| `measurements` (new) | `measurement_dialect.py`, `measurement_feature_queries.py`, `measurement_image_alignment.py`, `measurement_row_materialization.py`, `measurement_row_qualifiers.py`, `runtime_measurements.py` |
| `execution` (new): what a worker runs and keeps while it runs | `runtime_stores.py`, `runtime_stack_cache.py`, `runtime_pattern_cache.py`, `runtime_source_binding_cache.py`, `runtime_batch_contracts.py`, `runtime_adapters.py`, `runtime_profile.py`, `runtime_image_loading.py`, `execution_state.py`, `image_payload_execution_mode.py`, `processing_contracts.py`, `processing_preparation.py`, `lazy_gpu_imports.py`, `post_execute.py` |
| `sources` (new): source bindings and their identity | `source_binding_context.py`, `source_binding_selection.py`, `source_bindings.py`, `source_bindings_preview.py`, `source_image_provenance.py`, `source_matching.py`, `source_metadata.py`, `source_path_identity.py`, `source_plane_alignment.py`, `source_projection.py`, `source_tile_geometry.py`, `path_pattern_matching.py` |
| `configuration` (new) | `config.py`, `config_cache.py`, `config_document.py`, `config_sections.py`, `stated_types.py`, `xdg_paths.py` |
| `debugging` (new) | `debug.py`, `debug_session_projection.py`, `debug_view_models.py`, `debug_views.py`, `log_utils.py` |
| `streaming` (new) | `streaming_config_declarations.py`, `streaming_config_factory.py`, `viewer_streaming_service.py` |
| `artifacts` | `artifact_inspection.py`, `artifact_key_selection.py`, `projected_image_output.py`, `runtime_artifact_queries.py`, `runtime_artifact_values.py`, `runtime_output_matching.py`, `runtime_exports.py`, `runtime_execution_validation.py` |
| `dataset_sources` | `source_binding_workspace.py`, `source_workspace_projection.py`, `virtual_workspace_metadata.py`, `plate_image_inventory.py`, `plate_file_inventory.py`, `input_workspace.py`, `pipeline_import.py`, `synthetic_plate_generation.py`, `result_file_formats.py` |
| `components` | `axes.py`, `axis_boundaries.py`, `axis_filter.py`, `component_filters.py`, `component_group_scope.py`, `component_set.py` |
| `pipeline` | `callable_contract.py`, `function_patterns.py`, `function_contract_metadata.py`, `invocation_artifacts.py`, `variable_component_stack_requirement.py`, `framework_device_resolver.py`, `partition_filter.py`, `compiled_step_plan.py`, `step_dependencies.py`, `autoregister_preparation.py`, `vfs_protocol.py` |
| `steps` | `function_reference.py`, `function_step_document.py`, `function_step_transport.py`, `pipeline_document.py` |
| `materialization` | `roi_point_metadata.py`, `roi_source_metadata.py`, `numpy_jsonable.py`, `image_file_serialization.py`, `image_quantization_numba.py` |
| `orchestrator` | `compiled_execution.py`, `execution_visualizer.py`, `metadata_cache.py`, `native_threading.py`, `alias_property.py` |
| `context` | `worker_start_policy.py` |
| `equivalence` | `runtime_identifier.py` |

That is 114 of 114. After the moves, a second, mechanical batch drops the prefix the
package now states (`values/runtime_image_values.py` → `values/image.py`), one NRA
module rename per file.

## Saved pipelines and configs name these modules

`openhcs/serialization/pycodify_formatters.py:51` writes `type(value).__module__` into every
generated pipeline and config script, and `:248` writes `FunctionStep.__module__`. A user's
saved `.py` pipeline therefore imports `openhcs.core.config`, `openhcs.core.steps...` and
any other module whose classes it holds. Moving those modules breaks saved scripts on load.

The fix is one rewrite, not an alias: a `tools/cutover/` script, generated from the same
destination table, rewrites `openhcs.core.<old>` to `openhcs.core.<package>.<old>` in saved
scripts, runs once and is deleted. No re-export shim stays in `core/` (TIME-3). The batches
that move a serialized class (`configuration`, `steps`, `values`, `components`) ship with
that script in the same PR.

## Batches

Big batches are cheaper: each costs one NRA run (2-3 min) and one test pass, no matter
how many modules it carries.

1. **Everything without saved-script exposure in one table**: `measurements`,
   `execution`, `sources`, `debugging`, `streaming`, `artifacts`, `dataset_sources`,
   `pipeline`, `materialization`, `orchestrator`, `context`, `equivalence`.
2. **The serialized ones** with the cutover script: `configuration`, `components`,
   `steps`, `values`.
3. **Prefix-dropping renames**, one table.
4. **Guards**: no new module directly under `openhcs/core` (a test listing its `.py`
   files against an empty allowance), and import direction between core's packages.

Each batch: NRA apply, then the leftover-shell check, the stale-path scan (imports in
any scope, `TYPE_CHECKING` blocks, dotted strings), import of every `openhcs` module,
the touched tests, on all cores.

What agent-comms' run taught, so these batches don't repeat it (fixes on
claude-n-plan's NRA queue): a module-level statement that is not a declaration
blocks the empty shell from dissolving, and one refused row sinks the whole table.
NRA can also hoist a `TYPE_CHECKING` import to module scope, and it misses imports
inside function bodies and in code held in strings. Until those fixes merge, the two
scans above catch each one before the run, not after it.

## Phase 2: the cycle cores

A file whose classes form one cycle cannot be split by moving classes: any split leaves
a module cycle, which `TYPE_CHECKING` guards and local imports only hide (rules: no new
guards). For each cycle core above, the plan is the one agent-comms `orders.py` needs:
find the references that close the cycle (usually a low-level record asking upward
for a high-level owner), move the declaration both sides need into a module both
import, and then the remaining families split along the order the cycle no longer
forces. `materialization/core.py` is first: 4,470 lines in one component.
