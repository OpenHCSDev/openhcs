# G2: Member references derived from the axis family

**Head audited:** `openhcs` `main` at `66a0b30a0` (#1182; G1, G3, G4, G6 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.**
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "The axis family". *Uses:* G1 `Axis`/`AxisFamily`/roles, PolyStore `ZarrBatchAxis`.

## What is wrong

**Kernel modules still spell microscopy members by name: 134 references in 22 files name an axis (`well`, `channel`, …), its collection key (`wells`, …) or its label, as a string literal, an attribute or a class field (IDEN-4, MEMB-2).**

G1 removed every member *class* reference from kernel modules (its guard keeps that at zero). The names themselves remain. Census at this head, an AST scan of `openhcs/` minus the domain modules of the G1 guard and `interop/`. Tokens are derived from the microscopy family: each axis's `name`, `metadata_collection_field`, and `label` when longer than one letter (`Z` and `T` coincide with ImageJ/NGFF dimension letters and `TypeVar("T")`). Docstrings are excluded.

| File | Hits | What they are |
|---|---|---|
| `runtime/fiji_viewer_server.py` | 38 (attr 32, field 3, lit 3) | hyperstack coordinates named `channel` / `z_axis_coordinates` / `frame`; `name="channel"`; `"Ch{idx}"` label fallback |
| `agent/dto/plate.py` | 19 (attr 9, field 5, lit 5) | MCP `well=` file filter (3 DTOs) and synthetic-plate `wells` |
| `processing/backends/cellprofiler/color.py` | 16 (attr 13, field 2, lit 1) | `FixedImageType.channels`; ColorToGray `"channels"` value |
| `core/progress/types.py` | 14 (attr 3, field 10, lit 1) | progress-stream declarations name their stream `channel` |
| `mcp/dev_client_commands/plate.py` | 8 | `well=`/`wells` client arguments |
| `agent/services/plate_inspection_service.py` | 5 | `.well` filter |
| `agent/services/synthetic_plate_service.py` | 4 | `.wells` |
| `core/synthetic_plate_generation.py` | 4 | `SyntheticPlateGenerationParameters.wells`, `max_wells` reads |
| `formats/experimental_layout_rows.py` | 4 | `"well"`, `"wells"` workbook row labels (MetaXpress domain code outside the domain package) |
| `core/source_bindings.py` | 3 | `ImagePlaneSource.channel` |
| `formats/experimental_result_formats.py` | 3 | `"well"`, `"Well"` workbook columns (domain code) |
| `agent/services/plate_streaming_service.py` | 2 | `.well` filter |
| `core/plate_file_inventory.py` | 2 | `PlateFileInventoryQuery.well` |
| `core/plate_image_inventory.py` | 2 | `.well` filter |
| `processing/backends/cellprofiler/save_images.py` | 2 | `SaveImagesSeriesAxis` values `"timepoint"`, `"z_index"` |
| `runtime/zmq_compilation.py` | 2 | `ZMQCompilationRequest.wells` |
| `core/progress/runtime_tree.py` | 1 | `WellProgressTreeNode.node_kind = "well"` |
| `core/steps/function_io.py` | 1 | NGFF axis type `"channel"` restated beside `"c"` |
| `mcp/dev_client_renderers/plate.py` | 1 | `.wells` |
| `processing/backends/cellprofiler/display_modules.py` | 1 | `PlatemapData.well` (plus a private copy of the well row/column codec) |
| `processing/backends/cellprofiler/export_to_database.py` | 1 | `well_metadata="Well"` (CellProfiler's metadata tag, also restated as `"Metadata_Well"` in `display_modules.py`) |
| `runtime/viewer_display.py` | 1 | Fiji slot wire value `"channel"` |

Already clean at this head (re-measured; done by G1/G4/G6): the `function_io` Zarr strategies are keyed by role; `config.py` viewer modes are per-role fields with slot-family defaults; source projections are one `SourceAxisProjection` over axis declarations; `required_variable_components` is `required_axis_roles`; analysis consolidation is a domain post-execute hook. Member *class* references in kernel modules: 0.

Domain modules in the G1 allowlist that are not in the domain's package: `formats/experimental_analysis.py` sits apart from its two sibling modules (`experimental_layout_rows.py`, `experimental_result_formats.py`), which are not allowlisted and so count above.

## Target

- **Asked by role / derived:** the MCP and kernel file filter `well` becomes `partition` (the value of the family's partition axis; `plate_image_inventory` already resolves it by role); `ZMQCompilationRequest.wells` and the synthetic-plate `wells` become `partition_values`; the runtime tree's partition node is `PartitionProgressTreeNode` (`node_kind = "partition"`); the CellProfiler plate map splits positions with `partition_axis().grid_coordinates` (its private `_parse_well_name` copy is deleted).
- **External vocabularies owned by their owners:** the NGFF axis type is derived from the NGFF axis name by PolyStore (`ZarrBatchAxis` no longer takes `axis_type`; lockstep PolyStore PR), so `function_io` declares only `"t"`, `"field"`, `"c"`, `"z"`. CellProfiler's well metadata tag is declared once in interop and `ExportToDatabase`/`DisplayPlatemap` defaults derive from it. CellProfiler's ColorToGray "Channels" choice is declared through `cellprofiler_literals`.
- **Named for what they are:** Fiji hyperstack coordinates use ImageJ's position letters `c`, `z`, `t` (`setPosition(c, z, t)`), and slice labels and the label fallback derive from the dimension's name; progress streams are `progress_channel`; ColorToGray's fixed colour planes are `fixed_channels`; `ImagePlaneSource.channel` is `colour_sample` (the colour sample within one source plane); `SaveImagesSeriesAxis` members are CellProfiler's `TIME`/`SLICE`.
- **Moved into the domain package:** `formats/experimental_{analysis,layout_rows,result_formats}.py` move into `processing/backends/experimental_analysis/` (the MetaXpress experimental-analysis package already allowlisted), so the allowlist loses `formats/experimental_analysis.py`.
- **One external spelling kept:** `FijiSlots.HyperstackChannel.wire_value == "channel"` is ImageJ's hyperstack channel dimension, and saved configs spell it `FijiDimensionMode.CHANNEL` (G6 kept member names so saved configs load unchanged). The guard pins exactly this one declaration.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Fiji/progress/runtime-tree wire values, compile requests, MCP requests | runtime | reset |
| Saved pipelines naming `ImagePlaneSource(channel=…)` or `SaveImagesSeriesAxis.TIMEPOINT/Z_INDEX` | durable | Only CellProfiler-imported pipelines that set a single-image channel or a non-default series axis spell these; both parameters are carried but never read. Not converted (reported to the owner). |
| Saved configs (`FijiDimensionMode.*`) | durable | unchanged |

## Guards

`tests/unit/test_axis_family_guards.py` gains an exact kernel scan: over every module outside the G1 domain allowlist, no string literal (docstrings aside), attribute or class field equals a token derived from the active domain family (name, collection key, multi-letter label). The only admitted occurrence is the Fiji slot declaration above, pinned by module, class and value. The allowlist itself shrinks by one entry.

## Tests

- Witness (`tests/unit/test_axis_family_witness.py`): extended so the remote-sensing family's Zarr layout follows its roles (NGFF types from PolyStore) and its Fiji slots map band→channel and date→frame, with no domain module loaded; the end-to-end subprocess witness stays green.
- Touched behaviour tests are updated to the new names; no assertion is weakened.

## New-case experiments

Before: a second domain finds `well`/`wells` in the MCP file filter, synthetic plate profile, compile request and runtime tree, and the NGFF type restated beside its name. After: those read the partition axis or the external standard's owner.

## Done when

The guard finds zero kernel occurrences besides the pinned Fiji declaration; the witness, the touched tests, the parity check (baseline 29/30) and the `test_main.py` disk and zarr direct cases are green.
