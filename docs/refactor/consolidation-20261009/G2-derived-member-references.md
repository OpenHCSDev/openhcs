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

## Target (as built)

- **Asked by role / derived:** the MCP and kernel plate-file filter `well` is `partition` (`PlateFileInventoryQuery`, the three plate-file DTOs, both services, the dev client `--partition`); `plate_image_inventory` already resolved it through `partition_axis()`. The synthetic-plate profile, request and result carry `partition_values` (`--partition-value`); `ZMQCompilationRequest.wells` is `partition_values`. The runtime tree's partition node is `PartitionProgressTreeNode` (`node_kind = "partition"`).
- **External vocabularies declared by their owners:** PolyStore 0.5.0 declares `NGFF_AXIS_TYPES` and derives each axis's NGFF type from its name, so `ZarrBatchAxis` takes no `axis_type` and `function_io` declares only `t`, `field`, `c`, `z` (lockstep PR OpenHCSDev/PolyStore#36; pin `polystore>=0.5.0,<0.6`). The four role-keyed Zarr leaves are named by role (`Time`, `Tile`, `Colour`, `Stack` `ZarrAxisProjection`), not by microscopy member. CellProfiler's `Plate`/`Well` metadata tags are declared once in `interop/cellprofiler/analyst_export.py` (`PLATE_METADATA_TAG`, `WELL_METADATA_TAG`); `CellProfilerDatabaseExportSettings` and `export_to_database` take their defaults from them.
- **Named for what they are:** Fiji hyperstack coordinates are ImageJ's `c`, `z`, `t` (`FijiDimensionStorage`, `FijiHyperstackCoordinateComponents`, `FijiHyperstackCoordinates`); `FijiHyperstackCoordinates.axes()` gives them in ImageJ order, and `dimensions`, `key`, `imagej_position`, `contains_axis_values` and the slice-label builder iterate it instead of restating the triple; slice labels and the channel-label fallback derive from the dimension name. Progress declarations name their stream `progress_channel`. ColorToGray's fixed colour planes are `fixed_channels`, InvertForPrinting's are `rgb_channels`, and the ColorToGray "Channels" type's value is `numbered_channels` (CellProfiler's spelling still matches by member name). `ImagePlaneSource.channel` is `colour_sample`. `SaveImagesSeriesAxis` members are CellProfiler's `TIME`/`SLICE`. `PlatemapData.well` is `well_name` (CellProfiler's DisplayPlatemap term).
- **Moved into the domain package:** `formats/experimental_analysis.py`, `experimental_layout_rows.py` and `experimental_result_formats.py` are `processing/backends/experimental_analysis/{analysis,layout_rows,result_formats}.py`. `openhcs/formats/` holds only `pattern/`; the G1 and G4 allowlists lose `formats/experimental_analysis.py`.
- **One external spelling kept:** `FijiSlots.HyperstackChannel.wire_value == "channel"` is ImageJ's hyperstack channel dimension, and saved configs spell the slot `FijiDimensionMode.CHANNEL` (G6 kept member names so saved configs load unchanged). The guard pins exactly this declaration.

Production (Python under `openhcs/`): −294 +264.

## Corrections made while executing

- The CellProfiler plate map keeps its own well-name split: it parses CellProfiler's `Metadata_Well` measurement, not the partition axis, so binding it to `partition_axis().grid_coordinates` would couple CellProfiler's vocabulary to the active family. The private `_parse_well_name` copy of the well codec stays with the CellProfiler domain (owner: P1).
- The spelling scan excludes `openhcs/interop/` as well as the G1 domain allowlist: interop is the CellProfiler domain (04-ARCHITECTURE, P moves it to `domains/cellprofiler`) and owns CellProfiler's `Well` tag. The member-class scan of G1 still covers interop.
- The NGFF types could not be expressed as kernel declarations without restating `"channel"` in a kernel module; they belong to the NGFF writer, so they moved to PolyStore.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Fiji/progress/runtime-tree wire values, compile requests, MCP plate requests and results | runtime | reset |
| Saved pipelines naming `ImagePlaneSource(channel=…)` or `SaveImagesSeriesAxis.TIMEPOINT/Z_INDEX` | durable | Only CellProfiler-imported pipelines that set a single-image channel or a non-default series axis spell these; neither parameter is read by any code path. Not converted (decision G2-Q1 in the index; default: no tool). |
| Saved configs (`FijiDimensionMode.*`) | durable | unchanged |

## Guards

`tests/unit/test_axis_family_guards.py`:
- `test_kernel_modules_spell_no_microscopy_member`: over every module outside the G1 domain allowlist and `interop/`, the set of (module, enclosing class, spelling) for string literals (docstrings aside, f-string parts included), attribute names and class-body fields equal to a microscopy spelling (each axis's `name`, `metadata_collection_field`, and `label` when longer than one letter) **equals** `EXTERNAL_SPELLINGS`, which holds the one Fiji declaration. Exact equality: a new spelling or a removed exemption both fail.
- `test_domain_allowlist_names_existing_domain_modules`: every allowlist entry exists.
- The allowlist shrinks by `formats/experimental_analysis.py` (also in `test_dataset_source_guards.py`).

Census: 134 occurrences in 22 kernel files at `66a0b30a0`; 1 (the pinned Fiji declaration) after.

## Tests

- Witness (`tests/unit/test_axis_family_witness.py`): new `test_zarr_layout_follows_roles_and_ngff_types` (the remote-sensing family's Zarr layout follows its roles: tile → HCS image `field`, band → `c`, date → `t`, NGFF types from PolyStore). The end-to-end subprocess witness (no domain module loaded) passes unchanged.
- PolyStore: `test_array_axes_take_their_type_from_the_ngff_axis_name`; constructor calls lose the restated type.
- Touched behaviour tests take the new names; no assertion is weakened.

## New-case experiments

Before: a second domain meets `well`/`wells` in the MCP file filter, the synthetic-plate profile, the compile request and the runtime tree, and `function_io` restates the NGFF type beside each NGFF name. After: those read the partition axis, and the NGFF type comes from the writer.

## Handoff (recorded for later surfaces)

- **G7:** identifiers that contain a member name are runtime vocabulary and are not guarded yet: `WellFilterConfig`/`well_filter`/`well_filter_mode`/`WellFilterProcessor` (`core/config.py`, `core/utils.py`), `owned_wells`/`total_wells` (progress), `available_wells`, `_wells_for_execution` (`zmq_execution_server.py`), `plate_*` names. Once renamed, the guard's token match should extend to identifier substrings.
- **U1:** `pyqt_gui/widgets/shared/plate_view_widget.py` (`coord_to_well`, `wells_with_images`), the image browser's well decoding, and the MCP `component_filters` generalisation of the single `partition` filter.
- **P / P1:** `processing/backends/analysis/consolidate_analysis_results.py` and `processing/backends/experimental_analysis/` move into `openhcs/domains/microscopy`; `processing/backends/cellprofiler/` (with `display_modules._parse_well_name` and the `Metadata_Well*` defaults) into `domains/cellprofiler`. The G1 spelling scan then excludes only `domains/`.

## Done when

The guard finds zero kernel occurrences besides the pinned Fiji declaration; the witness, the touched tests, the parity check (baseline 29/30) and the `test_main.py` disk and zarr direct cases are green.
