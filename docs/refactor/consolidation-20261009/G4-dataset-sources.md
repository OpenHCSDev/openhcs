# G4: Dataset sources, formats and domain hooks

**Head audited:** `openhcs` `main` at `2897dca70` (#1170, G1 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.**
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "Sources and formats". *Builds:* `DatasetSource`, the domain-extension discovery, `SourceMetadataEnricher`, `PostExecuteHook`, `DatasetRootRule`. *Uses:* the G1 axis family, `AutoRegisterMeta`/`LazyDiscoveryDict`.

## What is wrong

**The kernel's source protocol, its own storage format and its post-run work live in the microscopy package or are hardcoded for microscopy, so the kernel imports the domain and a second domain cannot read or write data (IDEN-1, MEMB-2, IMPL-2).**

- The source protocol is domain code. `MicroscopeHandler` (`microscopes/microscope_base.py:180`), `FilenameParser`/`MetadataHandler` (`microscope_interfaces.py:303,455`) and the factory `create_microscope_handler` (`:912`) are the only way the kernel reaches data, and 24 kernel modules import `openhcs.microscopes` for them (`compiler.py:294`, `orchestrator.py:56,570`, `function_io.py:393`, `function_outputs.py:1202`, `source_workspace_projection.py:56,895`, `materialization_flag_planner.py:22`, seven `core/steps/*` modules, `plate_image_inventory.py`, …).
- The kernel's own format is domain code. The openhcsdata reader/writer (`microscopes/openhcs.py`, 1,765 lines) imports `Microscopy` and fills `channels=… wells=…` by member (`:1239-1243`); `source_bindings_handler.py` and `source_schema.py` (the generic image-folder source and the kernel plane-filename parser) also sit in `microscopes/`.
- `Microscope` enum (`constants.py:50`) restates the handler registry; `OPENHCS_DATA_MICROSCOPE_TYPE`, `MicroscopeSourceSelectionRole.require_registered_microscope` and 61 production lines translate between the two; `PipelineConfig.microscope` holds the enum.
- `SourcePlaneStoreAdapter` (the generic store family) is declared in `microscopes/bioformats_adapter.py:491`; `ImageXpressTiffSourceMetadataAdapter` (`imagexpress_source_metadata.py:20`) joins it only to supply `source_metadata_for_path`, returning `()` from `discover_stores`.
- Five per-role projection strategies (`source_metadata.py:1231-1355`) restate per-axis facts: metadata aliases, the persisted collection key (also derived a second way by `virtual_workspace_metadata.component_metadata_field`), fallbacks, and the microscopy `A01` row/column well codec.
- Filename codecs: grouped artifact paths insert a hardcoded `_w{key}` (`artifacts.py:4183-4185`, reached from `path_planner.py:2394,2495`); `SourceSchemaFilenameParser.extract_component_coordinates` hardcodes the `A01` row/column split. (`OpenHCSPlaneAddress.filename` was already derived from axis prefixes by G1.)
- OMERO in the kernel: `"/omero/"` output-root rule (`path_planner.py:2418`); `zmq_orchestrator_environment.py:56-80` parses OMERO plate ids and imports `microscopes.omero`.
- Domain post-run work is hardwired: `compiled_plate_execution.py:313` always calls microscopy analysis consolidation; `ProcessingContext` carries `analysis_consolidation_config`, `plate_metadata_config` and `auto_add_output_plate_to_plate_manager` (`processing_context.py:104-160`); `StepExecutionObservation.analysis_inputs` and `function_artifact_materialization.py:1024,1251` feed it by name; `AnalysisConsolidationConfig`/`PlateMetadataConfig`/`ExperimentalAnalysisConfig` (MetaXpress) are kernel config.
- `constants.py`: `DEFAULT_SITE_PADDING`, the stitching defaults (`DEFAULT_TILE_OVERLAP` … `DEFAULT_SEARCH_RADIUS`), `DEFAULT_MICROSCOPE`, `DOCUMENTATION_URL` have no reader.
- Stack handling in `source_image_provenance.py:1596,1775` and `source_projection.py:995-1029` already asks `one(StackAxis)` (G1) but is still spelled `z_index`/"Z" in names and messages.

## Target

```python
# openhcs/core/dataset_sources/ (kernel)
class DatasetSource(MetadataSourceDetector, FilenameParserCapability, ViewerMicroscopeHandlerABC,
                    ABC, metaclass=AutoRegisterMeta):     # registry key = identity
    source_name: ClassVar[str]
    def axis_values(self, axis, root) -> tuple[str, ...]
    def available_backends(self, root) -> list[Backend]
    def resolve_metadata_artifact(self, ref, root) -> object
    @classmethod
    def create_for(cls, root, filemanager, source_bindings_config) -> DatasetSource
class AutoDetectedSource(...)          # explicit "detect" choice for PipelineConfig.dataset_source
class SourcePlaneStoreAdapter(...)      # store family root
class SourceMetadataEnricher(...)       # metadata-only family; ImageXpress TIFF is a leaf
class PostExecuteHook(...)              # bound at compile time from the global config
class DatasetRootRule(...)              # claims a dataset id; prepares storage; output base
openhcs_format.py                       # the openhcsdata source/reader/writer, axis-derived
source_bindings_source.py, source_schema.py

# AxisFamily (kernel) declares the domain's registration modules
class Microscopy(AxisFamily):
    extension_modules = ("openhcs.microscopes", "openhcs.domains.microscopy.hooks")
```

- Kernel families that domains extend use one `LazyDiscoveryDict` discovery: the kernel package's own modules plus the active family's `extension_modules`. No kernel module imports `openhcs.microscopes` or `openhcs.domains`.
- Axis declarations own their source-metadata facts: `metadata_aliases`, `metadata_collection_field`, `metadata_fallback` (a small `AxisValueFallback` family), and `metadata_value()` (overridden by the domain's `Well` for row/column). One `SourceAxisProjection` replaces the five strategies and `component_metadata_field`.
- Grouped artifact paths spell the group key with the grouping axis's declared filename token.
- `PipelineConfig.dataset_source: type[DatasetSource]` (choices derived from the registry plus `AutoDetectedSource`) replaces `microscope: Microscope`. Wire and form spellings are the registry key.
- Microscopy registers `AnalysisConsolidationHook` (with its config sections) and the OMERO root rule from the domain; the kernel calls hook and rule families only.
- **Deleted:** `Microscope`, `DEFAULT_MICROSCOPE`, `OPENHCS_DATA_MICROSCOPE_TYPE`, `require_registered_microscope`, `handler_registry_service.py`, `create_microscope_handler`, `MICROSCOPE_HANDLERS`, the five `Source*ComponentProjection` classes, `component_metadata_field`, `SourcePlaneStoreAdapter.source_metadata_for_path`/`enrich_source_candidate`, `ProcessingContext.{analysis_consolidation_config,plate_metadata_config,auto_add_output_plate_to_plate_manager}`, `StepExecutionObservation.analysis_inputs`, the dead constants, the `"/omero/"` branch and OMERO import in the kernel.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| `openhcs_metadata.json` | derived (rewritten by initialization and execution) | keys unchanged: the per-axis collection keys come from axis declarations with today's spellings |
| Global config / saved `.py` pipelines naming `Microscope.X` or `microscope=` | durable | `tools/cutover/g4_dataset_source.py` rewrites `microscope=Microscope.X` to `dataset_source=<SourceClass>`; deleted once the owner has migrated |
| Registry caches, compiled plans | runtime | reset |

## Guards

`tests/unit/test_dataset_source_guards.py`:
- No kernel module imports `openhcs.microscopes` or `openhcs.domains` (kernel = `openhcs/` minus `microscopes/`, `domains/`, `processing/presets/`, `demo/`, `pyqt_gui/`, `mcp/installed_demo.py`; authoring modules that still import handlers are listed by owning surface).
- No module names `Microscope` (the enum), `MicroscopeHandler`, `create_microscope_handler`, `MICROSCOPE_HANDLERS`, `SourceComponentProjectionStrategy` or `component_metadata_field`.
- No kernel module contains the `"/omero/"` literal or a `_w{` filename literal.
- No `SourcePlaneStoreAdapter` leaf returns `()` from `discover_stores`; no enricher defines `discover_stores`.

## Tests

- One family test over `DatasetSource.__registry__`: every leaf has a registry key, a selection role and backends; detection order is derived.
- One projection test over the active family's axes (aliases, fallbacks, collection keys, the domain well codec).
- Witness (extends G1's): a remote-sensing family declares prefixes and activates; a synthetic openhcsdata dataset is written through the kernel writer and a two-step pipeline compiles and executes end to end through `OpenHCSDatasetSource`, with zero kernel edits.
- Tests of deleted names are rewritten against the families; the 30-workflow parity check stays at its baseline.

## New-case experiments

Today a new domain's source needs a `Microscope` member, a module in `openhcs/microscopes`, and cannot read or write the openhcsdata format (it fills microscopy fields by name). After: one `DatasetSource` subclass in a module listed by the family's `extension_modules`; openhcsdata works unchanged.

## Corrections made while executing

- Domain config sections cannot be decorated with `@global_pipeline_config` inside the domain: importing the domain module before the kernel config would inject the global config without them. Sections instead inherit the light kernel marker `GlobalConfigSection` (`core/config_sections.py`); the kernel config imports the family's `config_modules` and decorates every declared section.
- `PostExecuteHook` lives in `core/post_execute.py`, not `core/orchestrator/`: the orchestrator package import closes a cycle with the compiler.
- Validation of `PipelineConfig.dataset_source` runs while modules import; the choice set tests membership by inheritance so it never triggers registry discovery.
- The base `post_workspace` rename loop (pad filenames, default Z to 1) is microscopy behaviour; it moved with the virtual-mapping workflow to `microscopes/vendor_layout.py` (`VirtualMappingSource`). The OpenHCS and Bio-Formats `post_workspace` overrides had no caller and are deleted.
- Plate-manager auto-add is an authoring flag read by the GUI from the global config, not a worker hook; it left `ProcessingContext` and `zmq_compilation` reads it from the resolved config.
- Grouped artifact paths now spell the group axis's own token: a step grouped by site writes `A01_s003_x.pkl`, not `A01_w3_x.pkl`.

## Handoff

- **G7:** vocabulary (`plate_path`, `microscope_handler_name` JSON key, `context.microscope_handler` attribute, MCP `microscope_type`) is renamed with the runtime vocabulary.
- **G8:** `FilenameParser.extract_component_coordinates` callers (image browser, Zarr HCS writer) move onto a grid role; G4 put the `A01` split on `Microscopy.Well.grid_coordinates`. The experimental-analysis menu in `pyqt_gui/main.py` is domain authoring.
- **G3:** `SourceVoxelSpacing.values_zyx` and the `("z", "y", "x")` calibration keys are the N-d spatial domain.
- **L1 (metaclass-registry):** `LazyDiscoveryDict._discover` logs and swallows discovery errors and marks the registry discovered; a failing domain module then leaves a silently partial registry. Discovery failures should propagate.
- **K2:** `grouped_artifact_path` sits in `artifacts.py`; it now takes the group axis.

## Done when

The kernel imports no domain module; the openhcsdata format and filename codecs derive from axis declarations; the enum, the five strategies and the hardwired consolidation are gone; the guards, the family tests, the witness and the parity check (baseline 29/30) pass.
