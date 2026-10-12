# E2: Classes that restate an existing declaration

**Head audited:** `openhcs` `main` at `ae6ddace5` (#1210, K1 merged); `pycodify` `main` at `e3e3d99` (0.2.0). **Rules:** [00-RULES.md](00-RULES.md). **Step 4 sweep.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* pycodify `SourceDocument`. *Uses:* pycodify `Assignment` / `generate_python_source` (L6), `MeasurementDialect.row_identity_contract`.

## What is wrong

**A second class restates a fact that a declaration next to it already holds, and the two are kept equal by convention.** Agreement between two copies does not say which one is the source ([P10] Proposition 2.2); a copy is one implementation or two, never a saving ([P1] Theorem 4.7).

1. **Document field enums: a grid of document kind × "Field".** `ConfigDocumentField` (`core/config_document.py:15`, 1 member), `PipelineDocumentField` (`core/pipeline_document_fields.py:6`, 2 members), `FunctionStepDocumentField` (`core/function_step_document.py:13`, 1 member). Each spells the module-level assignments of a generated `.py` file. `PipelineDocument` and `FunctionStepDocument` are dataclasses whose fields have exactly those names; the config document has no dataclass at all. Each of the three codecs hand-writes the same three steps (read a namespace by name, `exec` source, build `Assignment`s). A fourth document kind needs a fourth enum and a fourth copy: one class per cell of the grid ([P1] Theorem 4.5). pycodify has `Assignment` and `generate_python_source` but nothing that maps a dataclass to its assignments; `objectstate.codegen` has formatters only.
2. **One-member enums** (13 in `openhcs/`): each holds one fact. Verdicts in the table below.
3. **Agent config labels.** `ConfigFieldRequirementLabel` and `ConfigFieldResolutionLabel` (`agent/services/llm_context_service.py:615, 626`) turn `ConfigFieldSchema.required` and `.lazy` (two booleans) into two enums and back into text at one call site.
4. **Scan** for the same two shapes (115 enums with one or two members, 23 glued class names). The 15 most suspicious outside the brief are in the second table.

## Target

- **pycodify `SourceDocument`** (`pycodify/documents.py`, library PR, no version bump). A dataclass that inherits it is saved as one Python module: each constructor field (`init=True`) is one module-level assignment, in declaration order. It supplies `assignment_names()`, `from_namespace()` (a field with a default may be absent; a required one raises `ValueError`), `from_source()`, `body()` and `to_source(header=, clean_mode=)`. Identity is nominal ([P1] Proposition 3.1): a document is a document because it inherits `SourceDocument`, not because it has a field called `step`.
- **OpenHCS documents.** `PipelineStepsDocument(pipeline_steps)` (the steps-only file), `PipelineDocument(PipelineStepsDocument)` adding `pipeline_config` (default `PipelineConfig()`) and the non-constructor `source_text` (was `original_source`, rule 1b), `FunctionStepDocument(step)`, new `ConfigDocument(config)`. The codecs keep only OpenHCS's type checks and step normalization and call the inherited methods. `ConfigDocumentAuthority` is renamed `ConfigDocumentCodec` (rule 1b).
- **Deleted:** `ConfigDocumentField`, `PipelineDocumentField` and its module `core/pipeline_document_fields.py`, `FunctionStepDocumentField`, `McpReconnectOwner`, `RuntimeBatchCallableMetadataField` and `RUNTIME_BATCH_EXECUTORS_ATTR`, `CellProfilerSpreadsheetRowField`, `ConfigFieldRequirementLabel`, `ConfigFieldResolutionLabel`.
- The refactor merges no two cases that need different answers ([P10] Theorem 5.3): every deleted enum had one member, or (pipeline, labels) members in one-to-one correspondence with the declaration that replaces them.

### Candidates and verdicts (brief)

| Candidate | Fact it holds | Verdict |
|---|---|---|
| `ConfigDocumentField`, `PipelineDocumentField`, `FunctionStepDocumentField` | assignment names of a saved `.py` | **derived** from the document dataclass fields (`SourceDocument`); deleted |
| `McpReconnectOwner` | "the MCP client reopens the stdio session", set iff `restart_required` | **derived**: `reconnect_owner`, `reconnect_required`, `retry_after_reconnect` become properties of the recovery record computed from `restart_required`; enum deleted, wire value `"mcp_client"` unchanged |
| `McpWireContentType` | MCP content block `type: "text"` | **kept**, external spelling: Model Context Protocol tool-result content blocks (the dev client speaks raw JSON-RPC and does not import the SDK types) |
| `DesktopInstallerSchemaVersion` | `"openhcs.installer.v4"` | **kept**, external spelling: the installer contract read by `packaging/installers/macos/install-openhcs.sh` and `windows/Install-OpenHCS.ps1` |
| `RuntimeBatchCallableMetadataField` | one private attribute name on a callable | **deleted**: one module constant; the alias `RUNTIME_BATCH_EXECUTORS_ATTR` was unused |
| `SaveImagesImageKind` | CellProfiler SaveImages "type of image to save" | **kept**, external spelling: `.cppipe` SaveImages setting (`Image`); the other CellProfiler values are unsupported, so the parser must reject them |
| `CellProfilerSpreadsheetRowField` | row key `image_number` | **derived** from `CellProfilerMeasurementDialect.row_identity_contract.sample_number_field`; deleted |
| `_ClassificationResultFieldRole`, `_AlignShiftFieldRole` | which result field carries a routing role | **kept**: an `Annotated` marker is the nominal way to find a field without its name string; the vehicle should be K3's row-role family (reassigned to K3 with `MeasurementRowAxisField`) |
| `AlignModule.AdditionalMode` | CellProfiler Align "Similarly" | **kept**, external spelling: `.cppipe` Align setting |
| `PlateInspectionWorkflowScope` | `workflow_scope: "diagnostic"` | **kept**, external spelling: MCP tool-result schema of plate inspection |
| `ConfigFieldSchema` | one reflected config field | **kept**: MCP result DTO, built only by `agent/services/config_service.py` from `dataclasses.fields` and the step signature; not hand-maintained |
| `ConfigFieldRequirementLabel`, `ConfigFieldResolutionLabel` | text for two booleans | **deleted**: the context section formats the booleans |

### Scan (15 most suspicious outside the brief)

| Candidate | Verdict |
|---|---|
| `PipelineDocumentNormalizationStrategy`, `StepDocumentNormalizationStrategy`, `ConfigDocumentNormalizationStrategy` (`pyqt_gui/services/code_document_normalization.py`) | kept: members of a registered strategy family keyed by declaration type, whose other members (plate manager, custom function, function pattern) are not documents; the three collapse to one when the codecs fold into the documents (see Outcome) |
| `FunctionStepCodeDocumentDriver` (`pyqt_gui/services/function_step_code_document.py`) | glued; used by the dual editor (U-surface agents hold those files): later pass |
| `SyntheticPlateFormat` (`core/synthetic_plate_generation.py`) | restates the microscope handler family: G4 |
| `FormattingMeasurementFeatureTemplate` (1 member, `interop/cellprofiler/runtime/measurement_rows.py`) | K3 |
| `McpBootstrapFailurePhase`, `PlateWorkspacePreparationOperation` | kept, MCP result spellings |
| `DesktopUpdateProgressMode` | kept, Tk progress-bar mode spellings |
| `WormControlPointAxis` | kept, CellProfiler UntangleWorms feature spelling |
| `IntensityDistributionSettingSchema` | kept, `.cppipe` revision layouts |
| `StartupWindowPresentation`, `ViewerControlPingMode`, `ViewerShapePayloadProjection`, `PlateViewerTab` | enums carrying behaviour through `__new__`: rule 1a families; later pass (U3 / G6) |
| `ObjectLabelRepresentation` | restates the `ObjectLabelVariant` family beside it: later pass (G3) |
| `SeededSegmentationRule` | prose in enum values: later pass |
| `ConfigCacheSpec` | a record, not a grid cell: fine |

Not examined, for a later pass: the remaining two-member enums outside `processing/backends/` (`CapabilityTransport`, `PlateFileKind`, `WriteMode`, `FijiPayloadKind`, `ViewerDescriptorField`, `ViewerPersistenceMode`, the K3 and K5 enums E1 reassigned) and the glued names `ObjectLabelVariantData`, `LiveMeasurementTableEntry`, `ViewerComponentValueDomainEntry`, `VirtualWorkspaceSourceProjectionCacheEntry`, `Napari{Image,Points,Shapes}LayerDisplayHandler`, `FijiImagePayloadHandler`, `WindowSpec`, `FunctionStepSpec`.

## Persisted state

Saved `.py` pipelines, steps and configs are durable. The assignment names (`config`, `pipeline_config`, `pipeline_steps`, `step`) are now the dataclass field names and do not change; the round-trip test proves each kind loads what it wrote and writes exactly those names.

## Guards

`tests/unit/test_e2_restated_declaration_guards.py`:
- none of the deleted names appears in `openhcs/`;
- `openhcs/core/pipeline_document_fields.py` does not exist;
- no module under `openhcs/` outside the document modules builds a `pycodify.Assignment` with a string literal naming a document field;
- every `SourceDocument` subclass in `openhcs/` is a dataclass.

## Tests

- `tests/unit/test_source_documents.py`: one family test over every `SourceDocument` subclass: render, load, compare, and assert the assigned names are the constructor fields (`config`; `pipeline_config`, `pipeline_steps`; `pipeline_steps`; `step`).
- pycodify: `tests/test_documents.py` (names, defaults, missing required field, `init=False` skipped, round trip).
- The three per-enum value assertions in the document tests are deleted.

## New-case experiments

A fourth saved document (say a plate layout). Today: a field enum, a codec with its own namespace reader, `exec` wrapper and `Assignment` list. After: one dataclass inheriting `SourceDocument`.

## Done when

The deleted names are gone with no alias; the guards, the round-trip test, the document, codegen and MCP contract tests pass; `guardrails rc=0`; `smoke rc=0`; parity 30/30 (spreadsheet export is touched).

## Outcome and corrections

Done: pycodify `SourceDocument` (library PR OpenHCSDev/pycodify#5, no version bump; the submodule points at its branch head), the four documents and three codecs, the one-member enums, the labels, the guards.

Corrections to the plan above:
- **`pipeline_steps_from_namespace` is kept.** It has no caller in `openhcs/`, but `tests/unit/test_cellprofiler_public_boundary_contracts.py` runs it in a fresh interpreter as the public reader of a generated steps file. It now reads through `PipelineStepsDocument`.
- **Assignment order in a complete pipeline file changes** to `pipeline_steps`, then `pipeline_config`: `PipelineDocument` inherits the steps field from `PipelineStepsDocument`, and dataclass fields are ordered base first. Names and values are unchanged, and files written in either order load. Keeping the old order needs a config-only base class that exists only to order two fields; that is a helper added to fit one chain ([P1] Theorem 4.6), so it was not added.
- **Error text changes** for a missing assignment: `PipelineDocument source must define 'pipeline_steps'.` (was `Pipeline document must define ...`), likewise for the other kinds. A wrong member type in a pipeline reads `Pipeline member N must be FunctionStep` from the one shared check.
- **`PipelineDocument.original_source` is `source_text`** (rule 1b) and is not a constructor field, so it is not an assignment; `read_from(source_text)` attaches it.
- **Certificates.** *derived*: the three field enums (`SourceDocument.assignment_names`), `McpReconnectOwner` and the three stored reconnect fields (properties of `restart_required`), `CellProfilerSpreadsheetRowField` (`row_identity_contract.sample_number_field`, asserted equal to `"image_number"` by the spreadsheet tests). *unused*: `RUNTIME_BATCH_EXECUTORS_ATTR`, `RuntimeBatchCallableMetadataField.owner_label` as a method (inlined at its two sites). *derived*: the two label enums (text of two booleans, same output except that `lazy` is joined by the formatter). No tests-only deletion.

Not done, with owner:
- The codecs still exist: they hold OpenHCS's type checks and step normalization and forward the rest to the document. Folding validation into the documents' `__post_init__` deletes the three codecs and collapses three normalization strategies into one; it touches 60 files (43 of them tests) and belongs to a surface that owns `pipeline_editor.py` and the code-document services.
- `FunctionStepTransportAuthority` keeps its name (rule 1b asks for a rename on touch): 12 product files and 27 test files, several held by open PRs. Proposed for the same later pass.

Test evidence is in the PR description.
