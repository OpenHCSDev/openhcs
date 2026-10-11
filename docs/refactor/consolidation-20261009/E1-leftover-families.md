# E1: Leftover families, value-to-JSON copies and path identity

**Head audited:** `openhcs` `main` at `72a5c3287` (#1200, K4 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4 sweep.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* `AutoRegisterMeta`, python-introspect `to_jsonable` / `RegisteredClassChoices` / `dataclass_from_mapping` (A2 as left by L2 and K6), zmqruntime `TypedWireMessage`, K4's `core/source_path_identity.py`.

E1 owns what K4 and K6 reported outside their briefs and the whole-tree census of rule-1a violations that no surface owned. It does not touch `core/callable_contract.py` or the function-pattern code (K5), `core/artifacts.py` (K2), or the measurement code held in #1199 (K3); enums whose dispatch lives there are reassigned below.

## What is wrong

**Kinds that already have, or need, a family are still enums dispatched by their consumers; two modules hand-write the value-to-JSON switch; two modules compare dataset and store paths with a second identity rule.**

1. **Source-binding enums (K4 handoff).** `core/source_bindings.py:62-118` declares six enums. Each is re-decided by its consumers:
   - `SourceFilterMatchType` (12 members, `requires_value` smuggled through `__new__`) and `SourceFilterSubject` (3) are restated one-to-one as the strategy families `SourceFilterMatcher` and `SourceFilterTargetResolver` (`source_matching.py:113-270`), each leaf naming its member twice (`match_type = X`, `match_type_key = X.value`) and looked up by `.value`. CellProfiler's `LoadImages`/`NamesAndTypes` import keeps a third copy (`processing/backends/cellprofiler/infrastructure.py:86-160`, enums whose members carry our members).
   - `MetadataSource` (2): `is MetadataSource.FOLDER_NAME` in `source_matching.metadata_source_texts` and twice in `infrastructure.py`.
   - `SourceSetRole` (2): `is MATCHED`/`is BROADCAST` in `source_bindings.py` (3), `source_binding_selection.py` (2), `source_binding_workspace.py` (1).
   - `SourceProjectionRole` (2): an `EnumKeyedStrategyMixin` family in `source_binding_workspace.py:507-580` with a totality check against `set(SourceProjectionRole)`, a `projection_role` ClassVar on the `source_projection.py` projection classes, and 14 `is PRIMARY_PLANE`/`is SOURCE_ARTIFACT` tests in `source_bindings.py`, `source_projection.py`, `source_binding_workspace.py`, `compiler.py`, `virtual_workspace_metadata.py`, `function_runtime.py`.
   - `SourceBindingOrigin` (2): 8 `is STEP_INPUT`/`is PIPELINE_START` tests in `source_bindings.py` and `function_runtime.py`.
2. **GUI debug enums (K6 handoff).** `DebugActionPlacement` (4) and `DebugToolbarAuxiliaryAction` (1, a `str` enum used as an action id beside `type[DebugCommandType]`) in `pyqt_gui/widgets/shared/services/pipeline_debug_actions.py`; the toolbar groups buttons by placement member (`debug_toolbar.py:81-92`). `DebugSessionPhase` (`core/debug_session_projection.py:31`, 9 members) keys `DebugSessionPhaseDeclarationBase`, which already carries the behaviour; `PipelineDebugSessionPhase = DebugSessionPhase` is an alias.
3. **`CompiledArtifactInspectionControlPayload`** (`core/artifact_inspection.py:150-195`) copies `CompiledArtifactInspectionRequest`'s one field, converts both ways and hand-codes `to_dict`/`from_dict` with a `type` check against the one-member `ArtifactInspectionControlMessageType`, exactly the shape K6 deleted from the debug requests.
4. **numpy-to-JSON switches (K6 handoff).** `core/plate_image_inventory.py:1455-1500` (`_jsonable_array_values`, `_jsonable_metadata_value`, `_jsonable_scalar`) and `napari_roi_manager/_dataclasses.py:91-105` (`_json_value`) each re-decide None, scalars, numpy scalars, arrays, sequences and mappings beside `to_jsonable`, which lacks only the two numpy types.
5. **Dataset and store identity (K4 handoff).** `SourceDatasetIdentity.for_root`, `SourcePlaneStoreIdentity.container_paths`, `SourcePlaneDataset.root` and `.aggregate` (`source_projection.py:243, 259, 439, 479`) and `DatasetSource._register_virtual_workspace_backend` (`dataset_sources/source.py:363-367`) compare `Path.resolve()` results, a second identity rule beside K4's lexical one; `microscopes/bioformats_adapter.py` feeds them resolved paths.
6. **Whole-tree census.** `openhcs/` declares 373 `Enum` subclasses. 185 of them have members compared (`is`, `==`, `in`), matched or used as dict keys in our own code, at 751 sites. 100 of those are in `processing/backends/` (function parameter choices, mostly CellProfiler setting spellings); 85 are elsewhere. The table in *Census* classifies every one.

## Target

- **Source bindings.** Each enum becomes an `AutoRegisterMeta` family whose members own the behaviour now switched on; fields hold the member class (`type[F]`, `RegisteredClassChoices(F)` for forms; `to_jsonable` spells it by registry key on the wire and pycodify by class name in saved pipelines):
  - `SourceFilterSubject` → `SourceFileName`, `SourceDirectory`, `SourceExtension`, each owning `text_of(path)`; `SourceFilterTargetResolver` is deleted.
  - `SourceFilterMatchType` → text predicates (`TextContains`, `TextDoesNotContain`, `TextContainsRegex`, `TextDoesNotContainRegex`, `TextEquals`, `TextDoesNotEqual`, `TextStartsWith`, `TextDoesNotStartWith`, `TextEndsWith`, `TextDoesNotEndWith`) and path predicates (`PathIsImage`, `PathIsTif`); each owns `matches(...)`, and `requires_value` is which base it inherits. `SourceFilterMatcher` and its twelve leaves are deleted. CellProfiler's spelling table keeps CellProfiler's literals and points at our classes; a negated literal names its negated class through the family (`negated`).
  - `MetadataSource` → `FromFileName`, `FromFolderName`, owning `texts(path)`.
  - `SourceSetRole` → `MatchedSource`/`BroadcastSource`; `SourceProjectionRole` → `PrimaryPlaneProjection`/`SourceArtifactProjection`, keying the workspace strategies by class (`NominalTypeKeyedStrategyMixin`), with totality read from the registry; `SourceBindingOrigin` → `FromStepInput`/`FromPipelineStart`. The `is` tests become what the member answers.
- **GUI debug.** `DebugActionPlacement` → a placement family the toolbar iterates; `DebugToolbarAuxiliaryAction` → the auxiliary action class itself is the identity (its `action_id`). `DebugSessionPhase` is deleted: the `DebugSessionPhaseDeclarationBase` subclasses are the phases (registry key `name`), the alias goes.
- **Artifact inspection.** `CompiledArtifactInspectionRequest` subclasses `TypedWireMessage` (`wire_type = "openhcs_artifact_read_compiled"`); the payload class and `ArtifactInspectionControlMessageType` are deleted; the control strategy keys by `wire_type`.
- **numpy values.** `to_jsonable` registers `numpy.generic` (`.item()`) and `numpy.ndarray` (`.tolist()`) once, in `openhcs/core/numpy_jsonable.py`; both private switches are deleted and their callers call `to_jsonable` (the inventory keeps only its hashable view of the encoded value).
- **Path identity.** Dataset and store identities and roots use `source_path_identity` over `Path.absolute()`; no `resolve()` remains in an identity or equality in these modules or in the adapter that feeds them.
- **Census.** Every dispatched enum outside `processing/backends/` is converted, justified as an external-contract or boundary spelling, or reassigned to the surface holding its files.

## Persisted state

Saved `.py` pipelines and configs that name the six source-binding enums (`SourceFilterSubject.FILE`, …) are durable. **E1-Q1:** rewrite them? Default: no tool, as K4-Q1, G1-Q1 and G7-Q1; they fail loudly on load and are re-saved from the GUI. Two presets in `processing/presets/pipelines/` and `benchmark/validation/corpus.py` are rewritten in this PR; `benchmark/results/` is a frozen record and is not. Wire spellings (`to_jsonable` of a member is its registry key) keep the old `.value` strings.

## Guards

`tests/unit/test_e1_enum_dispatch_guards.py`:
- No module under `openhcs/` dispatches on an `Enum` member (an `is`/`is not`/`==`/`!=`/`in` comparison with `Enum.MEMBER`, a `match` case on one, a dict display keyed by one, or an `EnumKeyedStrategyMixin` key) unless the enum is listed as a boundary spelling or reassigned in the guard's table, each entry naming its module and reason; the table only shrinks.
- The old member spellings of the six source-binding kinds (`SourceFilterSubject.FILE`, …) and the deleted names (`SourceFilterMatcher`, `SourceFilterTargetResolver`, `DebugSessionPhaseDeclarationBase`, `PipelineDebugSessionPhase`, `DebugActionPlacement`, `DebugToolbarAuxiliaryAction`, `CompiledArtifactInspectionControlPayload`, `ArtifactInspectionControlMessageType`, `_jsonable_metadata_value`, `_jsonable_scalar`, `_jsonable_array_values`) stay deleted in the live trees.
- `core/source_projection.py`, `core/dataset_sources/` and `microscopes/bioformats_adapter.py` call no `.resolve(`.

## Tests

- One family test: every member of each new source-binding family round-trips through `to_jsonable`/`registered_class_from_key` and answers its behaviour (filter matching over a path table; metadata texts).
- One numpy round trip through `to_jsonable` (scalar, nested array, mapping of arrays).
- Existing source-binding, matching, workspace, CellProfiler import, editor, debug toolbar, artifact-inspection and inventory tests, updated to the families.

## New-case experiments

- A new filter predicate (say `TextMatchesGlob`). Today: an enum member, a matcher leaf naming it twice, a CellProfiler spelling row, an editor choice. After: one subclass; the editor and wire derive from the registry, CellProfiler adds a row only if CellProfiler spells it.
- A new numpy-bearing value in a preview: today, a third private switch. After: nothing.

## Done when

The brief's items are gone as named; every dispatched enum in the census is converted, justified or reassigned in the guard's table; the guards, the focused suites for touched code, the structural ratchet and nra-r1 pass with no regression.

## Outcome and corrections

Production (Python under `openhcs/`) −4095 +4010; tests −1517 +2120; benchmark and scripts −70 +63. Guards 6/6. Structural ratchet (openhcs, scripts, benchmark) and NRA R1 exit 0. Library PR: python-introspect #22 (0.2.8, `RegisteredClassChoices` validates registry keys in pydantic, so MCP tool schemas accept family-valued fields); the submodule points at its branch head and the `>=0.2.7` pin moves to `>=0.2.8` once it is released.

The census ran as five batches (this worktree plus four in parallel, merged here). Every enum that `test_e1_enum_dispatch_guards.py` finds dispatched is converted, deleted, or listed in its `ALLOWED` table with a reason.

**Converted to families or deleted** (members own the behaviour that was switched on; wire spellings are the old `.value` strings):
- Source bindings: `SourceBindingOrigin`, `SourceSetRole`, `SourceProjectionRole`, `MetadataSource`, `SourceFilterSubject`, `SourceFilterMatchType` (matcher and target-resolver families deleted; `CellProfilerSourceFilterSubject`/`CellProfilerSourceFilterOperator` replaced by the registry and one literal table), `SourceImageSetComponentRole`, `SourceAnchorSelectionStatus` (written, never read), `SourceBindingMatchResolutionStatus`, `StepInputDependencyKind` (the dependency record is now a family: `UnresolvedStepInput`, `NoMainFlowInput`, `PipelineStartInput`, `StepOutputInput`), `InputSource` (`ReadPreviousStep`, `ReadPipelineStart`).
- Debug and GUI: `DebugSessionPhase` (the phase declarations are the phases), `DebugActionPlacement`, `DebugToolbarAuxiliaryAction`, `ArtifactInspectionControlMessageType`, `MainWindowStartupReadinessState`, `_StartupWindowSignal`, `RoiTableColumn`, `SelectedAllSelectionMode`, `DesktopUpdateCheckOrigin`, `DesktopUpdateProgressAction`, `PlateManagerCodeNamespaceField` (a record).
- Runtime and viewers: `OrchestratorState`, `TerminalExecutionStatus`, `ExecutionStatus` (core), `RuntimeObservationMode`, `ZMQRuntimeObservationExportScope`, `MaterializationBackend`, `MaterializedFilenameIdentity`, `CustomFunctionLifetime`, `MfdPresetKey`/`MfdPresetFamily` (one definition per preset), `ViewerSettlePhase`, `ViewerSettleField`, `ViewerPayloadSummaryField`, `ViewerProcessLaunchField`, `ViewerLifecycleMode`, `ViewerLaunchContextMode`, `NapariLayerKind`, `NapariDimensionLabelRouteSource`, `NapariVariableSizeHandling`.
- Agent and MCP: `FunctionParameterSource` (agent- and runtime-supplied branches), `FunctionCatalogControlField`, `FunctionCatalogPreparationStatus`, `SelectedPlateFileQueryTarget`, `UiBridgeOperationStatus`, `UiObjectStateFieldFilter`, `UiActionInvocationStatus`, `UiWindowSemanticMarker`, `DescriptorSetCardinality`, `SummaryView`, `SignatureView`, `CatalogSearchRank`, `WorkflowPollSummaryStatus`, `WidgetTreeOutputFormat`, `McpProcessRecoveryReason`, `McpHttpAuthenticationMode`, `ClientRegistrationStatus`, `AgentRuntimePlatformKey`.
- CellProfiler and labels: `CellProfilerPipelineStage`, `CellProfilerPipelineFileKind`, `ModuleSettingCoverageStatus`, `CellProfilerMeasurementFeatureKind`, `MeasurementImageReferenceDomain`; internal processing kinds `ThresholdDiagnosticDomain`, `WatershedRuntimeFamily`, `ExperimentalAnalysisScope`, `DefineGridVariant`, `SplitOrMergeInputTopology`.

**Boundary spellings kept** (guard table): `processing/backends/` function-parameter choices and CellProfiler setting tables, dispatched only by the declaring function's module and its backend twins (checked module by module: every one is a parameter or CP literal); `CPAPropertyName`, `CellProfilerObjectTableMode`, `CellProfilerSourceImageProjectionField`, `CellProfilerMeasurementTargetScope` (CellProfiler literal tables); `McpWireMethod`, `McpWireContentType` (MCP); `QtPlatformName` (Qt QPA names); `PlateInspectionIssueCode` (`AgentError.code` spellings); `MultiprocessingStartMethod` (stdlib names; converting it showed ObjectState does not pass a class-valued top-level `GlobalPipelineConfig` field down to lazy `PipelineConfig`, which is L6's). `CellProfilerSpatialGridMeasurementFeature` is only a CellProfiler feature-name table: its one reader is its own `render()`, nothing compares its members.

**Reassigned** (guard table, by owner):
- K3 (#1199's measurement files): `MeasurementScope`, `MeasurementRowAxisField`, `MeasurementRowValueField`, `MeasurementStatistic`, `ObjectFeatureArrayDomain`, `RuntimeCellValueKind`, `RuntimeMeasurementFeatureNameMode`, `RuntimeMeasurementQualifierValueMode`, `RuntimeMeasurementSourceNameEncoding`, `MeasurementTableRowLayout`, `MeasurementObjectRowIdentity`, `MissingObjectMeasurementValuePolicy`, `ObjectLabelRepresentation`; `WriteMode` (its policy family restates it one-to-one; converting it edits `spreadsheet_export.py`).
- K5: `FunctionStepExecutionScope`, `ImagePayloadConsumption`, `MainFlowInputProjection`, `RuntimeInvocationDomain`. K2: `ArtifactPayloadShape`.
- Plane-mode family (flagged unowned by G3; needs `artifacts.py` and #1199): `RuntimePlaneAxis`, `ImagePayloadMetadataCompositionMode`, `ObjectLabelDomainScope`.
- L7/G6: `ViewerLayerField`, `ViewerControlField`, `ViewerPayloadField`, `ViewerIntensityWindowField`, `ViewerDescriptorField` (reply-dict keys; the server should emit the agent DTO records and the window service decode them).
- U2: `CapabilityKind`, `CapabilityRole`, `CapabilityVisibility`, `PlateFileKind` (MCP tool-input choices; converting needs the MCP binder to project family fields, which python-introspect 0.2.8 enables).
- No owner yet (proposed E2): `FileFormat` restates PolyStore's format family (`get_format_from_extension`) and keys the image browser's result actions.

Corrections to the plan above:
- **Behaviour changes.** A plate reached through a symlink alias is a different dataset root (lexical identity, as K4 decided); the registration test now checks a lexically equal spelling. `SourceFilterClause` and the role fields no longer coerce strings in `__post_init__`; wire input decodes through `registered_class_from_key`. Catalog control replies carry their value under `result`. `DefineGrid` reads the first grid-definition row, not the last (differs only when a module repeats it).
- **Durable spellings that change** (E1-Q1, no tool): saved `.py` files naming the enums above (`SourceFilterSubject.FILE`, `InputSource.PIPELINE_START`, `MaterializationBackend.DISK`, `NapariVariableSizeHandling.PAD_TO_MAX`, …) fail on load and are re-saved from the GUI.
- **Ratchet fixes beyond the brief.** Flags that restated a member's identity (`writes_zarr`, `streams_from_source_context`, `keeps_every_field`, `completed`, `editable`, `collects_records`, `returns_every_record`, `agent_supplied`) are deleted for nominal identity; the outcome export scope checks its own export path (the rule was written twice); default step directories moved onto the step-input dependency.

Found outside the brief: `processing/materialization/core.py` `json_payload_value` is a third value-to-JSON singledispatch (materialization; passes unknown values through and converts DataFrames, so not a drop-in for `to_jsonable`); `ZMQAuxiliaryParamField` is a wire-key table (L3); `viewer_protocol.py` still declares `ViewerPersistenceMode`, `FijiPayloadKind`, `ViewerProcessPlatform`, `OpenHCSViewerControlMessageType`, `ViewerLayerIsolationField`, `ViewerProtocolStatus` (no member dispatch the guard finds; G6/L7).
