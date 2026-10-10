# G5: The processing contract family and the measurement dialect

**Head audited:** `openhcs` `main` at `89b8fdbff` (#1185; G1, G2, G3, G4, G6 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.** Replaces K3 and K8.
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "Processing semantics". *Uses:* G1 `Axis`/`AxisFamily`/roles, G3 `ImagePayload`/`PayloadAxes`, `AutoRegisterMeta`.

## What is wrong

**A processing contract is an enum whose members forward to per-member registry methods, crosses the decorator as a name string, and is re-decided by the CellProfiler executor; two of the function requirements are enums over one member each; and the kernel spells CellProfiler's measurement names (IDEN-1, IMPL-2, MEMB-2).**

Census at this head. Production = Python under `openhcs/`. Kernel = `openhcs/` minus the G1 domain allowlist, `openhcs/interop/` and `openhcs/processing/backends/cellprofiler/` (the CellProfiler domain; P1 moves both to `domains/cellprofiler`).

### Contract-kind dispatch (AST: compares, `match`, tables, `isinstance`, by-name lookups and forwarding against the contract kinds; 21 sites in 6 files, plus 2 enum re-dispatches)

- **The enum.** `ProcessingContract(Enum)` (`processing/backends/lib_registry/unified_registry.py:1231-1296`) maps four members onto four declaration classes (`:999-1228`) and adds `declaration`, `declared_name`, `from_declared_name`, `semantic_control_parameter_types` and an `execute` that forwards to the declaration.
- **Forwarding.** Each declaration's `execute` calls back into the executor by member: `registry.execute_pure_3d` (`:1128`), `registry.execute_pure_2d` (`:1153`), `registry.execute_volumetric_to_slice` (`:1219`); the bodies live on `LibraryRegistryBase` (`:1797`, `:1813`, `:1979`) and again on `CellProfilerFunctionContractExecutor` (`interop/cellprofiler/runtime/function_contract_execution.py:223`, `:434`, `:573`).
- **Re-dispatch through the enum.** `FlexibleProcessingContract.execute` calls `ProcessingContract.PURE_2D.execute` / `ProcessingContract.PURE_3D.execute` (`unified_registry.py:1185`, `:1192`).
- **The CellProfiler executor matches on the kind.** `match mode, processing_contract` with every member listed in three cases (`function_contract_execution.py:123`, `:144`, `:157`); `callable_contract.processing_contract is ProcessingContract.PURE_3D` decides validation (`:235`, `:306`); `executor.execute_pure_3d` is called directly for FULL_STACK mode (`:151`).
- **Three encodings.** The decorator turns the member into its lowercase name (`core/memory/decorators.py:159-170`), stores the string (`declared_processing_contract`), and turns it back by name at five sites: `decorators.py:245`, `callable_contract.py:2124`, `openhcs_registry.py:807`, `:813`, `registry_service.py:506`; the function cache stores `contract.name` and reads `ProcessingContract[...]` (`unified_registry.py:2141`). `CallableMetadata.processing_contract` is typed `Enum | None` (`callable_contract.py:395`) and checked with `isinstance(..., ProcessingContract)` (`:1409`, `:1430`); the validator labels errors with `processing_contract.name if isinstance(processing_contract, Enum)` (`funcstep_contract_validator.py:1209`).
- **Classification table.** `classify_function_behavior` maps probe outcomes to members through a dict (`unified_registry.py:2353-2359`) and `_classify_dual_support` (`:2366`) tests `len(shape) == 2` against probes of shape `(3, 20, 20)` / `(20, 20)` (`:2314`): the rank is hard-coded instead of taken from the active family's `payload_spatial_rank`.
- **Ownership (K8).** The family lives in `processing/backends/lib_registry`, yet `core/callable_contract.py`, `core/memory/decorators.py`, `core/runtime_batch_contracts.py` and `core/function_reference.py` import it (lazily, around a cycle).
- **Execution modes are enums matched at call sites.** `ImagePayloadExecutionMode` (`core/image_payload_execution_mode.py:13`; NATURAL, FULL_STACK, ALIGNED_MULTI_IMAGE_STACK) is matched in the executor above and compared at `unified_registry.py:1139`, `runtime_batch_contracts.py:122`, `function_contracts.py:180`, `interop/.../invocation.py:474`, `object_measurement_execution.py:81-119`, `module_execution.py:1548`. `RuntimeCallableView` and `RuntimeInvocationKwargPolicy` (`unified_registry.py:130-250`) are enums restated by an `EnumKeyedStrategyMixin` strategy family one-to-one.

### Function requirements declared by flag

Role requirements on the step's variable axes already exist (`required_axis_roles`, G1/G2: colocalization, color, alignment and worms ask `ColourAxis`, tracking `TimeAxis`, flatfield its observation role). What is left:

- `PrimaryImageCarrierRequirement(str, Enum)` with one member `SOURCE_CHANNEL_AXIS` and an `if self is …` body (`callable_contract.py:253-280`), and `PrimaryImageCarrierTransition` (`:283-311`; `PRESERVE`, `CREATE_SOURCE_CHANNEL_AXIS`). They encode "the primary image declares a colour axis", by name. Consumers: `compiler.py:1128-1335`, `function_patterns.py:913-1240`; declarations `processing/backends/cellprofiler/color.py:1536,1637`, `crop.py:853`.
- `ObjectLabelInputExecutionMode(str, Enum)` (`core/pipeline/function_contracts.py:149`; FULL_STACK, MATCH_IMAGE_STACK, SLICE_ALIGNED): 16 declarations in CellProfiler backends, compared at `function_contracts.py:180,444,446`, `unified_registry.py:1970`, `object_measurement_execution.py:56,101`.

### CellProfiler naming in kernel modules (AST over string literals, names, attributes, definitions and arguments; docstrings excluded: 171 occurrences in 18 files)

| Spelling | Hits | Where |
|---|---|---|
| `image_number` (CellProfiler's `ImageNumber`, the sample identity) | 75 | `core/equivalence/measurement_rows.py` 49 (`RuntimeImageNumberOffset` `:198-300`), `core/runtime_measurements.py:1207,1871-1897`, `core/steps/abstract.py:62-161`, `processing/materialization/core.py` 15, `core/equivalence/relationships.py`, `core/runtime_exports.py:214`, `core/steps/function_artifact_materialization.py:1255` |
| `unedited` / `small_removed` label variants (IdentifyPrimaryObjects outputs) | 70 | `core/runtime_object_labels.py` 54, `runtime_object_label_aggregation.py` 8, `runtime_object_label_building.py` 4, `measurement_image_alignment.py` 4 |
| `zernike` tolerances | 4 | `core/equivalence/policy.py` |
| `Parent_`, `Children_`, `_Count` relationship feature names | 3 | `core/runtime_relationships.py` |
| `from_cellprofiler_xyz` | 1 | `core/source_metadata.py:929` |
| `CROP_MASK` | 1 | `core/artifacts.py:1811` |
| `MeasurementScope.EXPERIMENT` (plus `IMAGE`, 63 production references to the two) | 3 | `runtime_measurements.py:525`, `equivalence/keys.py`, `equivalence/measurement_rows.py` |
| `from_cellprofiler_pipeline` (scope marker) | 3 | `ui/shared/plate_scope_identity.py`, `pyqt_gui/widgets/plate_manager.py` (U1 owns; see Handoff) |

- **Two dialect classes fed by the same providers (K3).** `RuntimeMeasurementLookupDialect` (`core/measurement_lookup_dialect.py:53`, 5 value/provider pairs) and `RuntimeMeasurementDialect` (`core/equivalence/policy.py:305`, 13 value/provider pairs and 6 provider-only fields) are both dataclasses of callables; the CellProfiler instances (`interop/cellprofiler/measurement_dialect.py:109`, `:150`) pass the same `CellProfilerModule` classmethods into both, and `cellprofiler_lookup_dialect_for_measurement_owner` (`:125`) rebuilds one with `dataclasses.replace`. Each field pair is a `None`-mode: "use the tuple, or call the provider".

## Target

```python
# openhcs/core/processing_contracts.py (kernel)
class ProcessingContract(ABC, metaclass=AutoRegisterMeta):   # identity: the subclass
    key: ClassVar[str]                                        # boundary spelling ("pure_2d"), registry key
    def execute(self, call: ContractCall, image, kwargs): ...  # the behaviour
class Pure3DContract(ProcessingContract)          # whole stack, once
class Pure2DContract(ProcessingContract)          # each plane of the declared plane axis
class FlexibleContract(Pure2DContract, Pure3DContract)   # semantic control picks a parent's execute
class VolumetricToSliceContract(ProcessingContract)       # whole stack in, plane axis collapsed out
class ContractCall(ABC)    # one callable invocation's environment: invoke, plane split, slice batch, aggregation
class LibraryContractCall(ContractCall)          # kernel default (registry wrappers)
# interop: CellProfilerContractCall(ContractCall)  (compiled plane projection, profiling, aligned stacks)
```

- **Identity.** A decorator takes the contract class (`contract=Pure2DContract`); callable metadata stores the class; strings exist only at boundaries (function cache, catalog DTO, LLM context) and come from `key` through the family registry. **Deleted:** the `ProcessingContract` enum, `declaration`, `declared_name`, `from_declared_name`, the `declared_processing_contract` attribute and string path, `_declared_processing_contract_name`, every `isinstance(..., ProcessingContract)` on an `Enum`.
- **Execution.** Each contract's `execute` holds its algorithm over `ContractCall` primitives; `FlexibleContract` calls its parents' `execute` directly. **Deleted:** `LibraryRegistryBase.execute_pure_3d/execute_pure_2d/execute_volumetric_to_slice`, the executor's same-named methods, the enum re-dispatch, the `match mode, processing_contract`, the two `is ProcessingContract.PURE_3D` checks (a declared capability on the contract).
- **Execution modes are a family.** `ImagePayloadExecutionMode` members become subclasses owning their execution step; `RuntimeCallableView`/`RuntimeInvocationKwargPolicy` enums are deleted and their strategy classes are the identity.
- **Classification by declaration.** Each contract declares which probe outcome it explains; the probe arrays take their rank from `AxisFamily.active().payload_spatial_rank`.
- **Ownership.** The family, the plane slicers and aggregators and the callable invocation policy move to `openhcs/core/processing_contracts.py`; `unified_registry.py` keeps the library registries.
- **Requirements by role.** `@requires_payload_axis(ColourAxis)`, `@creates_payload_axis(ColourAxis)` and `@preserves_payload_axes` replace the carrier requirement and transition enums; the requirement asks the source file's declared payload axes for the role. `ObjectLabelInputExecutionMode` becomes a family whose members own the decision their consumers make today.

```python
# openhcs/core/measurement_dialect.py (kernel)
class MeasurementDialect(ABC, metaclass=AutoRegisterMeta):
    # how rows are named and shaped: sample identity fields, object identity fields,
    # scope spellings, label variants, relationship feature names, lookup aliases,
    # comparison qualifiers; one method per question, no value/provider pairs
class PlainMeasurementDialect(MeasurementDialect)      # kernel default: kernel field names
# openhcs/interop/cellprofiler/measurement_dialect.py
class CellProfilerMeasurementDialect(MeasurementDialect)   # ImageNumber, Image/Experiment, Unedited/SmallRemoved, Parent_/Children_
```

- **One dialect.** `RuntimeMeasurementLookupDialect` and `RuntimeMeasurementDialect` merge into `MeasurementDialect`; providers become overridden methods on the CellProfiler subclass; the per-owner `replace` becomes a subclass instance bound to its module.
- **The kernel names samples and runs.** `MeasurementScope.IMAGE/EXPERIMENT` become `SAMPLE/RUN`; "Image" and "Experiment" are the CellProfiler dialect's spellings. `image_number` in kernel rows, exports and materialization becomes `sample_number`; detecting ImageNumber reference fields and the image-number offset move to the CellProfiler dialect.
- **Label variants are declared by the dialect.** Object labels carry `variants: Mapping[type[LabelVariant], data]`; CellProfiler declares `Unedited` and `SmallRemoved`.
- **Moved to interop:** `from_cellprofiler_xyz`, `CROP_MASK`, the relationship `Parent_`/`Children_`/`_Count` spellings, the Zernike tolerances.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Function registry cache (stores the contract key), compiled plans, worker bundles | runtime | reset |
| Saved pipelines and configs | durable | unchanged: they name functions, not contracts |
| User custom functions | durable | unchanged: the templates declare no contract |
| CellProfiler-format outputs (`ImageNumber`, `Image`/`Experiment` tables) | external contract | unchanged: spelled by the CellProfiler dialect |

## Guards

`tests/unit/test_g5_processing_contract_guards.py` (AST over `openhcs/`):
- No `ProcessingContract.<MEMBER>` attribute, no `ProcessingContract[...]`, no `from_declared_name`, no `declared_processing_contract`; no `execute_pure_2d`/`execute_pure_3d`/`execute_volumetric_to_slice` definition or attribute.
- Outside `openhcs/core/processing_contracts.py`, no compare, `match` case, dict key or `isinstance`/`issubclass` against a contract class.
- No `PrimaryImageCarrierRequirement`, `PrimaryImageCarrierTransition`; no compare or `match` against an execution-mode or object-label-mode member outside its family module.
- CellProfiler naming: the set of (module, spelling) for the census spellings in kernel modules **equals** an exact allowlist (U1's scope marker only); a new spelling or a removed exemption both fail.

## Tests

- Witness (`tests/unit/test_axis_family_witness.py` and its subprocess script): the remote-sensing family runs a pipeline whose measurement step is named and shaped by a witness-declared `MeasurementDialect`, end to end, with no `openhcs.microscopes`, `openhcs.interop` or `openhcs.processing.backends.cellprofiler` module loaded.
- One family test for the contract family (registry keys, boundary round trip, classification).
- Tests of deleted structure (enum members, the per-member registry methods, provider fields) are rewritten onto the family or deleted.
- 30-workflow CellProfiler parity (baseline 29/30) and `tests/integration/test_main.py` disk and zarr direct cases.

## New-case experiments

- A new contract kind (for example "per tile"): before, an enum member, a declaration class, a registry `execute_*` method, an executor method, a `match` arm and a name in the decorator string path. After: one `ProcessingContract` subclass.
- A new measurement dialect: before, two dataclasses of provider callables, and the kernel still spells `image_number`. After: one `MeasurementDialect` subclass.

## Done when

The enum, the forwarding methods, the string path, the requirement enums and the kernel's CellProfiler spellings are gone; the guards and the witness pass; the touched tests, the parity check (baseline 29/30) and the `test_main.py` disk and zarr direct cases are green.
