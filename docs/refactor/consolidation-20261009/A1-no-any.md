# A1: `Any` is not a declared type

**Head audited:** `openhcs` `main` at `1b5fe99f5` (#1231). **Rules:** [00-RULES.md](00-RULES.md).
Branch `refactor/A1-no-any-in-declarations`.

## Owner requirement

"We shouldn't allow Any." A declared type is what OpenHCS turns into a form control, an
MCP parameter description and an array conversion. `Any` is the answer that mechanism
needs and does not get.

## What is wrong (measured on `1b5fe99f5`)

**The declarations a user reaches carry six `Any`, and nothing stops a seventh; the rest
of the tree carries 1,385 more and nothing counts them.**

- `SourceSpatialDomain.fill_value: Any` (`openhcs/core/source_spatial_domain.py:88`) is a
  field of `GlobalPipelineConfig.source_bindings_config`. Building the global config form
  headless raises `UnsupportedWidgetTypeError: No typed writable widget projection exists
  for parameter 'fill_value' with annotation 'Any'` inside the widget-creation callback, and
  `ParameterFormManager.form_build_complete` stays `False`.
- `calculate_math(operand1_value: Any, operand2_value: Any)`
  (`openhcs/processing/backends/cellprofiler/measurement_math.py:899`) is a catalogued function.
- Two catalogued functions return `Dict[str, Any]` special outputs
  (`consolidate_special_outputs`, `trace_neurites_rrs_alva`).
- The error appears when a form is built, not when the type is declared.

### Counts (AST, not grep)

Tool: `scripts/any_annotation_report.py`, a report over the packaged ratchet measure
`agent_comms.debt_ratchet.AnyAnnotation` (one definition of "a use of `Any`": parameters,
returns, annotated assignments and type aliases, nested and quoted; `annotation is Any`
in introspection code is not a use). Owners come from a live import: the 57 dataclasses
reachable from `GlobalPipelineConfig` and the lazy config pairs, and the 169 functions
`OpenHCSRegistry().discover_functions()` returns.

Before (grep on 2026-10-12 said about 1,180 for `openhcs/`; grep counts lines, the AST
counts uses):

| package | uses |
|---|---:|
| openhcs | 1391 |
| external/arraybridge/src | 487 |
| external/PolyStore/src | 265 |
| external/ObjectState/src | 249 |
| external/pyqt-reactive/src | 248 |
| external/formbridge/src | 91 |
| external/metaclass-registry/src | 63 |
| external/pycodify/src | 37 |
| external/python-introspect/src | 35 |
| external/zmqruntime/src | 34 |
| **total** | **2900** |

| declared as | uses |
|---|---:|
| parameter | 1617 |
| return | 862 |
| dataclass field | 218 |
| variable | 115 |
| alias | 60 |
| class attribute | 28 |

| owner | uses |
|---|---:|
| internal | 2677 |
| DTO (dataclass that is not a config) | 217 |
| catalogued function | 5 |
| config dataclass | 1 |

## What landed

### After (same tool, branch head)

| | before | after |
|---|---:|---:|
| openhcs | 1391 | 1373 |
| libraries under `external/*/src` | 1509 | 1509 |
| config dataclass fields typed `Any` | 1 | 0 |
| catalogued function parameters typed `Any` | 2 | 0 |
| catalogued function returns containing `Any` | 3 | 3 (map, JSON-like) |

### Retyped

| declaration | was | now | evidence |
|---|---|---|---|
| `SourceSpatialDomain.fill_value` (config field; also the six parameters that carry it in `source_spatial_domain.py` and `aligned_image_payload.py`) | `Any` | `FillValue = bool \| int \| float` | callers pass `0` and `False`; it is written with `np.full(..., fill_value, dtype=array.dtype)` and stored through `to_jsonable`, so it is a JSON number or a mask's `False`. The form gives it the literal-union editor |
| `calculate_math(operand1_value, operand2_value)` and the two `KeywordRuntimeParameter.annotation_type` declarations that restate them | `Any` | `MathOperandValue = MathOperandSliceValue \| RuntimeSliceAlignedValueSet[MathOperandSliceValue]`, `MathOperandSliceValue = float \| np.ndarray` | `CalculateMathInputPolicy.operand_value` returns a `float` count or scalar, an `np.asarray` vector, or `RuntimeSliceAlignedValues`; the consumer does `np.asarray(value, dtype=float)` or dispatches on `RuntimeSliceAlignedValueSet` |
| `MathOperand.value`, `MathCalculationRequest.for_operand_values`, `MathOperandSliceAlignment.aligned_operands` | `Any` | the same two aliases | same flow |
| `_create_external_virtual_modules(all_functions)` (function registration) | `Mapping[str, Any]` | `Mapping[str, FunctionMetadata]` | reads `metadata.registry` and `metadata.func` |
| `CustomFunctionManager._create_execution_namespace()` (custom-function registration) | `dict[str, Any]` | `dict[str, object]` | an `exec` namespace: user code binds whatever it defines, so any object truly is accepted |

Not retyped, recorded: the two catalogued functions whose special outputs are
`Dict[str, Any]` (`consolidate_special_outputs`, `trace_neurites_rrs_alva`). They are
returns, not parameters, and belong to the JSON-like cause below.

## Guards

1. **Config fields, at declaration.** `openhcs/core/stated_types.py::require_stated_field_types`
   walks a root's fields and every dataclass they nest and raises `UnstatedTypeError`
   naming `Class.field`. Called where each root's family is complete:
   `openhcs/core/config.py` right after `_inject_all_pending_fields()` (covers
   `GlobalPipelineConfig`, `PipelineConfig` and every `@global_pipeline_config` member),
   and `openhcs/pyqt_gui/config.py` after `UIConfig`. Importing the module is the check.
2. **Function parameters, at declaration.** `require_stated_parameter_types` reads the
   signature the catalogue exposes (so runtime-bound parameters are included) and names
   each parameter. Built-ins: `OpenHCSRegistry._metadata_for_function` (catalogue
   discovery). Custom functions: `custom_functions/validation.py::validate_function`; the
   message tells the user to state the type and gives examples.
3. **Everything else, a ratchet.** `AnyAnnotation` in `agent-comms-ratchet`
   (OpenHCSDev/agent-comms #745, merged as `863fbf89`), keyed per file. Pin moved in
   `.github/workflows/refactor-guardrails.yml` and `.claude/verify/guardrails_local.sh`.

### The measure tracks the thing

Totals over `openhcs/` at old revisions, then for each interval the three files that
rose most, checked against the diff between the two revisions (count of the word `Any`
on added and removed lines, imports excluded; the diff also counts prose, so it can
exceed the measure):

```
origin/main      5235c1a95 2026-10-12 files=685 AnyAnnotation=1391
origin/main~150  e4d4108ee 2026-10-07 files=702 AnyAnnotation=1338
origin/main~600  78f2f0b31 2026-10-03 files=704 AnyAnnotation=1266
origin/main~2000 9ef9b73e5 2025-10-02 files=293 AnyAnnotation=589

origin/main~150..origin/main: net 53, files up 32, files down 50
  +173 openhcs/core/processing_contracts.py: diff adds 173 'Any' words, removes 0
  +50 openhcs/processing/backends/processors/image_stack_operations.py: diff adds 50 'Any' words, removes 0
  +34 openhcs/core/dataset_sources/openhcs_format.py: diff adds 36 'Any' words, removes 0

origin/main~600..origin/main~150: net 72, files up 19, files down 9
  +23 openhcs/core/runtime_image_values.py: diff adds 29 'Any' words, removes 6
  +16 openhcs/core/runtime_slice_projection.py: diff adds 16 'Any' words, removes 0
  +16 openhcs/core/callable_contract.py: diff adds 20 'Any' words, removes 3

origin/main~2000..origin/main~600: net 677, files up 119, files down 85
  +106 openhcs/processing/backends/lib_registry/unified_registry.py: diff adds 109 'Any' words, removes 0
  +68 openhcs/core/callable_contract.py: diff adds 69 'Any' words, removes 0
  +68 openhcs/core/aligned_image_payload.py: diff adds 68 'Any' words, removes 0
```

Existing measures are unchanged by the new pin (old pin `aea99bf7` against the branch
that merged, over `origin/main~25..origin/main`):

```
old openhcs exit 0
new openhcs exit 1
openhcs base: old keys 9235, new keys minus AnyAnnotation 9235, identical True, AnyAnnotation keys 442 sum 1128
openhcs head: old keys 9235, new keys minus AnyAnnotation 9235, identical True, AnyAnnotation keys 442 sum 1144
openhcs delta: old keys 9235, new keys minus AnyAnnotation 9235, identical True, AnyAnnotation keys 442 sum 16
openhcs paths identical True (442 changed files)
old scripts exit 0
new scripts exit 0
scripts base: old keys 395, new keys minus AnyAnnotation 395, identical True, AnyAnnotation keys 13 sum 171
scripts head: old keys 395, new keys minus AnyAnnotation 395, identical True, AnyAnnotation keys 13 sum 171
scripts delta: old keys 395, new keys minus AnyAnnotation 395, identical True, AnyAnnotation keys 13 sum 0
scripts paths identical True (13 changed files)
old benchmark exit 0
new benchmark exit 0
benchmark base: old keys 804, new keys minus AnyAnnotation 804, identical True, AnyAnnotation keys 32 sum 31
benchmark head: old keys 804, new keys minus AnyAnnotation 804, identical True, AnyAnnotation keys 32 sum 29
benchmark delta: old keys 804, new keys minus AnyAnnotation 804, identical True, AnyAnnotation keys 32 sum -2
benchmark paths identical True (32 changed files)
```

## Tests

- `tests/unit/pyqt_gui/test_config_forms_build.py`: builds the form headless
  (offscreen) for every concrete config type (the two roots, `UIConfig`, every lazy
  pair: 43 forms) and asserts no `UnsupportedWidgetTypeError` and a completed build.
  With `FillValue = Any` restored it fails for `GlobalPipelineConfig` and one nested
  config with the original message.
- `tests/unit/test_stated_types.py`: `Any` found at any depth, evaluated or quoted;
  a nested config field refused by name; a custom function refused with the message; a
  built-in refused at discovery.
- agent-comms `tests/guards/test_debt_ratchet.py`: 68 pass (62 existing, 6 new cases).

## Findings and follow-ups (not done here)

- **No nominal type for "an array of a supported library".** arraybridge types every
  array `Any` (`arraybridge/types.py` 194 uses, `array_operations.py` 252); OpenHCS has
  `RuntimeArrayData = RuntimeArrayPayload | np.ndarray`, which is numpy only.
  Proposal (owner: arraybridge): an ABC `Array` whose members are each framework's array
  class, registered by the `MemoryType` declaration when its library imports (P1
  Proposition 3.3: a structural protocol would admit any object with `shape` and `dtype`;
  membership here must be declared). Per-library forms follow from the same registry.
  This is the largest single cause: about 397 uses in `openhcs/` and 315 in the libraries.
- **The config guard's generic owner is ObjectState.** `_inject_multiple_fields_into_dataclass`
  is where a config family is consumed. The check sits in OpenHCS at the two root
  declarations because moving it needs an ObjectState release in lockstep; `UIConfig` is
  a plain dataclass root that ObjectState never decorates, so it would still need its
  own call.
- **`KeywordRuntimeParameter` restates the signature.** `annotation_type` and
  `parameter_default` repeat what the function's own parameter declares
  (`measurement_math.py`, and `np.ndarray | None` in five other CellProfiler modules).
  Owner: the runtime-bound parameter family in `openhcs/core/callable_contract.py`.
- **External-library parameters inferred as `Any` are hidden, not refused.**
  `RuntimeTestingRegistryBase._annotation_has_authored_value`
  (`unified_registry.py`) treats `Any` as "no editor"; those signatures belong to
  scikit-image, CuPy and pyclesperanto, so the guard applies to OpenHCS declarations only.
- **Six catalogued parameters have no annotation at all** (live probe). The guard
  refuses `Any`, not a missing annotation; the same reasoning applies to them.
- The ratchet covers `openhcs`, `scripts` and `benchmark`. The libraries under
  `external/` are separate repositories without it.

## The map of the remainder

Grouped by cause from the annotation text and the names on the line (a scratch script
over the report's JSON; candidates, not verdicts: a use lands in the first cause that
matches, in the order JSON-like, registry, array, callable, any-object, missing family,
pass-through).

### openhcs: 1373

| cause | uses | examples |
|---|---:|---|
| JSON-like payload (str-keyed mapping of Any) | 399 | openhcs/agent/dto/functions.py:55 `def from_control_payload(cls, payload: Mapping[str, Any]) -> Self:`<br>openhcs/agent/services/viewer_endpoint_discovery.py:40 `def as_dict(self) -> dict[str, Any]:`<br>openhcs/core/aligned_image_payload.py:1612 `def __getstate__(self) -> dict[str, Any]:` |
| array typed Any (library optional or no nominal array type) | 397 | openhcs/core/aligned_image_payload.py:81 `def array(self) -> Any:`<br>openhcs/core/image_file_serialization.py:64 `def validated_channel_axis(self, payload: Any) -> int | None:`<br>openhcs/core/image_payload_execution_mode.py:40 `image: Any,` |
| value passed through generic machinery (TypeVar candidate) | 193 | openhcs/authoring/session/live_measurements.py:106 `def _semantic_sort_atom(value: Any) -> tuple[int, int | str]:`<br>openhcs/core/aligned_image_payload.py:76 `value: Any`<br>openhcs/core/callable_contract.py:141 `def default_value(cls) -> Any:` |
| missing family (a named domain object typed Any) | 138 | openhcs/agent/services/viewer_endpoint_discovery.py:150 `response: Any,`<br>openhcs/core/aligned_image_payload.py:552 `def compose_mask(self, composed: Any, metadata: ImagePayloadMetadata) -> Any | None:`<br>openhcs/core/callable_contract.py:375 `def read(self, value: object, *, owner: str) -> Any:` |
| callable or *args/**kwargs forwarded untouched (ParamSpec/TypeVar) | 94 | openhcs/authoring/session/events.py:31 `def __init_subclass__(cls, **kwargs: Any) -> None:`<br>openhcs/core/callable_contract.py:1826 `) -> Callable[[Callable[..., Any]], Callable[..., Any]]:`<br>openhcs/core/dataset_sources/discovery.py:45 `**kwargs: Any,` |
| other (unclassified parameter or variable) | 82 | openhcs/core/aligned_image_payload.py:497 `self, payloads: Sequence[Any] | None = None,`<br>openhcs/core/callable_contract.py:128 `annotation_type: ClassVar[Any] = inspect.Parameter.empty`<br>openhcs/core/dataset_sources/openhcs_format.py:867 `values_by_axis: Mapping[type[Axis], Any],` |
| record field with no stated type (DTO) | 26 | openhcs/core/aligned_image_payload.py:354 `reference_payload: Any | None = None`<br>openhcs/core/callable_contract.py:1724 `public_defaults: tuple[tuple[str, Any], ...] = ()`<br>openhcs/core/compiled_step_plan.py:274 `input_source: Any = None` |
| registry or cache value (non-str key or named registry) | 23 | openhcs/core/aligned_image_payload.py:1322 `) -> dict[ArtifactSpecRef, Any]:`<br>openhcs/core/callable_contract.py:1061 `) -> dict[ArtifactSpecRef, Any]:`<br>openhcs/core/measurement_feature_queries.py:406 `row_masks: Mapping[int | None, Any | None] | None = None,` |
| genuinely any object (dunder protocol, equality, isinstance probe) | 21 | openhcs/core/callable_contract.py:920 `) -> tuple[Callable[..., "CallableContract"], tuple[Any, ...]]:`<br>openhcs/core/lazy_gpu_imports.py:21 `self._module: Any | None = None`<br>openhcs/core/measurement_row_materialization.py:540 `def __getitem__(self, column_name: str) -> Sequence[Any]:` |

### libraries: 1509

| cause | uses | examples |
|---|---:|---|
| array typed Any (library optional or no nominal array type) | 315 | external/arraybridge/src/arraybridge/array_geometry.py:26 `def from_value(cls, value: Any) -> ArrayGeometry | None:`<br>external/arraybridge/src/arraybridge/array_operations.py:27 `def _dtype_name(dtype: Any) -> str:`<br>external/arraybridge/src/arraybridge/array_payload.py:14 `def array_payload_data(self) -> Any:` |
| JSON-like payload (str-keyed mapping of Any) | 304 | external/formbridge/src/formbridge/managers/time_travel_binding.py:22 `self._limbo_items: dict[str, Any] = {}`<br>external/formbridge/src/formbridge/services/function_pattern_code_document.py:163 `) -> dict[str, Any]:`<br>external/formbridge/src/formbridge/services/widget_tree_projection_config.py:40 `def compact_dataclass_projection(value: object) -> dict[str, Any]:` |
| missing family (a named domain object typed Any) | 265 | external/arraybridge/src/arraybridge/array_operations.py:47 `def _scaled_values(result: Any, result_min: Any, result_max: Any, target_dtype: Any) -> An`<br>external/arraybridge/src/arraybridge/decorators.py:184 `def apply(self, request: DtypeConversionRequest) -> Any:`<br>external/arraybridge/src/arraybridge/dtype_scaling.py:11 `def _scale_generic(result: Any, target_dtype: Any, mem_type: MemoryType) -> Any:` |
| value passed through generic machinery (TypeVar candidate) | 240 | external/arraybridge/src/arraybridge/decorators.py:301 `) -> tuple[int | None, Any | None]:`<br>external/arraybridge/src/arraybridge/stack_utils.py:143 `) -> list[Any]:`<br>external/formbridge/src/formbridge/flash_trace.py:54 `def _format_value(cls, value: Any) -> str:` |
| callable or *args/**kwargs forwarded untouched (ParamSpec/TypeVar) | 139 | external/arraybridge/src/arraybridge/array_payload.py:23 `transform: Callable[[Any], Any],`<br>external/arraybridge/src/arraybridge/decorators.py:158 `scale_func: Callable[[Any, Any], Any]`<br>external/arraybridge/src/arraybridge/types.py:27 `ConversionFunc = Callable[[Any], Any]` |
| other (unclassified parameter or variable) | 113 | external/formbridge/src/formbridge/pattern_metadata.py:23 `def is_key(cls, key: Any) -> bool:`<br>external/formbridge/src/formbridge/protocols/component_selection.py:12 `def is_grouped(self, group_by: Any) -> bool:`<br>external/formbridge/src/formbridge/services/code_editor_form_updater.py:32 `new_instance: Any,` |
| record field with no stated type (DTO) | 47 | external/arraybridge/src/arraybridge/types.py:119 `capsule: Any`<br>external/formbridge/src/formbridge/forms/parameter_form_base.py:42 `color_scheme: Any | None = None`<br>external/formbridge/src/formbridge/managers/reorder_controller.py:16 `list_widget: Any` |
| registry or cache value (non-str key or named registry) | 46 | external/formbridge/src/formbridge/pattern_metadata.py:19 `def key_in(cls, values: Mapping[Any, Any]) -> bool:`<br>external/formbridge/src/formbridge/protocols/form_config.py:26 `custom_widget_factories: dict[type, Any] = field(default_factory=dict)`<br>external/formbridge/src/formbridge/services/service_registry.py:31 `_services: dict[type, Any] = {}` |
| genuinely any object (dunder protocol, equality, isinstance probe) | 40 | external/arraybridge/src/arraybridge/decorators.py:295 `self._streams: dict[tuple[MemoryType, int], Any] = {}`<br>external/formbridge/src/formbridge/managers/item_hooks.py:16 `def __call__(self, item: Any) -> str: ...`<br>external/formbridge/src/formbridge/managers/time_travel_binding.py:19 `def __init__(self, manager: Any, item_access: Any) -> None:` |

**Largest causes.** Arrays and JSON-like payloads are each about a quarter of the total
(712 and 703 of 2,882). **The single change that removes the most** is the nominal array
type above: it is one declaration in arraybridge and the uses are concentrated
(`arraybridge/array_operations.py`, `arraybridge/types.py`, `core/processing_contracts.py`,
`core/runtime_image_values.py`, `core/aligned_image_payload.py`). The JSON-like group
needs no new type: `python_introspect.JsonValue` and `JsonObject` exist, and each use
is either that or a record that should be a dataclass. Suggested cuts by owner: arraybridge
(array type), then `openhcs/core` runtime values, then DTO `to_dict`/`from_mapping` pairs
per package, then ObjectState and pyqt-reactive value plumbing (`TypeVar`).

## Gates

Run on `4c81f2b29` (origin/main `a51f4eab1` merged).

```
verify_branch.sh a1:
suite: = 15 failed, 11786 passed, 25 skipped, 350 warnings, 6 subtests passed in 1834.86s (0:30:34) =
collected 11825, reported 11801, crash lines 0
new vs known: 13
only on a1:
fails on both with a different error:

parity (test_official30_compile_execute_and_match_native_references_over_zmq, heavy slot + official30.lock):
1 passed in 1186.97s (0:19:46)

smoke_local.sh:
smoke pytest exit 0 (172 s): 7 passed, 2 warnings in 166.14s (0:02:46)
smoke gui exit 0 (55 s):
smoke rc=0

guardrails_local.sh:
ratchet openhcs exit 0
ratchet scripts exit 0
ratchet benchmark exit 0
38 passed, 22 warnings in 73.59s (0:01:13)
nra-r1 exit 0: "increased": []
base a51f4eab135b8b56f55f048391497fa62015b41d head 4c81f2b29646ab1ef1025e700f9dc0062c62e685 guardrails rc=0
```

A first smoke run reported `smoke rc=1` (3 failed): two source files were edited while
it ran, which invalidated the catalogue cache mid-run. The three tests pass alone and
the full rerun above is on the unchanged tree. The first parity invocation ran the whole
file; its napari and Fiji per-case viewer tests failed headless and were stopped, and
the parity test was rerun alone.
