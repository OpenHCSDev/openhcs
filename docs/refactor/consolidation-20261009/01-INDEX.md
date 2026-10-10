# OpenHCS consolidation index

**Head:** `0be261732` (#1152). **Rules:** [00-RULES.md](00-RULES.md).

Surface files are written one at a time against the head of the day; re-verify yours before editing.

## Evidence

Measured with Python 3.12 (repo `.venv`); every parse succeeded. Production means Python under `openhcs/`.

| Measure | Whole tree at head | Added since `902913616` (2026-10-02) |
|---|---|---|
| Code lines | 368,625 | +12,019 |
| Headline debt per 1,000 lines (type identity checks + long boolean chains + string-key subscripts) | 3.7 | 6.7 |
| `is None` / `is not None` per 1,000 lines | 19.3 | 37.1 |
| Foreign absence probes per 1,000 lines | 4.0 | 7.5 |
| Raw dict shapes read by key while a class models the record | 163 | |
| God classes / god functions | 71 / 261 | |

Structure:
- `openhcs/core` has 112 flat root modules: 30 `runtime_*` (21k lines), 14 `source_*` (15k), `measurement_*` (5k).
- Module-level imports in core are acyclic. 201 function-level imports, 85 of them in `artifacts.py`, close cycles across 107 of 176 core modules. 122 more are `TYPE_CHECKING` imports, which are fine.
- `processing` imports `interop` 368 times (all from `processing/backends/cellprofiler`). `core` imports `processing` 15 times, for three concepts: `ProcessingContract`, materialization specs and the function registry.

Most new debt is modes encoded as absence: an `Optional` field whose `None` selects one behaviour and whose value selects another, re-decided at every consumer (for example `artifact_graph is None` at `core/function_patterns.py:939`, `plane_index is None` at 43 sites, `required_keys is None` at 25 sites). Code added during the agent burst of 2026-10-02 to 2026-10-08 (2,366 commits) carries it at twice the tree's density. The model to follow is `ccfef5f6d` in #60: semantics moved onto their owners and the parallel layers deleted, net −11.6k production lines.

## Surfaces

Estimates are net production lines. "Out" means moved out of `openhcs/` into non-product tooling.

| ID | Surface | Evidence | Target | Est. |
|---|---|---|---|---|
| [D1](D1-dead-processing.md) | Dead processing and interop code | `analysis/focus_analyzer.py` 346, `test_simple_implementation.py` 207, `cell_counting_pyclesperanto_simple.py` 328, `pos_gen/mist_processor_cupy.py` 130 (no importer, no decorator, so never registered); write-only `MaterializationFormat` roster; `func_registry` facades with 0-1 callers | deleted | −1.2k |
| [D2](D2-dead-core-runtime.md) | Dead core and runtime code | `core/utils.py` except `WellFilterProcessor` (~330); test-only `function_contracts` helpers; unreachable validator branch; `CompiledStepPlan.step_type` never read; `ExecutionStatus.PENDING` never built; ~15 measurement/equivalence symbols | deleted | −1.0k |
| [D3](D3-product-boundary.md) | Research tools and vestigial packages | `agent/blind_recipe_audit.py`, `mcp/recorded_evidence.py`, `mcp/memory_diagnostic*.py` used only by tests and scripts; `validation/` (628) no product importer; `introspection/` re-export shim; `components/framework.py` "moved" split; `MultiprocessingCoordinator` (140, only re-exported); `utils/pipeline_migration.py` (508) legacy pickle migration | deleted or moved to `scripts/` | −2.1k |
| [D4](D4-equivalence-tooling.md) | Equivalence tooling out of core | `core/runtime_equivalence.py` (3,300) and `core/equivalence/` (11.2k) mix two roles: 18 production modules on the CellProfiler measurement path import `policy`, `keys`, `cells`, `relationships`, `measurement_features`, while comparison and report code serves only `benchmark/` and tests | modules production cannot reach move to `benchmark/equivalence/`; the rest stays for K3 | ≤ −6k out |
| [D5](D5-validation-logs.md) | Committed validation logs | `docs/validation` is 160 MB, 1,137 files | delete files nothing in `paper/` or `docs/` links to | non-code |
| C1 | Capability invocation family | 7 nullable `*_invocation` slots (`agent/capabilities.py:1313`); 11 near-copy `generated_*_capability_declarations` (`mcp/server.py:591…`); 21-field `to_spec` copy | one `invocation` field; each invocation class owns execute, MCP binding, CLI arguments | −1.0k |
| C2 | MCP CLI renderers | 42 renderers read result dicts by key (784 reads) while declaring `output_contract`; typed base used by 23 | every renderer on `McpDevTypedOutputRenderer`; `McpDevPayloadProjection` deleted | −1.2k |
| C3 | Source-binding editor | `pyqt_gui/widgets/source_bindings_editor.py` (3,554) restates `NamedSourceBinding` as 11 text columns and **drops `explicit_source` and `load_as_monochrome` on save** (`bindings()` at :1448); `core/source_bindings_view.py` 9 `*View` string mirrors | columns derived from the dataclass through pyqt-reactive; table infrastructure upstream; view mirrors deleted | −1.8k |
| C4 | Per-backend algorithm copies | `processing/processors/{numpy,cupy,torch,jax,tensorflow,pyclesperanto}_processor.py` define 15 shared names 78 times | one array-namespace implementation, per-backend overrides only where semantics differ | −3.0k |
| C5 | CellProfiler backend selection | two strategy families with the same three methods (`analysis/region_properties.py:124`, `cellprofiler/_backend.py:279`); `backend_key` restated in 52 classes; identical twin backends `shape.py:1661/1677`; `shape.py:763` flattens `DenseLabelRegionProperties` to skimage keys and reads 19 back | one strategy family; key derived by `__key_extractor__`; attributes read directly | −0.3k |
| C6 | Progress events | field list written six times, already drifted (`core/progress/types.py:514-710`); every event dict-encoded 2-3 times in process; untyped `context` bag probed by key in 3 consumers | one dataclass-derived codec; `ProgressContextPayload` family | −0.2k |
| C7 | Viewer control actions | `NapariControlMessageAction` and `FijiControlMessagePlan` restate shutdown, clear-state, launch, settle; Fiji answers unknown messages with SUCCESS, Napari with ERROR | viewer-neutral action base with per-viewer mixins | −0.4k |
| K1 | Image payloads and plane modes | bare-array vs carrier switch restated at 513 call sites (`runtime_image_values.py:1508-1533`); 4-type switch `aligned_image_payload.py:1950`; `plane_index None` 43 sites, `plane_axis None` 66 sites; two slice-projection mechanisms; triple dispatch in `steps/function_runtime.py:1069,1196,1235` | payload family owns data, metadata, mask, alignment and slice mapping; plane modes are types | −0.8k |
| K2 | Artifacts | `artifacts.py` (4,190) fuses payload base, kind family and planning; 14 `isinstance` checks on owned value types; slice loop hand-written 31 times; `output_plan None` | `core/artifacts/` package; kinds call payload methods | −0.4k |
| K3 | Measurement dialect and rows | dialect split over two classes fed the same providers; 23 value/provider pairs; `required_keys None` 25 sites; cell hashing written twice and drifted | one dialect ABC, CellProfiler subclass; row vocabulary module | −0.6k |
| K4 | Source bindings | `config.py:744` rebinds `StepSourceBindingsConfig` to a different class; absence in three encodings; `match_plan None` read two ways; five path-identity equality rules; one enum dispatched twice | one class identity; typed absence; one path identity | −0.4k |
| K5 | Callable contract and patterns | `CallableMetadata` 13 Optionals, one fact stored twice, fields restated three times; five raw pattern walkers beside `NormalizedFunctionPattern`; test-only `artifact_graph=None` mode used by 213 tests | declaration/invocation split; one pattern authority; test-only mode deleted with its tests | −0.6k |
| K6 | Debug views | one value-to-JSON/cell-text switch written three times (`debug_view_models.py:409`, `debug_views.py:240`, `serialization/json.py:38`); snapshot record shape written four times | `to_jsonable` and `DebugJsonCodec` only | −0.3k |
| K7 | Execution protocol | `ComponentGroupScope` packs three variants into two fields (57 predicate uses); `ProcessingContext` mixes compile and execution state; worker lanes dispatch tuple commands on strings with two receivers; `ExecutionResult` longhand union | variant types; `Compiling`/`Compiled` contexts; typed lane messages | −0.5k |
| K8 | Contract and materialization ownership | `ProcessingContract` crosses the decorator as a name string and is re-decided over three encodings; materialization types live in `processing` but core imports them in 7 modules | contract family and materialization specs owned by core | −0.2k |
| P1 | CellProfiler module placement | 91 leaf declarations live in `processing/backends/cellprofiler` beside kernels; `__init__` swaps the module class to list itself | declarations in `interop/cellprofiler/modules`, kernels in processing | −0.1k |
| P2 | Core packages | 112 flat modules | `core/{artifacts,runtime,image_payload,object_labels,measurements,source,callables,debug,config}` per the layering source → runtime values → payloads/labels/measurements → artifact kinds → callables; wire contracts out of `agent/` into a contracts package | relocation |

Total: about −16k production lines removed from `openhcs/`, plus up to −6k of verification tooling moved out (D4 measures the exact set).

## Order

| Step | In parallel | Why |
|---|---|---|
| 1 | D1, D2, D3, D4, D5 | Pure deletion, disjoint files, no shared abstraction. Shrinks every later surface. |
| 2 | C1 then C2 (same package); C3; C4; C5; C6; C7 | Disjoint packages. C3 also fixes a live data-loss bug. |
| 3 | K1, then K2 and K5 (both consume payload methods); K3, K4, K6, K7, K8 in parallel with K1 | Core identity rung. K1 builds A1. |
| 4 | P1, P2 | Relocation last, after the other surfaces have shrunk the modules being moved. |

## Crossings

| Shared thing | Resolved by |
|---|---|
| `core/source_bindings_view.py` | C3 owns it (deletes the view mirrors); K4 does not touch it |
| `steps/function_runtime.py` payload dispatch | K1 owns the three switches; K7 touches only lane and context code |
| `core/function_patterns.py` | K5 owns it; D2 leaves its symbols alone |
| `mcp/server.py` vs `mcp/dev_client_renderers/` | C1 owns server.py and dev_client_commanding.py; C2 owns renderers and dev_client_rendering.py; C1 merges first |
| `core/equivalence/` modules reachable from production | K3 owns them; D4 moves only what production cannot reach |
| `config.py` source-binding rebinding | K4 |
| `core/components/` | D3 |

## Decisions

| ID | Question | Default |
|---|---|---|
| Q1 | Where does equivalence tooling go? | `benchmark/equivalence/`, beside its consumers |
| Q2 | Per-backend dedupe (C4) may change results at floating-point level? | No: each backend keeps exact parity with its current tests; a backend that cannot is kept as an override |
| Q3 | Delete the GroupBy pickle migration (old saved pipelines then fail loudly)? | Yes |
| Q4 | Delete validation logs under `docs/validation` that nothing links to? | Yes |
| Q5 | `omero/` (a separate Django plugin) | Out of scope |

## Surface files

Written just in time:
- [D1-dead-processing.md](D1-dead-processing.md)
- [D2-dead-core-runtime.md](D2-dead-core-runtime.md)
- [D3-product-boundary.md](D3-product-boundary.md)
- [D4-equivalence-tooling.md](D4-equivalence-tooling.md)
- [D5-validation-logs.md](D5-validation-logs.md)

## Revised plan after the genericity audits (2026-10-10)

The owner set the direction: OpenHCS is a domain-blind tensor dataflow kernel, microscopy is one domain, and every hardcoded domain member is slop to be derived from the declared axis family. [04-ARCHITECTURE.md](04-ARCHITECTURE.md) gives the target and its evidence. This section replaces steps 2 to 4 above. Step 1 (D1 to D5) is unchanged.

| ID | Surface | Replaces | Depends on |
|---|---|---|---|
| G1 | Axis family: `Axis`/`AxisFamily`/roles with cardinality; the microscopy family declared in the domain package; enums and config as derived views; per-call enum construction deleted | none | none |
| G2 | Member references derived: every `AllComponents.<MEMBER>` and per-member field, strategy or roster in kernel modules asks the family by role (`function_io` strategies, `config.py` viewer mode fields, source projections, analysis consolidation, `required_variable_components`) | parts of K4, K7 | G1 |
| G3 | Tensor payload with declared axes; N-d spatial domain; one boundary wrap | K1 | G1 |
| G4 | `DatasetSource` protocol; kernel `SourcePlaneStoreAdapter`; openhcsdata format derived from declared axes; domain post-execute hooks | K4 | G1 |
| G5 | Processing contract family owns execute; role-declared function requirements; measurement dialect ABC with the CellProfiler instance in interop | K3, K8 | G1 |
| G6 | Viewers take declared axes; slot families; one control family (fixes Fiji answering SUCCESS to unknown messages); `ViewerFamily` | C7 | G1 |
| G7 | Runtime vocabulary and protocol: partition, dataset and axis values; typed worker IPC; lane identity derived | K7, C6 | G1, L3 |
| G8 | Taken over by U1 (04-ARCHITECTURE.md, The UI) | none | none |
| L1–L7 | First-party library moves (04-ARCHITECTURE.md, First-party libraries) | C4 → L5 | in the listed order |
| C1, C2, C3, C5, K2, K5, K6 | Unchanged from the table above. K6 uses L2's codec; C3 hands its table to L4 | | |
| W | Witness: a non-microscopy family runs end to end in CI with zero kernel edits; a ratchet on domain member references in kernel modules | none | G1–G7 |
| P | Layout: `openhcs/kernel`, `openhcs/authoring`, `openhcs/domains/{microscopy,cellprofiler}`; CI guard that the kernel imports no domain code; then the kernel splits into its own distribution (04-ARCHITECTURE.md, End state) | P1, P2 | last |

Order:

| Step | In parallel |
|---|---|
| 2 | G1; L1; L2; C1 then C2; C3; C5 |
| 3 | G2; G3; G4; G5; G6; L3; L4; K6 |
| 4 | G7; G8; L5; L6; K2; K5 |
| 5 | L7 (`streamviewer`); W; P |
