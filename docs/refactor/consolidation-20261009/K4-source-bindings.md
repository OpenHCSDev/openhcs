# K4: Source bindings

**Head audited:** `openhcs` `main` at `29b2ed6dc` (#1198, L6 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* `AutoRegisterMeta`, python-introspect `RegisteredClassChoices`, ObjectState's `global_pipeline_config` decorator.

Re-measured at this head. None of K4 had landed: C3 and L4 moved the editor's table machinery to pyqt-reactive and deleted `core/source_bindings_view.py`; G4 added `DatasetSource` and moved the source-bindings source into `core/dataset_sources/`. All five items below are still present.

## What is wrong

**The source-binding config has two class identities, its absences and its pairing method are re-decided by each consumer, and five rules decide whether two source paths are the same path.**

1. **Two classes named `StepSourceBindingsConfig`.** `core/source_bindings.py:2196` defines it; `core/config.py:539-545` decorates it with `global_pipeline_config`, which rebuilds it with `None` defaults (`objectstate.lazy_factory.rebuild_with_none_defaults`) into a *different* class, then assigns the new class back onto the `source_bindings` module, and `config.py:930-933` re-exports both. `config.py:966` reassigns `source_bindings.EMPTY_SOURCE_BINDINGS`. A module that imports `source_bindings` before `config` keeps the old class and the old `EMPTY_SOURCE_BINDINGS` (verified: `import openhcs.core.source_bindings as sb; pre = sb.StepSourceBindingsConfig; import openhcs.core.config as c; pre is c.StepSourceBindingsConfig` is `False`). The rebuilt class does not subclass the old one, so `isinstance` against the stale name fails. `_SourceBindingPlanBase` carries a registry (`SourceBindingPlanMeta`, `registered_plan_types`, `concrete_registered_plan_type`) whose only job is to recover the concrete classes from entries the lazy classes overwrote; its one consumer is the editor's widget registration.
2. **Absence in three encodings.** A source-binding plan that selects nothing is `None` (`CompiledSourceBindingPlan.for_main_flow_scope` returns `None`; `compiler.py:1219,1254`, `function_execution.py:354,399,404`, `function_runtime.py:228` each test it), an empty instance (`CompiledSourceBindingPlan.empty()`, `CompiledSourceUniversePlan.empty()`, `EMPTY_SOURCE_BINDINGS`, `type(self)()` in `for_input_source`), or a predicate on a value (`is_empty`, written twice by hand at `source_bindings.py:1834` and `:2181` over different field lists). `function_runtime.py:228` converts the `None` back into an empty plan.
3. **`match_plan is None` read two ways.** `SourceSetAssembler.for_config` (`source_binding_workspace.py:257-262`) reads `None` as ORDER pairing; `SourceBoundAnchorPatternPolicy.for_plan` (`source_binding_selection.py:722-732`) reads it as "no pairing" and keeps every anchor, so a plan with two matched aliases and no declared method is paired by order at plate initialization and not collapsed at execution. `MetadataSourceSetAssembler` and `MetadataMatchedImageSetAnchorPatternPolicy` re-check `match_plan is None` as an error (`:309`, `:981`, `:1052`).
4. **Five path-identity rules.**
   - `str(Path(p))` (`source_path_identity.py:27-36`, `source_path_identity_key`, `source_paths_equal`), which keeps `..` components;
   - `Path.resolve()` equality (`NamedSourceBinding.physical_path_matches`, `source_bindings.py:1007`);
   - `resolve(strict=False)` for absolute path-like metadata (`source_metadata.py:661-695`, `normalized_path_metadata_value`, `path_metadata_values_equivalent`);
   - `as_posix()` spellings (`source_binding_selection.py:83-86`, `source_bindings.py:2037-2041`);
   - `str(path).replace("\\", "/")` (`source_binding_workspace.py:1471`).

   None of them agrees with pycodify 0.2, which saves absolute `Path` values factored and lexically normalized (`pycodify/paths.py:_lexically_normalized`): `Path('/data/screen/a/../b.tif')` saves as `path_root / 'b.tif'` and loads back as `/data/screen/b.tif`, which `str(Path())` calls a different path and `resolve()` calls different when `a` is a symlink.
5. **One enum dispatched twice.** `SourceBindingMatchMethod` is dispatched by `SourceSetAssembler` (`EnumKeyedStrategyMixin`), again by `SourceBoundAnchorPatternPolicy` through its string `.value` (`policy_key = SourceBindingMatchMethod.ORDER.value`), again by `SourceBindingMatchedImageSet.expand` (`is not SourceBindingMatchMethod.METADATA`, `:1226`), translated by `CellProfilerSourceMatchMethod` (`infrastructure.py:169`, an enum whose members carry the other enum's members) and offered by the editor's pairing row.

## Target

**Class identity.** `SourceBindingsConfig` and `StepSourceBindingsConfig` are declared in `core/config.py` beside every other `global_pipeline_config` section, decorated where they are defined, so each name has one class. `source_bindings_defaults_to_base` and `EMPTY_SOURCE_BINDINGS` move with them and are defined once. `core/source_bindings.py` keeps the declaration vocabulary (bindings, selectors, pairing, `SourceBindingDeclarationsMixin`, `_SourceBindingPlanBase`, the compiled plan) and never names the config classes. The config compiles itself (`StepSourceBindingsConfig.compiled_plan(...)`, `.compiled_plan_for_contracts(...)`), replacing `CompiledSourceBindingPlan.from_config`/`from_contracts` and their `isinstance` check. Deleted: the rebinding and monkeypatch (`config.py:531-545`, `:930-933`, `:966`), `SourceBindingPlanMeta`, `registry_key`, `registered_plan_types`, `concrete_registered_plan_type`. The editor registers its widget for `SourceBindingsConfig`; pyqt-reactive's catalog already matches subclasses and lazy types.

**Pairing is a family; absence is its default member.**

```python
@dataclass(frozen=True)
class SourceSetPairing(ABC, metaclass=AutoRegisterMeta):   # name: form and CellProfiler spelling
class PairByOrder(SourceSetPairing):     name = "order"
class PairByMetadata(SourceSetPairing):  name = "metadata"; dimensions: tuple[SourceBindingMatchDimension, ...]
```

`match_plan: SourceSetPairing = PairByOrder()`. `None` exists only as ObjectState's "inherit" on lazy configs and never reaches a consumer. The workspace assemblers and anchor policies are keyed by the pairing class (`NominalTypeKeyedStrategyMixin`), so absence has one meaning (order) and the `is None` checks go. `expand` asks `match_plan.dimensions` (order has none) instead of comparing enum members; `keyed_by(dimensions)` lets the editor and CellProfiler build a pairing without switching on its type. Behaviour change: a plan with two or more matched aliases and no declared method now has its execution anchors collapsed by order, as its source sets already were. Deleted: `SourceBindingMatchMethod`, `SourceBindingMatchPlan`, `SourceBindingMatchFields` (a one-method wrapper), `DefaultSourceBoundAnchorPatternPolicy`'s use as the `None` reading, `CellProfilerSourceMatchMethod` (CellProfiler's `Order`/`Metadata` literals decode through the family registry). The editor row's method column is `type[SourceSetPairing]` with `RegisteredClassChoices`.

**Typed absence for plans.** `for_main_flow_scope` returns the plan projected to no bindings, never `None`; the plan selects its own anchors (`select_anchors`, none when it binds nothing) and answers cross-group resolution itself. `CompiledSourceBindingPlan.empty()` and `CompiledSourceUniversePlan.empty()` are deleted (the empty value is `CompiledSourceBindingPlan()`). `is_empty` is written once, on `SourceBindingsConfig`, as "every field at its default" (it now also counts `source_spatial_domain`); compiled plans compare with `CompiledSourceBindingPlan()`.

**One path identity.** `core/source_path_identity.py` owns it: a source path's identity is its lexical normal form (`.` and `..` collapsed, no filesystem access), the rule pycodify 0.2 applies when it factors a saved path; its text spelling for filters is that form's POSIX spelling. `source_paths_equal`, metadata path normalization, candidate spellings and workspace spellings all use it. `physical_path_matches` locates the candidate file (`resolve`, as `resolve_source_file` locates the explicit one) and compares them with the same rule. Deleted: `path_metadata_values_equivalent` and its cache, `_normalized_source_path`, the private `as_posix` spellings.

## Persisted state

Saved `.py` pipelines and configs are durable. A file that names `SourceBindingMatchPlan` or `SourceBindingMatchMethod`, or imports the lazy source-binding configs from `openhcs.core.source_bindings` (generated files did), fails loudly on load; `match_plan=None` in a saved lazy config still means "inherit". **K4-Q1:** rewrite saved files that name the old pairing classes? Default: no tool, as G1-Q1 and G7-Q1 (no saved pipeline in the repository names them). The path rule changes no stored value.

## Guards

`tests/unit/test_k4_source_binding_guards.py`:
- `config.py` contains no assignment to an attribute of `source_bindings` and no rebinding of a name to a call of `global_pipeline_config` on another module's class; `source_bindings.py` defines no `SourceBindingsConfig`/`StepSourceBindingsConfig` and no `EMPTY_SOURCE_BINDINGS`.
- Importing `openhcs.core.source_bindings` alone, then `openhcs.core.config`, leaves one `StepSourceBindingsConfig` class (subprocess check).
- No `SourceBindingMatchMethod`, `SourceBindingMatchPlan`, `match_plan is None` / `is not None` under `openhcs/`.
- In the source modules (`core/source_*.py`, `core/runtime_source_binding_cache.py`), no `.resolve(` used in an `==`/`!=` comparison, no `as_posix()` outside `source_path_identity.py`, no `replace("\\", "/")`.
- Every pairing class has a workspace assembler and an anchor policy (registries are total over the family).

## Tests

- One path-identity test: paths with `.`/`..`/repeated separators saved through `pycodify.generate_python_source` (path factoring on) and loaded back compare equal to the originals under `source_paths_equal`, and each is equal to its own normal form.
- One pairing family test: for each pairing class, the workspace assembler and the anchor policy agree on the pairing of a two-alias universe; the default (no declared method) pairs by order in both.
- The existing source-binding, workspace, anchor, CellProfiler import and editor tests, updated to the family; the L6 round-trip test covers the moved config classes.

## New-case experiments

- A new pairing method (say, pair by acquisition time). Today: an enum member, an `EnumKeyedStrategyMixin` leaf, a string-keyed anchor policy, the `expand` branch, a `CellProfilerSourceMatchMethod` member and an editor choice: six edits in four modules. After: one `SourceSetPairing` subclass plus its two strategy leaves; the editor and CellProfiler decoding derive from the registry, and the totality guard names any missing leaf.
- A new path spelling (Windows UNC, URI-backed source). Today: decide which of five rules applies. After: one function.

## Found outside the brief

| Item | Evidence | Belongs to |
|---|---|---|
| Dataset and store identity still use `resolve(strict=False)` | `source_projection.py:243,259,439,479` (`SourceDatasetIdentity.for_root`, `SourcePlaneStoreIdentity.container_paths`, dataset aggregation), `dataset_sources/source.py:363-367`; fed by `microscopes/bioformats_adapter.py` | dataset sources (G4 follow-on) |
| Five more source-binding enums (rule 1a) | `SourceFilterMatchType`, `SourceFilterSubject` (restated 1:1 as strategy classes keyed by `.value` in `source_matching.py:160-270`), `MetadataSource`, `SourceSetRole`, `SourceProjectionRole` (an `EnumKeyedStrategyMixin` family in `source_binding_workspace.py` plus `is` checks in `source_projection.py`, `compiler.py`, `virtual_workspace_metadata.py`, `function_runtime.py`), `SourceBindingOrigin`; CellProfiler mirrors them in `infrastructure.py` (47 sites) | unassigned |

## Done when

The rebinding, the duplicated empties, the match-method enum and the `None` readings are gone; every source-path comparison goes through `source_path_identity`; the guards, the focused source-binding and CellProfiler suites and the 30-workflow parity check pass; the structural ratchet and nra-r1 show no regression.
