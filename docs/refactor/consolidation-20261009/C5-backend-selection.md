# C5: CellProfiler and analysis backend selection

**Head audited:** `openhcs` `main` at `9a2550401` (#1163); rebased onto `34abdf41e` (#1160). **Rules:** [00-RULES.md](00-RULES.md). **Origin:** fork. **Step 2.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* the `AutoRegisterMeta` key extractor (exemplar `microscopes/microscope_base.py:184`); rule 1a (families, not enums).

## What is wrong

**Backend identity is declared twice per class and selection is implemented twice per family.**

- Two strategy families implement the same three methods. `AnalysisBackendStrategyMixin` (`processing/backends/analysis/region_properties.py:124`) and `CellProfilerBackendStrategyMixin` (`processing/backends/cellprofiler/_backend.py:279`) each own `for_memory_type`, `available_backend_providers` and `_resolve_backend_class`. Each has its own provider enum (`AnalysisBackendProvider` at `region_properties.py:87`, `CellProfilerBackendProvider` at `_backend.py:21`), and both enums contain `NUMBA`. Each has its own key function (`analysis_backend_key`, `CellProfilerBackendAuthority.backend_key`). Every consumer of the analysis family is a CellProfiler kernel (`object_images`, `shape`, `object_filtering`, `morphology`, `area_occupied`).
- `backend_key = <Authority>.backend_key(MemoryType.X, Provider.Y)` is restated in 52 classes (21 files) that also declare `memory_type = MemoryType.X` and `backend_provider = Provider.Y`. The key is a function of those two declarations.
- 24 family roots restate `__registry_key__ = "backend_key"` and `__skip_if_no_key__ = True` (three through the alias `THRESHOLD_BACKEND_REGISTRY_KEY`).
- `LegacyFastNumpyShapeMeasurementBackendStrategy` and `NumbaNumpyShapeMeasurementBackendStrategy` (`shape.py:1661`, `:1677`) have identical bodies; only the provider label and default flag differ. The twin guard found a second pair: `CentrosomeNumpyConvexHullSmoothingBackendStrategy` and `NativeExactLevelSetNumpyConvexHullSmoothingBackendStrategy` (`illumination.py:1722`, `:1816`).
- Providers are a closed `str` enum (rule 1a). Behaviour attached to members lives outside them: `requires_compiler_prewarm` is an `is NUMBA` check on the enum, and explicit-provider resolution is a separate `ExplicitCellProfilerBackendProviderSelection` wrapper around a member, beside `DefaultCellProfilerBackendProviderSelection`. `CellProfilerBackendAuthority` is a forwarding layer of five classmethods (type checks and the key function).
- `ObjectSizeShapeFeatureMeasurement._feature_arrays_2d` (`shape.py:763`) flattens `DenseLabelRegionProperties` into skimage `regionprops_table` keys (`"bbox-1"`, `"centroid-0"`, `"moments-2-3"`) through `as_regionprops_table_subset` (`region_properties.py:232`, sole caller) and reads 19 scalar keys plus the advanced matrices back by string.
- `label_region_properties_backend` (`region_properties.py:476`) has no caller.

## Target

- **One provider family.** `CellProfilerBackendSelection` (`AutoRegisterMeta`, names derived from class names) has two kinds of member, both used as values: `DefaultBackendSelection` and the `BackendProvider` subfamily (`NativeBackendProvider`, `NumbaBackendProvider`, `CppBackendProvider`, `CentrosomeBackendProvider`, `OpencvBackendProvider`, `LegacyFastBackendProvider`, `CucimBackendProvider`, `PyclesperantoBackendProvider`, `SkimageBackendProvider`). Each member owns `backend_class(snapshot)`, `provider_or(default)` and `semantic_identity()`; a provider owns `backend_key(memory_type)` and `requires_compiler_prewarm`. Kernel code passes and declares provider classes.
- **The enum is a derived boundary view.** `CellProfilerBackendProvider` stays as the choice list for function signatures, forms, MCP schemas and generated pipelines, built from the family registry; each member's `.provider` is its class. `CellProfilerBackendSelection.from_input` is the one place a choice becomes a class.
- **One strategy family.** `CellProfilerBackendStrategyMixin` is the only selection mixin; `LabelRegionPropertiesBackendStrategy` joins it, so its Numba provider is prepared at compile time like every other Numba backend.
- **Key derived from the declarations.** The mixin declares `__registry_key__`, `__skip_if_no_key__` and `__key_extractor__`; the extractor returns `backend_provider.backend_key(memory_type)` and rejects a second class claiming an existing key. Each subclass's key is re-derived (an inherited key is cleared), so a subclass of a concrete backend registers under its own declarations.

```python
class SkimageNumpyLabelRegionPropertiesBackendStrategy(LabelRegionPropertiesBackendStrategy):
    memory_type = MemoryType.NUMPY
    backend_provider = SkimageBackendProvider
```

- **Twins collapsed.** One `NumbaNumpyShapeMeasurementBackendStrategy` (the former mixin, now the default). The Centrosome convex-hull twin is deleted; Native is the default and runs the same code.
- **Projection deleted.** `_feature_arrays_2d` and `_advanced_2d_features` read `DenseLabelRegionProperties` attributes directly.
- **Deleted:** `AnalysisBackendProvider`, `DEFAULT_ANALYSIS_BACKEND_PROVIDER`, `AnalysisBackendStrategyMixin`, `analysis_backend_key`, `_normalize_backend_provider`, `as_regionprops_table_subset`, `label_region_properties_backend`, the hand-written `CellProfilerBackendProvider` enum, `CellProfilerBackendAuthority`, `CellProfilerBackendProviderSelection`, `DefaultCellProfilerBackendProviderSelection`, `ExplicitCellProfilerBackendProviderSelection`, `DEFAULT_CELLPROFILER_BACKEND_PROVIDER`, `LegacyFastNumpyShapeMeasurementBackendStrategy`, `NumbaShapeMeasurementMixin`, `CentrosomeNumpyConvexHullSmoothingBackendStrategy`, `THRESHOLD_BACKEND_REGISTRY_KEY`, all 52 `backend_key =` assignments and the 24 per-root registry declarations.

## Persisted state

The choice list keeps its import path and member spellings, so saved pipelines that name a provider still load. Those that spelled `regionprops_backend_provider=AnalysisBackendProvider.…`, `shape_backend_provider=CellProfilerBackendProvider.LEGACY_FAST` or `convex_hull_backend_provider=CellProfilerBackendProvider.CENTROSOME` explicitly fail loudly. The defaults are unchanged in meaning (Numba region properties; the Numba shape leaves), and `.cppipe` import emits only the module declaration's default. No converter (rule 2: our Python APIs change freely; no saved corpus in the tree spells either value).

## Guards

`tests/unit/test_backend_selection_guards.py`:
- no class body under `openhcs/` assigns `backend_key` or declares `__registry_key__ = "backend_key"` (outside `_backend.py`);
- no backend declares `backend_provider = CellProfilerBackendProvider.<member>` (backends declare provider classes);
- `CellProfilerBackendProvider` is not a hand-written class;
- `AnalysisBackendProvider`, `AnalysisBackendStrategyMixin`, `analysis_backend_key`, `as_regionprops_table_subset`, `CellProfilerBackendAuthority` and the shape twin appear nowhere under `openhcs/`.

`tests/unit/test_cellprofiler_backend_selection.py::test_no_two_backends_in_a_family_are_twins`: no two registered backends in one family have the same bases and body once their declarations are removed.

## Tests

- One family-level test: every registered backend in every family registers under `backend_key(memory_type, backend_provider)`, and exactly one default exists per memory type.
- One new-case test: declaring a backend with a memory type and provider registers it under the derived key; a second class claiming the same pair raises.
- One test that the choice list is derived from the family and that choices, classes and `None` resolve through `from_input`.
- The region-properties provider tests in `test_cellprofiler_processing_backend.py` move to `CellProfilerBackendProvider`; the per-family Numba prewarm test iterates registries.
- Gate: the 30-workflow Official30 parity check.

## New-case experiments

Today a new backend needs four declarations: `backend_key`, `memory_type`, `backend_provider`, `is_default_backend`, where the first restates the next two; a new family needs `__registry_key__` and `__skip_if_no_key__`; a new analysis primitive picks between two selection mixins and two provider enums. After: `memory_type` and `backend_provider` (plus `is_default_backend` when it is the default), and a new family is a subclass of the one mixin.

## Done when

The guards pass with zero exceptions; registry contents (family → key → class) are unchanged apart from the two deleted twins, the shape default moving to the surviving Numba backend, and region properties joining the family under the same keys; the Official30 parity check matches main's baseline.

## Out of scope, recorded for owners

- `MemoryType` (`constants/constants.py`) is a closed enum that backends key on; its owner is L5 (arraybridge memory namespace).
- The `LegacyFast…` provider and `LegacyWatershedBackendStrategy` names violate the no-`legacy` naming rule; renaming the `legacy_fast` choice changes a user-visible value in saved pipelines. Decision for the owner: rename the provider and choice (for example `ApproximateBackendProvider`, `approximate`) as a hard cutover of saved pipelines that name it.
