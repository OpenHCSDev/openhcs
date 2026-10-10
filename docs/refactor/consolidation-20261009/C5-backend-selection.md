# C5: CellProfiler and analysis backend selection

**Head audited:** `openhcs` `main` at `9a2550401` (#1163). **Rules:** [00-RULES.md](00-RULES.md). **Origin:** fork. **Step 2.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* the `AutoRegisterMeta` key extractor (exemplar `microscopes/microscope_base.py:184`).

## What is wrong

**Backend identity is declared twice per class and selection is implemented twice per family.**

- Two strategy families implement the same three methods. `AnalysisBackendStrategyMixin` (`processing/backends/analysis/region_properties.py:124`) and `CellProfilerBackendStrategyMixin` (`processing/backends/cellprofiler/_backend.py:279`) each own `for_memory_type`, `available_backend_providers` and `_resolve_backend_class`. Each has its own provider enum (`AnalysisBackendProvider` at `region_properties.py:87`, `CellProfilerBackendProvider` at `_backend.py:21`), and both enums contain `NUMBA`. Each has its own key function (`analysis_backend_key`, `CellProfilerBackendAuthority.backend_key`). Every consumer of the analysis family is a CellProfiler kernel (`object_images`, `shape`, `object_filtering`, `morphology`, `area_occupied`).
- `backend_key = <Authority>.backend_key(MemoryType.X, Provider.Y)` is restated in 52 classes (21 files) that also declare `memory_type = MemoryType.X` and `backend_provider = Provider.Y`. The key is a function of those two declarations.
- 24 family roots restate `__registry_key__ = "backend_key"` and `__skip_if_no_key__ = True` (three through the alias `THRESHOLD_BACKEND_REGISTRY_KEY`).
- `LegacyFastNumpyShapeMeasurementBackendStrategy` and `NumbaNumpyShapeMeasurementBackendStrategy` (`shape.py:1661`, `:1677`) have identical bodies; only the provider label and default flag differ.
- `ObjectSizeShapeFeatureMeasurement._feature_arrays_2d` (`shape.py:763`) flattens `DenseLabelRegionProperties` into skimage `regionprops_table` keys (`"bbox-1"`, `"centroid-0"`, `"moments-2-3"`) through `as_regionprops_table_subset` (`region_properties.py:232`, sole caller) and reads 19 scalar keys plus the advanced matrices back by string.
- `label_region_properties_backend` (`region_properties.py:476`) has no caller.

## Target

- **One strategy family, one provider vocabulary.** `CellProfilerBackendStrategyMixin` is the only selection mixin; `CellProfilerBackendProvider` gains `SKIMAGE`. `LabelRegionPropertiesBackendStrategy` joins the mixin, so its Numba provider is prepared at compile time like every other Numba backend (it implements `prepare_backend`).
- **Key derived from the declarations.** The mixin declares `__registry_key__ = "backend_key"`, `__skip_if_no_key__ = True` and `__key_extractor__`, which returns `CellProfilerBackendAuthority.backend_key(cls.memory_type, cls.backend_provider)` for a class declaring a memory type and rejects a second class claiming an existing key. Family roots declare only `metaclass=AutoRegisterMeta`.

```python
class SkimageNumpyLabelRegionPropertiesBackendStrategy(LabelRegionPropertiesBackendStrategy):
    memory_type = MemoryType.NUMPY
    backend_provider = CellProfilerBackendProvider.SKIMAGE
```

- **Twins collapsed.** One `NumbaNumpyShapeMeasurementBackendStrategy` (provider `NUMBA`, default). The shape `LEGACY_FAST` member is deleted.
- **Projection deleted.** `_feature_arrays_2d`, `_advanced_2d_features` read `DenseLabelRegionProperties` attributes directly.
- **Deleted:** `AnalysisBackendProvider`, `DEFAULT_ANALYSIS_BACKEND_PROVIDER`, `AnalysisBackendStrategyMixin`, `analysis_backend_key`, `_normalize_backend_provider`, the analysis `BackendProviderInput`/`BackendStrategyT`, `as_regionprops_table_subset`, `label_region_properties_backend`, `LegacyFastNumpyShapeMeasurementBackendStrategy`, `THRESHOLD_BACKEND_REGISTRY_KEY`, all 52 `backend_key =` assignments and the 24 per-root registry declarations.

## Persisted state

Saved pipelines that spelled `regionprops_backend_provider=AnalysisBackendProvider.…` or `shape_backend_provider=CellProfilerBackendProvider.LEGACY_FAST` explicitly fail loudly at load. The defaults are unchanged in meaning (Numba region properties; the Numba shape leaves), and `.cppipe` import emits only the module declaration's default. No converter (rule 2: our Python APIs change freely; no saved corpus in the tree spells either value).

## Guards

`tests/unit/test_backend_selection_guards.py`:
- no class body under `openhcs/` assigns `backend_key`;
- no family root declares `__registry_key__ = "backend_key"`;
- `AnalysisBackendProvider`, `AnalysisBackendStrategyMixin`, `analysis_backend_key` and `as_regionprops_table_subset` appear nowhere under `openhcs/`;
- no two registered backends in one family have identical method bodies (AST comparison of each class's own body minus `memory_type`/`backend_provider`/`is_default_backend`).

## Tests

- One family-level test: every registered backend in every family registers under `backend_key(memory_type, backend_provider)`, and exactly one default exists per memory type.
- One new-case test: declaring a backend with a memory type and provider registers it under the derived key; a second class claiming the same pair raises.
- The region-properties provider tests in `test_cellprofiler_processing_backend.py` move to `CellProfilerBackendProvider`.
- Gate: the 30-workflow Official30 parity check.

## New-case experiments

Today a new backend needs four declarations: `backend_key`, `memory_type`, `backend_provider`, `is_default_backend`, where the first restates the next two; a new family needs `__registry_key__` and `__skip_if_no_key__`; a new analysis primitive picks between two selection mixins and two provider enums. After: `memory_type` and `backend_provider` (plus `is_default_backend` when it is the default), and a new family is a subclass of the one mixin.

## Done when

The guards pass with zero exceptions; registry contents (family → key → class) are unchanged apart from the region-properties keys moving to the unified provider enum and the deleted shape twin; the Official30 parity check matches main's baseline.
