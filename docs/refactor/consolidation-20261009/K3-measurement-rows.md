# K3: Measurement dialect and rows

**Head audited:** `openhcs` `main` at `29b2ed6dc` (#1198). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.** G5 (#1188) took the dialect half of K3; this file records what it left.
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* `MeasurementDialect` (G5), `AutoRegisterMeta`.

## Already done (G5, verified at this head)

- **One dialect.** `RuntimeMeasurementLookupDialect` and `RuntimeMeasurementDialect` are gone. `MeasurementDialect` (`core/measurement_dialect.py:288`) is an `AutoRegisterMeta` ABC with one overridable `*_declaration(s)` method per former value/provider pair; `CellProfilerMeasurementDialect` and the per-module `CellProfilerModuleMeasurementDialect` (`interop/cellprofiler/measurement_dialect.py:93,233`) override them. No `dataclasses.replace` rebuild and no provider callables remain. The 23 value/provider pairs are now a declaration method plus a cached normalizing accessor each, which is a derivation, not a restatement.

## What is wrong

**The rows half of K3 is untouched, and a measurement bug sits in it: AreaShape values land on the wrong object when a declared label is empty (IDEN-1, IMPL-2).**

- **Wrong labels (scientific bug, B5).** Since 7ce29a1d2, `ShapeObjectFeatureValueTable.feature_array_domain` (`processing/backends/cellprofiler/shape.py:518`) gives every compact regionprops vector the `ROW_ORDINAL` domain: value *i* goes to the *i*-th *declared* id, not the *i*-th *measured* id. With declared ids (1, 2, 7), label 1 empty, label 1 gets label 2's area and label 2 gets label 7's. 3-D undeclared domains are compact on purpose too (`measurement_row_domain`, `shape.py:717-724`: `range(1, len(measured) + 1)`). This copies CellProfiler's own `MeasureObjectSizeShape` defect (`regionprops_table` output written by position). The sparse IJV path (`SparseIJVObjectSizeShapeMeasurement.object_row`) assigns by label, so the two representations disagree. `tests/unit/test_registered_object_output_boundaries.py` (2 cases) fails on main; `test_cellprofiler_shape_hotpath.py::test_sparse_shape_vectors_preserve_native_compact_and_label_domains` and `test_runtime_values.py` pin the wrong values.
- **The object-feature domain is an enum plus a strategy family restating it one-to-one.** `ObjectFeatureArrayDomain` (`core/runtime_measurements.py:1527`; MEASURED_OBJECT_ID, LABEL_ID, ROW_ORDINAL) with `ObjectFeatureArrayDomainStrategy` (`:1571-1668`, an `EnumKeyedStrategyMixin` per member), `ObjectFeatureMissingValue` (`:1535`) and two `ClassVar` side tables (`feature_array_domains`, `feature_missing_values`) that no production class sets. Once ROW_ORDINAL is gone, only "one value per measured id" is used anywhere.
- **Cell hashing is written twice and has drifted.** `measurement_table_cell_payload` and `update_measurement_table_cell_hash` (`core/equivalence/cells.py:198,235`) walk the same value tree separately: one checks mappings before arrays and the other arrays first, and they encode `None`, lists and mappings differently. The numeric rounding of `runtime_cell_signature` (`:174`) is a copy of `_runtime_numeric_cell_signature`.
- **The row qualifier vocabulary is split three ways.** `RuntimeMeasurementQualifierValueMode` (`core/measurement_dialect.py:76`) is an enum; its suffix parsing is an `EnumKeyedStrategyMixin` family (`:133-212`); its rendering is a dispatch table in `core/equivalence/measurement_rows.py:100-150` with a runtime check that the table covers the enum. `intensity_distribution.py:442` and `measurement_dialect.py:909,925` dispatch on the enum. The dialect reaches the renderers through a function-level import (`measurement_dialect.py:1025`) because they live in a comparison module.
- **`RuntimeMeasurementSourceNameEncoding`** (`measurement_dialect.py:47`; SEPARATE_KEY, FEATURE_SUFFIX) is an enum branched on at `measurement_dialect.py:766-772,972-979` and `equivalence/keys.py:235`, with a "unsupported encoding" `raise` that a family makes impossible.
- **`required_keys` is a `None`-mode** ("`None` means every key"): 19 `is None` / `is not None` sites in `core/equivalence/measurement_rows.py` and `measurement_facts.py`, plus 3 `required_key_index is not None` second modes in the cell projections (`measurement_rows.py:2020,2053,2118`).
- **Comparison tooling is still in the product package.** Production imports two functions from `core/equivalence/measurement_rows.py` (2,392 lines): `measurement_qualifier_field_names` (2 callers) and `measurement_row_qualifiers` (the dialect). Those two imports pull the whole module and `measurement_facts.py` (446) into production. Everything else in them (required keys, long-form facts, cell projections, sample-number offsets) serves only `benchmark/equivalence/` and tests. `core/equivalence/relationships.py` is mixed the same way: the aggregate-feature semantics are production, while `RuntimeScopedMeasurementTable`'s comparison methods and the `ObjectInstanceKeyPlaneAlignment*` strategies are used only by `benchmark/equivalence/`.

## Target

1. **Values stay on their labels.** `ObjectFeatureValueTable` maps a 1-D feature array by position in `measured_object_ids` and nothing else; a declared object with no value gets `missing_value(feature, object_id)` (NaN by default). `ShapeObjectFeatureValueTable` overrides that hook only (radius and Feret are 0 below the largest measured label, as CellProfiler sizes those vectors by label count) and validates the AreaShape vocabulary. The shape row domain is the declared ids, or `1..max(label)` when none are declared, in 2-D and 3-D alike.
   Deleted: `ObjectFeatureArrayDomain`, `ObjectFeatureMissingValue`, `ObjectFeatureArrayDomainContext`, the five `*FeatureArrayDomainStrategy` classes, `feature_array_domains`, `feature_missing_values`, `feature_value_index(es)`, `LabelIndexedShapeFeature`, `measurement_row_domain`.
2. **One cell walker.** `measurement_table_cell_payload` is the only walker. The container digest hashes its pickled payload. `update_measurement_table_cell_hash` is deleted, and `runtime_cell_signature` uses the shared numeric signature.
3. **Row vocabulary module** `core/measurement_row_qualifiers.py`. It holds the `RowQualifierFormat` family (`IdentifierFormat`, `TwoDigitIntegerFormat`, `FractionOfCountFormat`), each owning `render(values)`, `suffix_token_width(tokens, end)` and `distinctive`, plus `RuntimeMeasurementRowQualifier(field_names, value_format, feature_prefixes)`, the qualifier sequences and the defaults. The dialect answers `row_qualifier_field_names()` and `row_qualifier_suffixes(row, field_name)` from it.
   Deleted: `RuntimeMeasurementQualifierValueMode`, `RuntimeMeasurementQualifierSuffixMatchStrategy` and its three subclasses, `_MEASUREMENT_QUALIFIER_VALUE_RENDERERS` with its coverage check, the id-keyed field-name cache, and the function-level import.
4. **Source-name encoding family.** `SourceNameEncoding` with `SeparateKeySourceName` and `FeatureSuffixSourceName`, each owning how a source name binds to a feature (`source_qualified_feature_family`, encoding a key). Deleted: the enum, the branches and the unsupported-encoding `raise`.
5. **Required keys leave the product.** The `required_keys` `None`-mode lives only in the comparison projections. It moves with them to `benchmark/equivalence/` (item 6), which leaves 0 sites in `openhcs/`. Typing it there as an all-keys/selected-keys family is benchmark work and is not part of this surface. `benchmark/` is non-product code and the ratchet excludes it.
6. **Comparison tooling leaves the product.** Once production no longer imports `measurement_rows`, the modules production cannot reach move to `benchmark/equivalence/` (Q1), together with `measurement_facts.py` and the benchmark-only half of `relationships.py`. Production keeps `RuntimeScopedMeasurementTable` as a plain carrier.

## Guards

`tests/unit/test_measurement_rows_guards.py`:
- no `class … (… Enum)` named `*ValueMode`, `*SourceNameEncoding`, `ObjectFeatureArrayDomain` or `ObjectFeatureMissingValue` under `openhcs/`;
- `EnumKeyedStrategyMixin` is not used in `core/measurement_dialect.py`, `core/measurement_row_qualifiers.py` or `core/runtime_measurements.py`;
- no `required_key… is None` / `is not None` comparison anywhere in `openhcs/`;
- `cells.py` has exactly one recursive payload or hash walker (`measurement_table_cell_payload`);
- no module under `openhcs/` imports `openhcs.core.equivalence.measurement_rows` or `measurement_facts` (they no longer exist there).

## Tests

- **Family test (new):** `tests/unit/test_object_measurement_empty_labels.py` runs every object-measurement function that takes a label payload (AreaShape, intensity, texture, granularity, neighbours) on dense 2-D, dense 3-D and sparse IJV labels where it accepts them. For each, declaring an extra empty label must leave every other label's row exactly unchanged.
- Rewritten: the three shape-table tests in `test_runtime_values.py` and the hotpath sparse test now assert label-correct values; the cooperative-capability test in `test_registered_object_output_boundaries.py` no longer needs a domain enum.
- Deleted with their code: enum-member and strategy-registry assertions.
- Parity: official30 (baseline 30/30). `ExampleImagingFlowCytometryObjectsInGrid` has empty grid cells, so its native reference carries CellProfiler's positional AreaShape write: object 77 holds object 78's area, and so on. That reference is compared after `benchmark/equivalence/native_shape_rows.py` undoes the write. The undo is a permutation inside each image: objects with a finite `Location_Center_X` take the leading positions, and Feret and Zernike columns stay label-indexed. With it, all 55 AreaShape columns of that workflow equal OpenHCS's label-correct output exactly.

## New-case experiments

- A new qualifier format (for example "zero-padded three digits"). Today it needs an enum member, a suffix-strategy subclass, a renderer function and a dispatch-table entry, across two modules. After: one `RowQualifierFormat` subclass.
- A new object measurement that returns compact vectors. Today it must pick a domain enum member, or it inherits the wrong-label mapping. After: it passes `measured_object_ids`, and nothing else is possible.

## Done when

The guards pass. `test_registered_object_output_boundaries.py` passes in full. The empty-label family test passes. Official30 parity is 30/30. The structural ratchet and nra-r1 show no regressions.

## As built

- **Bug:** fixed as targeted. `test_registered_object_output_boundaries.py` passes in full (10/10). The new `tests/unit/test_object_measurement_empty_labels.py` covers AreaShape (dense 2-D, dense 3-D, sparse IJV), intensity (2-D, 3-D), texture, granularity and neighbours (2-D). For each, declaring an empty label leaves every other label's row exactly unchanged. On main the AreaShape cases fail; the others already held. Rewritten to label-correct values: `test_cellprofiler_shape_hotpath.py::test_sparse_shape_vectors_land_on_their_measured_labels`, two `test_cellprofiler_module_execution.py` shape tests and three `test_runtime_values.py` shape-table tests.
- **Native reference:** `benchmark/equivalence/native_shape_rows.py`, applied in `benchmark/adapters/openhcs.py` where the reference snapshot is read.
- **Row vocabulary:** `core/measurement_row_qualifiers.py`. `RowQualifierFormat` members are classes; a qualifier holds `value_format: type[RowQualifierFormat]`.
- **Moved to `benchmark/equivalence/`:** `measurement_rows.py`, `measurement_facts.py`, the plane-alignment strategies, and `RuntimeScopedMeasurementTable`'s comparison methods (now functions in `runtime.py`; its `object_instance_key` was forwarding and is deleted). The ratchet counts moved code as new, so the move also splits the wide-row methods out of `RuntimeRowProjectionContext` (718 lines) into a mixin, deletes a scalar copy of the cell payload (`measurement_qualifier_cache_value`), and rewrites 10 foreign absence probes.
- **Production** (Python under `openhcs/`): −3,804 +453. About 2.8k of the removed lines moved to `benchmark/`.
- **Not done here:** `CellProfilerSpatialGridMeasurementFeature` (`interop/cellprofiler/measurement_dialect.py:45`) is an enum used as a two-column spelling table for CellProfiler's DefinedGrid names. It is boundary vocabulary and has no behaviour to move, so it stays.
