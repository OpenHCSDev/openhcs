# D2: Dead core and runtime code

**Head audited:** `openhcs` `main` at `0be261732` (#1152). **Rules:** [00-RULES.md](00-RULES.md). **Step 1.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* none.

## What is wrong

**Unused functions, fields, enum members and unreachable branches are spread through core and runtime (TIME-6, TIME-3).** Each item below was checked against `openhcs/`, `tests/`, `scripts/` and `benchmark/`, including uses by name in strings.

- `core/utils.py`: everything except `WellFilterProcessor`, about 330 lines. That covers the thread helpers (:22-275), `natural_sort` (:277-353) and `WellPatternConstants`.
- `core/metadata_cache.get_metadata_cache` (:117).
- `core/source_bindings.py`: `SourceRuntimePathLookup` and its two helpers (:2519-2564).
- `core/source_matching.metadata_source_text` (:314).
- About 15 measurement and equivalence symbols, roughly 176 lines. Examples: `measurement_feature_queries.py:1417, 1430, 1529`; `runtime_artifact_queries.py:224, 317`; `equivalence/cells.py:479, 489`.
- `core/function_contracts.py`:
  - `special_input_parameters_from_callable` has no callers.
  - `special_input_names_from_callable` is used only by the function above.
  - `image_payload_consumption_from_callable` and `runtime_bound_parameter_names_from_callable` are test-only.
  - The module-level `validate_artifact_input_parameter_bindings` is test-only and `del`s its `adapter_manages_inputs` argument.
- `core/artifact_planning.normalize_pattern`: test-only.
- `FuncStepContractValidator._resolve_relative_import`: the "old interface" branch (`pipeline/funcstep_contract_validator.py:281-311`) is unreachable, because its only caller (:265) always passes a level.
- `CompiledStepPlan.step_type` is written 3 times and never read.
- `ExecutionStatus.PENDING` is never constructed.
- The `special_outputs` alias is used only by 3 benchmark pipelines. Migrate them and delete the alias.
- `runtime/zmq_execution_observation._restore_legacy_axis_expectation` is a `getattr` default kept for archived payloads (TIME-2).
- `pyqt_gui` `image_browser.py:285` reads the orchestrator's `_metadata_cache_service` beside `orchestrator.metadata_cache`. Keep one.

## Target

Delete every item. Leave `core/function_patterns.py` alone; K5 owns it. `core/components/` belongs to D3.

## Guards

- The ratchet and NRA in CI already cover reintroduction.
- Add one AST test asserting that the deleted public names stay absent from `openhcs/`.

## Tests

Delete tests of deleted code, including the tests that were the only callers of the test-only helpers.

## Done when

Every listed item is gone, the full suite and the 30-workflow parity check are green, and the guard passes.

## Dispatch

> **`dead-core`:** Complete surface D2 per `docs/refactor/consolidation-20261009/D2-dead-core-runtime.md`. Done when every listed item is deleted. Do not edit `core/function_patterns.py` (K5) or `core/source_bindings_view.py` (C3).
