# D1: Dead processing and interop code

**Head audited:** `openhcs` `main` at `0be261732` (#1152). **Rules:** [00-RULES.md](00-RULES.md). **Step 1.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* none.

## What is wrong

**Modules that the function registry never registers, a write-only format roster, and facade functions nobody calls sit in the product package (TIME-6, TIME-3, MEMB-1).**

- No importer and no memory decorator, so registry discovery never registers them:
  - `processing/backends/analysis/focus_analyzer.py` (346 lines).
  - `processing/backends/analysis/test_simple_implementation.py` (207). Its bare `from cell_counting_pyclesperanto_simple import …` cannot even resolve.
  - `processing/backends/analysis/cell_counting_pyclesperanto_simple.py` (328, undecorated).
  - `processing/backends/analysis/README_SIMPLE_IMPLEMENTATION.md`.
- `processing/backends/pos_gen/mist_processor_cupy.py` (130) says "Re-export for backward compatibility" and duplicates `mist/phase_correlation.py:101`.
- `MaterializationFormat` (`constants/constants.py:8`) and `WriterSpec.format` are never read. The enum appears only as `writer_for(..., MaterializationFormat.X)` arguments at 8 sites, while the options type is already the key (`_WRITERS_BY_OPTIONS`, `processing/materialization/core.py:2597`).
- `processing/func_registry.py` facades have 0–1 product callers: `get_function_info`, `get_function_by_name`, `get_all_function_names`, `get_valid_memory_types`, `get_functions_by_memory_type`. They are re-exported through `processing/__init__.py:13`, which also offers a third import path for the decorators (`:24`). The decorator also has four local aliases (`numpy_func`, `numpy_decorator`, `numpy_backend`, `numpy`).

## Target

Delete every item above. Callers of `writer_for` drop the format argument. The decorators have one import path. A facade that has one real caller is inlined at that caller.

## Guards

- A test that imports every module under `openhcs/processing` and asserts each defines a registered function, a family member, or is imported by a registered module. The check walks the registry; it is not a roster.
- `MaterializationFormat` does not exist (AST check).
- `processing/__init__.py` re-exports nothing from `func_registry`.

## Tests

Delete tests of deleted code. No new tests beyond the guards.

## Done when

All listed code is gone, the guards pass, the full suite and the 30-workflow parity check are green.

## Dispatch

> **`dead-processing`:** Complete surface D1 per `docs/refactor/consolidation-20261009/D1-dead-processing.md`. Done when every listed item is deleted and the guards pass. Re-verify each module's registration before deleting it.
