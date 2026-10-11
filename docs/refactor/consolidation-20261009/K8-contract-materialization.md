# K8: Contract and materialization ownership

**Status:** the contract half landed with G5; the materialization half is blocked on E1 (#1203), which edits the same files. **Head audited:** `openhcs` `main` at `d597aa224` (#1205). **Rules:** [00-RULES.md](00-RULES.md).

## Already done (G5, verified at this head)

- `ProcessingContract` is an `AutoRegisterMeta` family in `openhcs/core/processing_contracts.py` (1,472 lines); members `Pure2DContract`, `Pure3DContract`, `FlexibleContract`, `VolumetricToSliceContract` own `execute`.
- The decorator takes the class (`core/memory/decorators.py:22-46`); no `declared_processing_contract`, `from_declared_name` or `ProcessingContract[...]` remains in `openhcs/`. The string spelling exists only at the function-cache boundary (`unified_registry.py:765` reads `ProcessingContract.for_key`, `:851` writes `.key`) and in error messages.
- Guards: `tests/unit/test_g5_processing_contract_guards.py`.

Nothing is left of the contract half.

## What remains

1. **Materialization lives in `processing` but is kernel code.** `openhcs/processing/materialization/` (5,834 lines; `core.py` 5,144) imports only `openhcs.core`, `polystore`, `zmqruntime` and `metaclass_registry`; nothing in `processing` beyond it. Seven core modules import it: `runtime_stores.py:50`, `runtime_execution_validation.py:30`, `pipeline/artifact_planning.py:45`, `runtime_exports.py:20,27`, `post_execute.py:33`, `pipeline/function_contracts.py:40`, `steps/function_artifact_materialization.py:53`. 97 files in `openhcs/`, `tests/`, `benchmark/` and `scripts/` import it, the package's own modules included. **Target:** move the package to `openhcs/core/materialization/`, update every importer, no re-export left behind.
2. **A third value-to-JSON switch.** `json_payload_value` (`processing/materialization/core.py:3015-3064`, a `singledispatch` over dict, `ColumnarRows`, list, tuple, `DataFrame`, `Series`, NumPy scalars and arrays) and its forwarding wrapper `JsonPayloadAuthority`. **Target:** python-introspect `to_jsonable`, with the measurement-row and columnar-row cases registered on it.
3. **`benchmark/validation/corpus.py:881` `_json_value`.** **Target:** `to_jsonable`.
4. **Dead computation (done in this PR).** `identify_secondary_objects` built `SecondaryObjectStats` (`processing/backends/cellprofiler/secondary.py:1277`) only to time it under the profiler key `iso_stats`, and never read it. The class had no other user.

## Blocked

Items 1 to 3 change files E1 (#1203, open) edits: `processing/materialization/{__init__,core,options}.py`, `benchmark/validation/corpus.py`, `core/pipeline/artifact_planning.py`, and 36 of the 97 importers. E1 also moves the `external/python-introspect` pointer, which item 2 builds on. They run after E1 merges.

## Reassigned

| Item | Evidence | Belongs to |
|---|---|---|
| `FileFormat` enum | lives in `openhcs/constants/constants.py` (E1 edits it), read by `pyqt_gui/widgets/image_browser.py:42-170` as a side table of `ResultFileAction`s; not in materialization | the UI surface owning `image_browser.py` (U-series), after E1 |
| Function registry imports from core (`function_reference.py:27,158,271,345`, `function_step_transport.py:157`, `funcstep_contract_validator.py:98`) | the third concept core reads from `processing`; not in K8's target | P2 (core packages) |

## Guards

After items 1 to 3: no `openhcs.processing.materialization` import anywhere; no `singledispatch` value-to-JSON function in `openhcs/` outside python-introspect (AST: a `@singledispatch` function whose registrations include `np.ndarray` and `dict`).

## Tests

`tests/unit/test_cellprofiler_identify_secondary_replacement_primary.py`, `test_cellprofiler_secondary_distance_backend.py`; the 30-workflow parity check.

## Done when

The materialization package is in `openhcs/core/`, nothing imports the old path, `json_payload_value`, `JsonPayloadAuthority` and `corpus._json_value` are gone in favour of `to_jsonable`, and parity is 30/30.
