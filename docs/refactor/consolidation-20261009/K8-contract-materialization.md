# K8: Contract and materialization ownership

**Head audited:** `openhcs` `main` at `d597aa224` (#1205), finished on `44980dfe2` (E1 #1203 merged). **Rules:** [00-RULES.md](00-RULES.md). The contract half is a closure note; the rest follows the receipt template.

## Already done (G5, verified at this head)

- `ProcessingContract` is an `AutoRegisterMeta` family in `openhcs/core/processing_contracts.py`; members `Pure2DContract`, `Pure3DContract`, `FlexibleContract`, `VolumetricToSliceContract` own `execute`.
- The decorator takes the class (`core/memory/decorators.py:22-46`); no `declared_processing_contract`, `from_declared_name` or `ProcessingContract[...]` remains in `openhcs/`. The string spelling exists only at the function-cache boundary (`unified_registry.py` reads `ProcessingContract.for_key`, writes `.key`) and in error messages.
- Guards: `tests/unit/test_g5_processing_contract_guards.py`.

Nothing was left of the contract half.

## What was wrong

**Kernel code lived in `processing`, one value-to-JSON answer was written three times, and result file kinds were an enum whose meaning was re-decided at three call sites (IDEN-4, IMPL-2, MEMB-2).**

1. **Materialization lived in `processing` but is kernel code.** `openhcs/processing/materialization/` (5,834 lines) imports only `openhcs.core`, `polystore`, `zmqruntime` and `metaclass_registry`. Seven core modules imported it (`runtime_stores.py`, `runtime_execution_validation.py`, `pipeline/artifact_planning.py`, `runtime_exports.py`, `post_execute.py`, `pipeline/function_contracts.py`, `steps/function_artifact_materialization.py`); 97 files in `openhcs/`, `tests/`, `benchmark/` and `scripts/` named it.
2. **A third value-to-JSON switch.** `json_payload_value` (`materialization/core.py`, a `singledispatch` over dict, `ColumnarRows`, list, tuple, `DataFrame`, `Series`, NumPy scalars and arrays) and its forwarding wrapper `JsonPayloadAuthority`.
3. **`benchmark/validation/corpus.py` `_json_value`**, a fourth.
4. **Dead computation.** `identify_secondary_objects` built `SecondaryObjectStats` (`processing/backends/cellprofiler/secondary.py`) only to time it under the profiler key `iso_stats`, and never read it. The class had no other user.
5. **`FileFormat(Enum)`** (`constants/constants.py`): ten members, four never referenced (`TORCH`, `JAX`, `CUPY`, `TENSORFLOW`). Its meaning was re-decided in `plate_image_inventory.py` (suffix matching by a hand-listed member tuple, ROI by `value[0]`; preview by `is ROI` / `in {CSV, JSON, TEXT}` / `is not CSV`; `streamable_roi_path` by `is ROI`) and in `pyqt_gui/widgets/image_browser.py` (a `RESULT_FILE_ACTIONS` side table of `ResultFileAction` records keyed by member, and `is ROI`).

## As built

- **Package move.** `openhcs/core/materialization/`; every importer updated; no re-export. Live docs (`docs/source/development/callable_artifact_authoring.rst`, the two `docs/audits` indexes) follow; archived plans and recorded paper supplements are left as written.
- **One encoder.** `render_json` calls `python_introspect.to_jsonable`. Joined by registration: `ColumnarRows` (in `core/runtime_tabular_values.py`, as row mappings), `pandas.DataFrame` and `Series` (in `materialization/core.py`); NumPy values through the existing `core/numpy_jsonable.py`. `corpus.py` calls `to_jsonable` directly. **Deleted:** `json_payload_value` and its eight registrations, `JsonPayloadAuthority`, `_json_value`.
- **`ResultFileFormat` family** (`core/result_file_formats.py`, registry key `name`, the spelling in metadata tables and agent DTOs): `TiffResultFile`, `NumpyResultFile`, `TextResultFile`, `JsonResultFile(TextResultFile)`, `CsvResultFile(TextResultFile)`, `RoiArchiveResultFile`. Each declares `suffixes`, and owns `names_path`, `preview(reader, record, …)` (none / text / table / ROI), `open_with(opener, path)` (default application / stream ROIs) and the capability `streams_rois`. `ResultFileFormat.for_suffix_of(path)` iterates the registry. The image browser implements `ResultFileOpener`. **Deleted:** the enum, its four unreferenced members, `RESULT_FILE_ACTIONS`, `ResultFileAction`, the two handler functions, the member tuple and membership set in the inventory, and two rows of E1's enum-dispatch table.
- **Secondary stats.** The computation, `SecondaryObjectStats` and the two imports only it used are deleted.

## Deletion certificates

| Deleted | Certificate |
|---|---|
| `SecondaryObjectStats` and its computation, profiler key `iso_stats` | **unused**: no reader in `openhcs/`, `tests/`, `benchmark/`, `scripts/`; its base has no registry |
| `FileFormat.TORCH/JAX/CUPY/TENSORFLOW` | **unused**: no reference in `openhcs/`, `tests/`, `scripts/` |
| `FileFormat` enum, `RESULT_FILE_ACTIONS`, `ResultFileAction`, inventory member tuples | **derived**: the `ResultFileFormat` registry; names, suffixes and per-kind behaviour are equal by `test_result_file_kinds_are_a_family` and the inventory tests |
| `openhcs.processing.materialization` (public import path) | **contract**: rule 1, no re-exports of moved names |
| `json_payload_value`, `JsonPayloadAuthority`, `_json_value` | **tests-only** for three inputs the old code admitted and tests do not exercise (below); otherwise **derived** from `to_jsonable` |

**Tests-only differences of `to_jsonable` against `json_payload_value`:**
- a mapping key that is `True`/`False`/`None` is now spelled `"True"`/`"False"`/`"None"` (`json.dumps` spelled it `true`/`false`/`null`);
- a value with no JSON form that is not a dataclass, enum, path, callable or registered class now raises in `to_jsonable` instead of in `json.dumps` (both raise `TypeError`);
- enums, paths, sets and family classes inside a JSON payload, which used to raise, now encode.

`PlateResultFileRecord.file_format` passed through `to_jsonable` is now the kind's name (`"CSV"`); as an enum it was the suffix list. I found no reader of that spelling.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Function registry cache, compiled plans | runtime | reset |
| Saved pipelines | durable | unchanged: they name functions through the catalog |
| **User custom functions that import `openhcs.processing.materialization`** | durable | **K8-Q1 (owner): no tool; such files fail loudly on import and are edited to `openhcs.core.materialization`.** Same default as G7-Q1 and K4-Q1 |

## Template-crop file naming (coordinator-assigned; accepted: tests were stale)

`tests/unit/test_template_crop_pipeline_execution.py` (16 cases) expected `images/A01_s001_w1_z001_t001_cropped_stack.tif`. Bisected (multi-plane case, 1,435 revisions from `bb76b5e44`): the first failing commit is `0dd77da46` (2026-10-03, "separate ordinary checkpoint and named artifact identities"), a deliberate rule in `core/steps/function_runtime.py` pinned by `test_function_runtime_source_projection.py::test_save_outputs_positional_lowering_preserves_explicit_payload_identity[unwrapped]`: a named image returned unwrapped keeps the source filename for its main-flow checkpoint, and the named artifact is materialized separately. `bb76b5e44` (#395, B5's bisect) changed only the singleton selection. The test now expects source names in `images/` and one `cropped_stack` file per channel in `results/`; the per-channel pixel assertion is unchanged. No production change.

With the owner (not changed here): `results/` slices are named by position (`…_slice_000.tif` is channel 2 when `target_channels=[1]`); the crop is written twice.

## Handoff

| Item | Evidence | Belongs to |
|---|---|---|
| `polystore.formats.FileFormat` is also an enum (`get_format_from_extension`, `is_pixel_payload`), a second roster of file kinds with different suffix sets | `external/PolyStore/src/polystore/formats.py`; read by `core/source_bindings.py:362` | a PolyStore library surface (L-series); `ResultFileFormat` could then derive its suffixes from it |
| Function registry imports from core (`function_reference.py`, `function_step_transport.py`) | the third concept core reads from `processing` | P (layout) |
| `test_official30_fiji_variants_project_registered_viewer_configs` fails with `NapariViewer has no attribute 'family'` | seen at `d597aa224` without the parity environment; not touched here | G6 |

## Guards

`tests/unit/test_k8_materialization_guards.py`:
- the old package directory is gone and no `.py` under `openhcs/`, `tests/`, `benchmark/`, `scripts/` names it;
- no `singledispatch` other than `to_jsonable` registers containers together with NumPy arrays and scalars; the three deleted converter names are not defined;
- no `FileFormat` class in `openhcs/`; the `ResultFileFormat` registry is exactly the six kinds, each found by its own suffixes.

## New-case experiment

A new result file kind (say `.parquet`): before, an enum member, an entry in the inventory's member tuple, a branch in the preview reader and a `RESULT_FILE_ACTIONS` record. After: one `ResultFileFormat` subclass.

## Done when

The package is in `openhcs/core/`, nothing names the old path, the three converters are gone, `FileFormat` is a family, the guards pass, parity is 30/30, and the ratchet and nra-r1 show no regression.

## Progress

- Done: all items above; touched tests; guards.
- Next: parity under flock on the final tree; ratchet and nra-r1; mark the PR ready.
