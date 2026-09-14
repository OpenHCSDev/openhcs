# Official30 reference-root and value-completion audit (2026-09-14)

## Scope and claim boundary

This is a dated extension and correction of the retained Official30 evidence. It
does not retroactively turn the historical 30-workflow summary into 30
reference-value comparisons. The historical cache contains five retained
successful-reference markers whose runner-selected output directories have no
CSV, SQLite, or image values. Those markers establish successful completion and
the selected-well strategy, but not the historical dependency versions or an
independent execution log. Benchmark-only exporters were appended to copies of
those five pipelines and rerun on one selected well per workflow.

The first current-source diagnostic suite produced one equivalent workflow out
of five and three equivalent artifacts out of eight. Those discrepancies exposed
five implementation errors in OpenHCS's CellProfiler compatibility operations.
After source-owned corrections and focused regression tests, an exact-commit
rerun produced five of five equivalent workflows and eight of eight equivalent
declared artifacts. Every final candidate observation records a matching
OpenHCS 0.8.5 client and a fresh isolated 0.8.5 execution endpoint. No original
pipeline setting or numeric tolerance was changed. This result completes a new,
dated five-workflow extension; it does not rewrite the historical Official30
summary or establish that its old empty output directories contained values.

## Environments and pinned inputs

The final candidate suite was `cp_vs_openhcs_20260914_adfbdc533`, executed on
2026-09-14 from the exact benchmark and processing source snapshot in OpenHCS
commit `adfbdc533`. It reused the same-day native CellProfiler exports generated
by suite `cp_vs_openhcs_20260914_122821`, then launched a fresh nonpersistent
execution server for each case on dedicated port 23850. Unrelated manuscript
edits and the separately scoped installer-timeout patch were dirty at execution
time but were not imported by this run. Per-observation provenance records the
benchmark-client interpreter and OpenHCS import path plus the endpoint PID,
create time, port, application version, and log path.

| Side | Runtime |
| --- | --- |
| Native | CellProfiler 4.2.8.1 and cellprofiler-core 4.2.8.1; Python 3.9.25; NumPy 1.24.4; SciPy 1.9.0 |
| Benchmark client | Editable OpenHCS 0.8.5 from `/home/ts/code/projects/openhcs`; Python 3.12.3; NumPy 2.1.3; SciPy 1.18.0 |
| Execution endpoints | Five fresh nonpersistent OpenHCS 0.8.5 processes on port 23850; PIDs, create times, executable/import paths, and log paths are persisted per observation |

Both ran on `Linux-7.1.5-arch1-2-x86_64-with-glibc2.44`. Native execution set
`NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4`. Dataset identities were:

- CellProfiler examples: `4972b59e670a4ae96c3d453803c92eeff378d054`
- CellProfiler4 benchmark supplement:
  `40abc2e600fd46b74c213999dd25c5245048dc92`
- CellProfiler tutorials: `264a8155da21a2d468051f78211bed2e580a8934`

The machine-readable environment receipt is
[`run_environment.json`](../../benchmark/results/official30_value_completion_20260914/committed_fixed_endpoint_run/run_environment.json).
These exact native dependency versions apply only to the new paired executions,
not to retained native outputs whose old markers did not record versions.

## Actual historical reference roots

The 30 retained references were re-audited through the same
`_native_reference_location` resolution and scope parameters used by the
comparison runner. The resulting partition is:

| Runner-selected reference class | Workflows |
| --- | ---: |
| Nonempty CSV | 21 |
| SQLite (with CPA properties) | 3 |
| NPY only | 1 |
| No CSV, SQLite, or image value | 5 |

The exact scope path, selected child reference path, included CSV/SQLite/CPA/image
paths, and image/CSV files outside the selected child are recorded for every
workflow in
[`reference_inventory.csv`](../../benchmark/results/official30_reference_root_audit_20260914/reference_inventory.csv).
There are 16 selected references containing images: 14 also contain CSV files,
one is NPY-only, and one contains SQLite plus a TIFF. Under the historical
`value_only: true` policy, CSV-plus-image references suppress image comparison.
Because `table_paths` recognizes CSV rather than SQLite, the NPY-only AllMethod
reference and the SQLite-plus-TIFF translocation-final reference enable image
comparison. The actual count is therefore **two**, not three.

The previously counted five advanced-segmentation illumination arrays are
inputs outside the selected reference child:

```text
native_cellprofiler_selected_source_workspace/_source/IllumER/20585_IllumER.npy
native_cellprofiler_selected_source_workspace/_source/IllumHoechst/20585_IllumHoechst.npy
native_cellprofiler_selected_source_workspace/_source/IllumMito/20585_IllumMito.npy
native_cellprofiler_selected_source_workspace/_source/IllumPh_golgi/20585_IllumPh_golgi.npy
native_cellprofiler_selected_source_workspace/_source/IllumSyto/20585_IllumSyto.npy
```

The selected native output child for
`cp_tutorial_advanced_segmentation_final` contains `BBBC022.db` and seven CPA
property files, but no image. Those five source arrays are consequently excluded
from runtime output equivalence.

## Benchmark-only export derivation

For each empty reference, the export plan is derived from the same parsed module
contracts and artifact graph used by `import_cellprofiler_pipeline`. It selects
supported processing outputs that are not consumed or replaced by a later
module. There is no workflow-name registry. The generated pipeline changes the
header `ModuleCount` and appends exporters; all original module text and settings
remain byte-for-byte unchanged.

Numeric images are saved as 32-bit NPY and compared with `atol=1e-6`,
`rtol=1e-6`, and zero permitted out-of-tolerance pixels. Object labels are
projected through CellProfiler `ConvertObjectsToImage` as uint16 TIFF and
compared as categorical label pixels by exact equality. The five sidecars under
[`benchmark/reference_exports/official30_value_completion_20260914`](../../benchmark/reference_exports/official30_value_completion_20260914/)
record source and generated SHA-256 hashes and the declared artifact inventory.

| Workflow | Derived terminal exports | Semantics |
| --- | --- | --- |
| `ExampleIlluminationCorrection_Example1_EachMethod` | `CorrGreen` | Numeric image pixels |
| `ExampleIlluminationCorrection_Example2` | `UncorrectedNuclei`, `SmallBlockCorrectedNuclei`, `LargeBlockCorrectedNuclei` | Categorical object labels |
| `ExampleIlluminationCorrection_Example3` | `PolynomialCorrected`, `ConvexHullCorrWorm` | Numeric image pixels |
| `cp4_supplement_combine_objects` | `CombinedObjects` | Categorical object labels |
| `cp_tutorial_translocation_start` | `Nuclei` | Categorical object labels |

The manifest explicitly sets `value_only: false`, so these images are actually
selected for comparison:
[`official30_value_completion_20260914.json`](../../benchmark/manifests/official30_value_completion_20260914.json).
The native success markers report image counts of 1, 3, 2, 1, and 1,
respectively. The runtime and receipt generator both validate the sidecar digest
against the exact generated pipeline, require exact native and candidate file
inventories, and dispatch comparison through the declared artifact semantic.
The only dimensional projection allowed is a 2-D categorical label image versus
the exact `(1, Y, X)` representation of the same single OpenHCS plane; arbitrary
singleton squeezing is rejected.

## Final exact-commit five-workflow result

Suite `cp_vs_openhcs_20260914_adfbdc533` reused the five same-day native
CellProfiler exports and freshly ran commit `adfbdc533` through five matching
0.8.5 endpoints. The authoritative file-level receipt is
[`artifact_comparisons.csv`](../../benchmark/results/official30_value_completion_20260914/committed_fixed_endpoint_run/artifact_comparisons.csv).

| Workflow / artifact | Contract result | Exact receipt |
| --- | --- | --- |
| EachMethod / `CorrGreen` | Pass | 0 of 262,144 pixels outside tolerance; max absolute difference 0 |
| Example2 / `UncorrectedNuclei` | Pass | Exact equality across 1,376,256 label pixels |
| Example2 / `SmallBlockCorrectedNuclei` | Pass | Exact equality across 1,376,256 label pixels |
| Example2 / `LargeBlockCorrectedNuclei` | Pass | Exact equality across 1,376,256 label pixels |
| Example3 / `PolynomialCorrected` | Pass | 0 of 213,443 pixels outside tolerance; max absolute difference 2.9802322387695312e-08 |
| Example3 / `ConvexHullCorrWorm` | Pass | 0 of 213,443 pixels outside tolerance; max absolute difference 0 |
| CombineObjects / `CombinedObjects` | Pass | Exact equality across 10,000 categorical pixels after the declared 2-D to single-plane-stack projection |
| Translocation-start / `Nuclei` | Pass | Exact equality across 409,600 label pixels |

Final aggregate: **5/5 equivalent workflows and 8/8 equivalent exported
artifacts**. Suite observations, summary, timing, exact candidate files,
endpoint logs, declaration-level comparison provenance, and decoded-pixel
digests are retained under
[`committed_fixed_endpoint_run`](../../benchmark/results/official30_value_completion_20260914/committed_fixed_endpoint_run/)
and the native exports under
[`benchmark/native_refs/official30_value_completion_20260914`](../../benchmark/native_refs/official30_value_completion_20260914/).
This demonstrates value equivalence for the new benchmark-only exports from the
five formerly empty workflows. Combined with the historical partition, it does
not license a claim that all 30 historical runs used these checks.

## Diagnosed compatibility discrepancies and corrections

The original current-source diagnostic suite
`cp_vs_openhcs_20260914_133100_current` is retained under
[`current_endpoint_run`](../../benchmark/results/official30_value_completion_20260914/current_endpoint_run/).
It reported one of five workflows and three of eight declared artifacts as
equivalent. The corrections were made in the existing declaration and backend
owners rather than in a workflow-name registry:

- `CombineObjects` merge had reduced the binary union to connected components.
  CellProfiler instead offsets incoming labels, preserves undisputed objects,
  assigns the disputed union to the nearest remaining initial object, then
  relabels the result. Implementing that policy made `CombinedObjects` exact.
- the Numba threshold backend's binned mode returned the center of the most
  populated bin. CellProfiler's Centrosome implementation returns the sample
  percentile associated with that bin. Correcting the primitive restored the
  translocation pipeline's Otsu threshold and foreground object.
- `ConvertObjectsToImage`'s uint16 mode returned `int32`. The subsequent image
  saver interpreted the `{0,1}` range as normalized intensity and wrote object
  label 1 as 65,535. The nominal uint16 renderer now validates and returns
  `uint16`, preserving categorical IDs.
- default labeled-hole filling handled only zero-valued background components.
  CellProfiler's foreground/background adjacency graph also treats a foreground
  object fully enclosed by another foreground label as a fillable labeled hole.
  Matching that graph removed the extra one-pixel Example2 object and the label
  renumbering cascade.
- defined-iteration shrinking used ordinary four-neighbor erosion. CellProfiler
  uses topology-preserving binary-shrink lookup tables for the declared number
  of iterations. Reusing the existing tables made the Example3 `ShrunkenWell`
  stage exact and restored both terminal correction images.

An augmented Example3 diagnostic exported nine intermediate images. Eight were
equivalent after the shrink correction. The remaining nonterminal
`PolynomialIllum` difference was confined to the masked-out domain:
`PolynomialCorrected`, the downstream consumed image, had zero pixels outside
`1e-6` and maximum absolute difference `2.9802322387695312e-08`. It is therefore
recorded as a masked-domain representation difference, not a terminal parity
failure. Its pipeline, exact native and candidate files, decoded-pixel receipt,
endpoint log, and explicit dirty-source limitation are retained under
[`example3_intermediate_diagnostic`](../../benchmark/results/official30_value_completion_20260914/example3_intermediate_diagnostic/).
This diagnostic localizes the difference; the terminal claim comes only from
the exact-commit final suite. Focused tests cover merge conflict assignment,
nested labeled-hole
filling, finite-iteration topology-preserving shrink, binned-mode selection,
uint16 rendering, exact export inventories, sidecar digest validation, and the
categorical single-plane contract.

## Superseded run that did not compare the exports

Suite `cp_vs_openhcs_20260914_121236` reported five equivalent cases, but it was
invalid as a value-comparison result. Its manifest still had `value_only: true`.
Because the native reference did not exist before the run, the pre-run reference
profile was empty and `compare_image_outputs` remained false. The exporters ran,
but their files were not compared. This suite is preserved, clearly segregated,
under
[`invalid_suppressed_image_run`](../../benchmark/results/official30_value_completion_20260914/invalid_suppressed_image_run/)
and is superseded by the current endpoint suite above.

## Superseded stale-endpoint run

Suite `cp_vs_openhcs_20260914_122821` freshly ran native CellProfiler for all
five workflows, but submitted candidate execution to a pre-existing persistent
OpenHCS 0.8.4 endpoint (PID 810643, started 2026-09-09) despite the benchmark
client importing editable OpenHCS 0.8.5. Its same numerical result is retained
only as a diagnostic under
[`stale_endpoint_run`](../../benchmark/results/official30_value_completion_20260914/stale_endpoint_run/).
It does not validate the current source checkout and is superseded by suite
`cp_vs_openhcs_20260914_adfbdc533` for every candidate claim.

## Refresh of the historical image cases

The actual selected-root audit leaves two historical image comparisons. Suite
`cp_vs_openhcs_20260914_133300_current_images` reran both candidates through
fresh matching OpenHCS 0.8.5 endpoints on dedicated port 23844.

- `cp_tutorial_translocation_final`: suite
  `cp_vs_openhcs_20260914_123020` freshly generated the CellProfiler 4.2.8.1
  reference, and the current image suite reused that same-day export with a
  fresh 0.8.5 candidate. The 640x640x3 uint8 overlay is raw-pixel identical:
  1,228,800
  compared pixels, zero outside tolerance, max absolute difference 0, and equal
  decoded-pixel digests. SQLite measurements and CPA properties also compared
  equivalent.
- `ExampleIlluminationCorrection_Example1_AllMethod`: fresh CellProfiler 4.2.8.1
  remained active until the declared 900-second timeout, so there is no new
  native/candidate pair. The current image suite instead compared a fresh
  OpenHCS 0.8.5 candidate against the retained native `Illum.npy`. The native
  512x512x3 grayscale-triplet array and candidate 512x512 array normalize to
  262,144 comparable pixels; zero are outside `1e-6`, with maximum absolute
  difference `2.384185791015625e-07`. The old native marker contains only the
  selected-well strategy, so its CellProfiler, Python, NumPy, and SciPy versions
  are irrecoverable and must not be inferred from the current environment.

The exact decoded-pixel receipts are in
[`image_comparisons.csv`](../../benchmark/results/official30_existing_image_refresh_20260914/current_endpoint_run/image_comparisons.csv).
The fresh observations, endpoint logs, retained candidate images, timeout trace,
current native markers, and superseded stale-endpoint suites are segregated
under
[`official30_existing_image_refresh_20260914`](../../benchmark/results/official30_existing_image_refresh_20260914/).
The fresh advanced-segmentation run also passed its SQLite/CPA comparison, but
its native marker records zero image outputs; it is not an image-pixel result.

## Reproduction commands

From the repository root, with the two project environments already prepared:

```bash
.venv/bin/python scripts/prepare_cellprofiler_reference_exports.py \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir benchmark/reference_exports/official30_value_completion_20260914 \
  --case ExampleIlluminationCorrection_Example1_EachMethod \
  --case ExampleIlluminationCorrection_Example2 \
  --case ExampleIlluminationCorrection_Example3 \
  --case cp4_supplement_combine_objects \
  --case cp_tutorial_translocation_start

OPENHCS_REFERENCE_EXPORT_PIPELINES_ROOT="$PWD/benchmark/reference_exports/official30_value_completion_20260914" \
NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 \
.venv/bin/python scripts/benchmark_cellprofiler_vs_openhcs.py run \
  --manifest benchmark/manifests/official30_value_completion_20260914.json \
  --native-reference-root benchmark/native_refs/official30_value_completion_20260914 \
  --require-native-reference \
  --output-dir <fresh-output-dir> \
  --suite-id <new-suite-id> \
  --openhcs-execution-port <unused-port> \
  --continue-on-error --no-memory-metric --no-figures

.venv/bin/python scripts/summarize_cellprofiler_reference_export_run.py \
  --run-root <fresh-output-dir> \
  --pipeline-root benchmark/reference_exports/official30_value_completion_20260914 \
  --output <fresh-output-dir>/artifact_comparisons.csv

.venv/bin/python scripts/summarize_cellprofiler_reference_inventory.py \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --native-reference-root benchmark/native_refs/official30_scoped_rows \
  --output <fresh-output-dir>/reference_inventory.csv
```
