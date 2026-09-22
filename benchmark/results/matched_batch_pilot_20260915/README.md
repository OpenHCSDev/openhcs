# Matched-batch experiment handoff

Status: native warm-batch timing works; the eight-well production probe found
two correctness gaps and an output-policy mismatch. No matched speedup or
Supplementary Figure 6 replacement is produced.

## Observations

- Native CellProfiler completed one warm-up and three repeated batches of eight
  genuine image assignments. Invocation durations were 19.2508, 17.1796 and
  18.8893 seconds; first-module-through-post-run durations were 18.8870, 16.9119
  and 18.6581 seconds. These are native-only observations.
- Production OpenHCS 0.8.5 executed all eight axes successfully in its own TCP
  ZMQ server, with `num_workers=1`. Its first batch stopped the pilot at strict
  observation validation, before any candidate repeat was accepted.
- Eight requested TIFFs compare pixel-exactly. Native and candidate databases
  both contain eight image rows, with identical object counts per image.
- The retained SQLite comparison reports four differences: three cytoplasm
  correlation mean features and the corresponding object-table values.

## Concrete repairs before continuing

1. Preserve execution scope in runtime artifact expectations. The compiler
   declares SQLite/CPA as a plate-scoped artifact, produced once by its owner;
   `RuntimeArtifactExecutionExpectation.from_compiled_contexts` collapses outputs
   to a flat kind set, and `_runtime_artifact_failures` requires that kind on each
   axis. Seven axes consequently fail the `special` kind check despite a complete
   plate export. Repair the declaration-to-expectation projection, not a
   `special`-string exemption or a relaxed validation call.
2. Preserve undefined object correlation values. `Per_Object` cytoplasm K1, K2
   and overlap are native NULL/NaN but candidate 0 for image/object pairs (3,91),
   (3,108) and (7,7). Image 3 is B01, image 7 is D01. The resulting candidate means
   include those zeros; native means exclude NULL. For example B01 K1 is
   1.952585605558394 native versus 1.9265511308176155 candidate, the 148/150 factor.
   The demonstrated owner path is object threshold metrics in
   `colocalization.py` through `_divide_measurements`. Preserve each metric's
   native undefined semantics rather than blanket-changing all correlation
   families. Add both a focused native oracle and this multi-well export case.
3. Resolve terminal write policy for the benchmark. The live candidate writes
   an extra terminal `CellAndNucleiOverlay.tif` per well in addition to the native
   pipeline's requested overlay export. The runtime materialization flag alone
   did not disable it. Select/derive a matching declared policy before timing,
   or make equivalent writes on both sides and describe that scoped export
   extension. Do not silently count unequal output work as a matched comparison.

After those repairs, rerun this case at concurrency 1, settle source-owned start
and completion membership, then extend to one production server with N workers
against N native whole-group batches. Multi-job SQLite union, grouped/time-aware
partitioning and corpus breadth remain design work; see design.md. No full
corpus sweep was launched.

## Evidence

- `native_report.json`: actual native environment and four batch observations.
- `candidate_probe.json`: actual endpoint identity, compile/artifact/execution
  IDs, coarse timing, all eight successful axes and seven validation failures.
- `events_-1.json.gz`: losslessly compressed raw source progress events for the
  final production probe.
- `receipt.json`: source/manifest/script digests, environment, direct SQLite
  cell differences, per-image object counts and TIFF pixel digests.
- `native_warmup/` and `candidate_warmup/`: paired requested outputs, about 22 MiB
  total. Extra candidate terminal copies are documented but not archived here.
- `pilot_driver.py`: reproduction driver. It differs from the executed temporary
  driver only in using the caller's output directory argument and current checkout
  instead of hard-coded paths; both digests are retained.

Task-owned temporary workspaces (176 MiB) and native staging were removed after
retaining these artifacts. Both owned probe servers exited normally.

The processing source was HEAD `b2f3cf83` plus the existing dirty intensity fix;
its scoped diff digest is retained. No processing fix for the newly found gaps
was made in this benchmark pass. Neither manuscript nor historical reference
tree was modified. No commit, push or release was performed.

## Reproduce the bounded probe

From the OpenHCS checkout, allocate a fresh task-owned directory with `mktemp -d`
and substitute its full path for `/tmp/OPENHCS_PILOT_DIRECTORY` below. This
command intentionally fails closed at the currently demonstrated observation
validation gap; it does not proceed to candidate timing repeats.

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 PYTHONHASHSEED=0 PYTHONPATH="$PWD" \
.venv/bin/python \
benchmark/results/matched_batch_pilot_20260915/pilot_driver.py \
/tmp/OPENHCS_PILOT_DIRECTORY
```

The native runner uses `.venv-cellprofiler39/bin/python`. Its recorded versions
are CP/core 4.2.8.1, Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0. The candidate
is OpenHCS 0.8.5, Python 3.12.3, NumPy 2.1.3 and SciPy 1.18.0. These are measured
pilot versions, not inferred release-CI versions.
