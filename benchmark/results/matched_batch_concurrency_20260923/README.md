# Matched eight-well concurrency pilot, 2026-09-23

Status: **a reproducible bounded comparison, not a manuscript speedup claim**.
This run used `benchmark/matched_cellprofiler_batch.py` with two native
CellProfiler jobs and two OpenHCS worker processes on the same eight genuine
Translocation-final wells. It does not replace the paper's 30-workflow
throughput figure or establish general comparative performance.

The native full batch and the two disjoint native jobs (image sets 1–4 and
5–8) each ran a warm-up followed by three observations. The OpenHCS execution
server also ran a warm-up followed by three observations. Native CellProfiler
4.2.8.1 used Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0; OpenHCS used its
recorded Python 3.12 environment. The retained CPPipe, imported workflow,
submission snapshots, exact selected-input digests, worker reports, ZMQ
receipts, output SHA-256 inventories and strict comparison policy are in this
directory. `input_inventory.json` was hashed immediately *after* the run from
the selected native source workspace, not asserted to be an execution-start
hash.

The two native jobs' outputs reconstructed the whole native batch under the
strict equivalence policy for every warm-up and observed repetition: eight
overlay images plus the combined CPA-declared image and object table rows;
plate-wide tables and CPA properties agreed in each shard. Every OpenHCS run
completed all eight axes and matched the whole native SQLite and TIFF values
with zero reported differences. The warm-up retained a value-rich runtime
observation, including ten declared exports. Timed OpenHCS observations used
ordinary outcome-only receipts to avoid a ~35 MB diagnostic-value export;
their ten filesystem outputs were compared against native images, SQLite and
CPA properties, but their receipt does **not** independently enumerate ten
declared export paths. The three retained outcome pickles each contain eight
successful axes and the matching execution ID.

| Observed batch | Native two-job first-module-to-completion makespan | OpenHCS first-axis-to-server-completion | OpenHCS completed server job | Native worker overlap | OpenHCS worker overlap |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 6.227 s | 22.693 s | 27.466 s | 4.965 s | 1.295 s |
| 1 | 6.272 s | 24.040 s | 29.209 s | 4.564 s | 1.190 s |
| 2 | 6.537 s | 23.164 s | 27.926 s | 4.610 s | 0.987 s |

Actual progress events prove two distinct OpenHCS worker PIDs per run and
eight unique axes. The OpenHCS second worker started several seconds after the
first, so configured process count did not imply equally effective overlap.
The measured OpenHCS interval includes about 12.8–13.1 seconds after the last
axis completion; its constituent cleanup, plate-scoped and export work has not
yet been separately timed. Native job processes persisted across repetitions,
whereas OpenHCS worker PIDs changed with each run. Native preparation precedes
the first module callback; OpenHCS compilation and pre-axis work precede the
first axis event. Those boundary and lifecycle differences preclude a
like-for-like speedup ratio from this table. On this one workload, the recorded
OpenHCS intervals are plainly longer; no favorable comparison is inferred.

The run reported `source_dirty=true` because unrelated checkout state was
present. The driver, native worker, manifest and CPPipe hashes are retained,
but this is not clean-checkout publication provenance. Full TIFF and SQLite
outputs and the large warm-up value pickle were deliberately not committed;
the retained reports contain their file inventories and comparison outcomes.
Captured Python sources use `.py.txt` names so formatting tools cannot alter
the exact bytes hashed in their receipts. The older apparent two-worker probe
was **invalid for concurrency**: an imported pipeline-level `num_workers=1`
overrode the global value. This run resets that override to inherit the global
worker count and rejects a run unless two distinct worker PIDs actually execute.

Reproduce with the official dataset cache and CellProfiler 4.2.8.1 venv
available, using a newly empty output directory:

```sh
env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 PYTHONHASHSEED=0 \
  .venv/bin/python -m benchmark.matched_cellprofiler_batch \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --case cp_tutorial_translocation_final --well-count 8 \
  --output-dir /tmp/openhcs-matched-reproduction \
  --native-python .venv-cellprofiler39/bin/python \
  --native-jobs 2 --openhcs-workers 2 --repetitions 3
```
