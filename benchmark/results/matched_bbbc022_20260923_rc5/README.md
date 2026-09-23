# Matched BBBC022 advanced-segmentation pilot

This is a bounded, output-complete correctness and timing diagnostic, **not** a
general CellProfiler/OpenHCS throughput result or a replacement for Figure 5.
The imported advanced-segmentation tutorial ran on eight distinct BBBC022 wells
(A01, A12, B01, B12, C01, C12, D01, D12), two image sets per well. Two native
CellProfiler processes each handled eight image sets; ordinary OpenHCS execution
used two observed worker processes for the same eight wells. Each side ran one
warm-up and one timed repetition.

| Repetition | Native two-job invocation makespan (s) | Native first-module makespan (s) | OpenHCS completed server job (s) | OpenHCS worker execution (s) | SQLite/CPA differences |
| --- | ---: | ---: | ---: | ---: | ---: |
| Warm-up | 211.026 | 209.818 | 180.707 | 119.280 | 0 |
| Timed | 206.459 | 205.872 | 189.933 | 126.457 | 0 |

Both native shard batches reconstructed the corresponding whole-batch native
output under the strict equivalence policy. The timed native invocation-start
skew was 0.0097 s: both processes waited at a file-backed barrier **before**
their timed intervals began. Both OpenHCS repetitions completed all eight axes
on two distinct, overlapping worker PIDs. Every run on each side emitted one
SQLite database and seven CellProfiler Analyst properties files. The shared
value comparison found no SQLite-table or normalized-properties differences;
there were no saved images to compare. Every OpenHCS output file was declared
by the ordinary runtime, with none missing or unexpected. The source-image
inventory was unchanged before and after the pilot.

The native interval begins at each already-running CellProfiler process's
invocation and ends after its measurements close; the two-job makespan spans
the earliest start to latest finish. The OpenHCS interval is the ordinary
server execution record after compilation, including worker lifecycle and
plate-scoped SQLite export. Compilation took 82.114 s in warm-up and 80.471 s
in the timed repetition, outside those server-job intervals. Native processes
persisted between repetitions, whereas OpenHCS created workers for each job.
These boundaries and lifecycles are not identical, and one timed repetition on
one workflow cannot establish a comparative speedup or throughput ranking.

The retained compact files include the exact submitted native CPPipe and
OpenHCS Python/configuration sources, native worker requests and environment,
strict policy, input and output SHA-256 inventories, worker-event diagnostics,
ordinary execution receipts, and the outcome-only observation files. The
`report.json` also embeds native-shard reconstruction and per-repetition value
comparison results. Raw SQLite databases and measurement scratch files remain
local rather than being added to git; the compact bundle records their hashes
and comparison outcomes, not standalone copies of their values. Original
absolute paths in receipts will not resolve in a separate checkout. Diagnostic
CSVs have LF line endings in this bundle; source snapshots, receipts and
outcome files retain their original bytes. Generated Python source snapshots
are stored as `.py.txt` so the repository's implementation formatter does not
rewrite measured source; the local run retains the original `.py` files.

This run used OpenHCS source commit `f0dc3193983d16de27b1e9c0164880dc99aa8b81`
and reports `source_dirty=true` because unrelated untracked work and prior
pilot outputs were present. The driver and native worker hashes, submitted
source hashes, and manifest/CPPipe hashes provide precise source provenance,
but this was not a clean-worktree run. Native CellProfiler was 4.2.8.1 on
Python 3.9.25, NumPy 1.24.4, SciPy 1.9.0; the OpenHCS endpoint environment is
recorded in each measured receipt. The two native jobs used separate
run-local temporary directories, avoiding a shared `/tmp` measurement file.

To reproduce with the official dataset cache and native CellProfiler
environment available, use a **new empty** output directory:

```sh
env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 PYTHONHASHSEED=0 \
  OPENHCS_CPU_ONLY=true QT_QPA_PLATFORM=offscreen \
  .venv/bin/python -m benchmark.matched_cellprofiler_batch \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --case cp_tutorial_advanced_segmentation_final \
  --well A01 --well A12 --well B01 --well B12 \
  --well C01 --well C12 --well D01 --well D12 \
  --output-dir /path/to/new/bbbc022-pilot-output \
  --native-python .venv-cellprofiler39/bin/python \
  --native-jobs 2 --openhcs-workers 2 --repetitions 1
```
