# Matched genuine-well Translocation pilot: declared `fork` workers

This is a bounded, three-observation correctness and timing diagnostic, **not**
the 30-workflow Figure 5 rerun or a general CellProfiler/OpenHCS speed claim.
The driver selected eight distinct BBBC013 Translocation wells (A01, A12, B01,
B12, C01, C12, D01, D12). Two native CellProfiler jobs each processed four
image sets, and ordinary OpenHCS execution processed the same wells on two
observed worker PIDs. The first complete batch on each side was a warm-up and
is omitted from the timed table.

| Timed observation | Native two-job invocation-to-completion makespan (s) | OpenHCS completed server job (s) | OpenHCS plate `ExportToDatabase` (s) | TIFF/SQLite differences |
| --- | ---: | ---: | ---: | ---: |
| 0 | 5.436 | 16.461 | 11.631 | 0 |
| 1 | 5.273 | 16.077 | 11.327 | 0 |
| 2 | 5.588 | 16.745 | 11.652 | 0 |

Every native shard reconstructed the whole native batch under the strict
equivalence policy. Every OpenHCS observation completed all eight axes with
two distinct, overlapping worker processes. Native and OpenHCS each produced
eight TIFF overlays, one SQLite database and one CPA properties file per
observation; image pixels, declared database tables and normalized CPA
properties had no reported differences. The warm-up's value-rich observation
declared all ten exports. Timed observations used outcome-only receipts and
compared the ten actual filesystem outputs, but those smaller receipts do not
independently list all ten export paths. The 17 selected native input files
were hashed before and after the pilot and did not change.

The table uses fuller intervals than the earlier first-module/first-axis
diagnostic: native time starts before per-run output-directory and measurement
setup and ends after `Measurements.close()`; its two-job makespan is
earliest invocation to latest completion. OpenHCS time is the ordinary server
execution record's start-to-completion interval after compilation. Both exclude
environment startup and pipeline compilation/loading. The native job processes
remain alive across observations, whereas OpenHCS creates forked workers for
each execution. These lifecycle differences and the single workflow limit
still prevent a generalized comparative performance claim. On this workload,
OpenHCS is plainly slower in the recorded full intervals; its progress trace
locates most of that time in the plate-scoped database export, not per-well
segmentation. No favorable speedup is inferred.

The compact retained bundle contains the exact native execution CPPipe,
imported and submitted Python source snapshots, submitted global configurations,
native worker reports, strict policy, pre/post input inventory and hashes,
OpenHCS endpoint/environment receipts, actual-output SHA-256 inventories,
progress events, worker lanes, step timings and the three small outcome files.
The copied CSV diagnostics use LF line endings; the source snapshots, receipts
and outcome files remain byte-for-byte copies. Duplicate native stdout JSON
was omitted because the structured native reports are retained.
Raw TIFF/SQLite outputs and the 34 MB warm-up value export are not committed;
the reports retain comparison outcomes and hashes, not a standalone copy of
the compared pixels. Receipts also contain the original absolute run paths, so
their file-existence checks cannot be replayed against this compact copy.

The run reports `source_dirty=true` because unrelated worktree state and the
untracked compact evidence directory were present. The benchmark driver and
native worker SHA-256 values in `pilot_provenance.json` were independently
checked against their bytes in commit `f4f489fe4`; this is exact source
provenance, but not a clean-worktree run. Native CellProfiler was 4.2.8.1 on Python 3.9.25,
NumPy 1.24.4 and SciPy 1.9.0. OpenHCS was 0.8.6 on its recorded Python 3.12
environment. The manifest declares the `fork` start method; imported pipeline
worker/thread/start-method overrides are cleared so that single global
declaration actually governs the measured execution.

Reproduce with the official dataset cache and native CellProfiler environment
available, using a newly empty output directory:

```sh
env OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 \
  NUMEXPR_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
  NPY_DISABLE_CPU_FEATURES=AVX512_SKX,X86_V4 PYTHONHASHSEED=0 \
  .venv/bin/python -m benchmark.matched_cellprofiler_batch \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --case cp_tutorial_translocation_final --well-count 8 \
  --output-dir /tmp/openhcs-matched-fork-reproduction \
  --native-python .venv-cellprofiler39/bin/python \
  --native-jobs 2 --openhcs-workers 2 --repetitions 3
```
