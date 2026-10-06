# Lab Meeting Benchmark Artifacts - 2026-05-13

This directory stores the compact CSV and figure artifacts used for the May 13
official30 CellProfiler-vs-OpenHCS benchmark discussion.

## Contents

- `official30_well_throughput/data/single_process_summary.csv`: single-process
  parity and timing summary for the official30 manifest.
- `official30_well_throughput/data/core_scaling_well_throughput.csv`: source
  CSV for the `1/2/3/4 core` presentation figures.
- `official30_well_throughput/data/wells_per_core_2c3c4c.csv`: source CSV for
  the `1..4 wells/core` queue-depth sweep on 2, 3, and 4 cores.
- `official30_well_throughput/data/wells_per_core_4c_6wpc_8wpc.csv`: additional
  4-core queue-depth source rows for 6 and 8 wells/core.
- `official30_well_throughput/figures/`: reusable presentation figure pack
  generated from the CSV inputs above.

## Interpretation Caveat

These are historical observations with different timing boundaries and output
workloads, not a matched comparison of current runtimes. The May native timer
wraps `subprocess.run`, including process, import and JVM startup. The OpenHCS
`1 core` point measures direct, same-process single-well execution; its
`2/3/4 cores` points measure OpenHCS multiprocessing throughput over replicated wells.
The generated OpenHCS pipeline requests
`prune_dead_unmaterialized_artifact_steps=True` and
`materialize_skipped_save_images=False`, with a different spreadsheet-export path.
Exact historical input, environment and complete-output equivalence to current
runs is not established by these compact artifacts.

The native multiwell denominator is a serial projection:
`native_single_sample_execution_seconds * well_count`. It is not a measured
native makespan with matching worker concurrency. The archived speedups and
queue-depth figures must be read with that projection and the distinct execution
boundaries; they do not establish matched native scaling or a current speedup.
Fixed OpenHCS fork/work-queue/file costs can also dominate very small pipelines
at low well counts.

The WoundHealing native baseline is additionally unqualified. Its exact `900 s`
value equals the configured timeout. At historical source `f58bca4e9`,
`CachedNativeReferenceTimingPolicy` in `benchmark/cellprofiler_comparison.py:655`
substitutes that timeout for a cached successful reference with missing elapsed
timing. No retained original observation proves that the WoundHealing `900 s`
entry was an actual elapsed native measurement. The source CSV's `success`
status describes OpenHCS execution; it does not authenticate native timing.

That entry yields approximately `725x` in the `1w_1t` core-scaling row. Removing
only this unqualified row changes that table's arithmetic mean from `36.30x` to
`12.55x`; this is a sensitivity check, not a corrected matched benchmark, since
all other boundary and custody limitations remain. Do not describe `900 s` as
measured CellProfiler runtime or use the uncensored corpus means as headline
performance evidence. The archived CSVs and figures are preserved unchanged.

Current typed native batch reports require complete measured observations and
do not use this historical missing-timing fallback. Fresh matched measurements
must state their own clock boundaries, concurrency, input custody and exported
output scope; they cannot be inferred from this archive.

## Regeneration

```bash
../openhcs/.venv/bin/python scripts/benchmark_cellprofiler_vs_openhcs.py \
  plot-well-throughput-presentation \
  --single-process-summary-csv benchmark/results/labmeeting_20260513/official30_well_throughput/data/single_process_summary.csv \
  --core-scaling-csv benchmark/results/labmeeting_20260513/official30_well_throughput/data/core_scaling_well_throughput.csv \
  --wells-per-core-csv benchmark/results/labmeeting_20260513/official30_well_throughput/data/wells_per_core_2c3c4c.csv \
  --additional-wells-per-core-csv benchmark/results/labmeeting_20260513/official30_well_throughput/data/wells_per_core_4c_6wpc_8wpc.csv \
  --output-dir benchmark/results/labmeeting_20260513/official30_well_throughput/figures
```
