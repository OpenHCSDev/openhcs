# Qualified current-production worker sweep

This record combines five newly measured configurations with the two qualified fixed-twelve captures already published in `matched_fixed12_physical_facts_20261008`. All seven configurations use production revision `3b173fd8c07bf0cbacd00c0b7f4c2759a3fc3ad9`, all thirty workflows, one warmup and three measured OpenHCS repetitions. The existing qualifier admits the complete declared output inventory and image, CSV and database parity for every repetition.

The [protocol](protocol/current/protocol-manifest.json) identifies newly captured and reused configurations. The [refresh plan](protocol/current/refresh-plan.json) and [source/environment seal](protocol/current/source-and-environment.json) retain capture provenance. Reusing the two identical-production fixed-twelve captures avoids repeating measurements already qualified on this implementation. Later manuscript and CI-only commits do not change the measured production source.

The initial one-worker single-sample capture allowed prepared workers CPUs2–5 even though its client and server used CPU5. Its [qualified summary and custody](diagnostics/singlewell-initial-wider-worker-affinity/summary_custody.json) are retained as a diagnostic; its original raw captures remain unchanged. The single-sample view here is a fresh strict-one-core follow-up, performed after the multicore captures complete to avoid CPU contention.

## Measurements and figures

The [generated numerical include](../../../paper/figures/slas/benchmark-publication/benchmark_claims.json) derives every manuscript scalar and seven-mode distribution from this record. The [main chart](../../../paper/figures/slas/benchmark-publication/measured_benchmark_publication_log.png), [worker schedule](../../../paper/figures/slas/benchmark-publication/reference-layout/reference_core_summary_log.png), and [assignment comparison](../../../paper/figures/slas/benchmark-publication/reference-layout/reference_assignments_summary_log.png) use the existing May-style figure owners. Generated input/output hash receipts bind the figures and numerical include to these qualified sources.

Qualified paired clocks and custody are under `data/first_use/`; immutable reports and phase receipts are under `reports/`. The seven configurations are assignments/workers 1/1, 8/2, 12/1, 12/2, 12/3, 12/4 and 16/4. Fixed-twelve scaling compares the same workload across worker counts. Repeated assignments reuse genuine source samples and are computational replicates rather than independent biological wells.

The [serial-batch execution figure](../../../paper/figures/slas/benchmark-publication/serial_batch/execution/serial_cp_relative_speedup_log.png) compare one processing worker at one and twelve assignments, with execution and total CP-relative speedups, seconds per sample and batching-reduction factors. CP1 is measured and CP12 is explicitly projected. Each chart retains every workflow and its paired values. Supplementary Figure6 embeds these views.

## Clock and native policy

Execution covers the entire `SERVER_PIPELINE_JOB`, including worker coordination, loading, saving, exports, publication and finalization. OpenHCS total adds disjoint compilation and client coordination, counting nested durations once. External process/JVM/ZMQ/server startup, function-library readiness and scientific qualification are excluded. Numerical libraries use one thread. For the single-assignment capture, all receiving-client, server and prepared-worker threads are pinned to CPU5 after readiness; native CP1 also uses CPU5. In multi-assignment captures, prepared workers allow CPUs2–5, with one numerical thread per worker; the one-worker server allows CPU5 and the other servers allow CPUs2–5. Per-mode recipes retain the actual affinities. Process-tree peak RAM is unavailable; historical May RAM is not substituted.

CP1 and CP8 references are unchanged genuine stock, one-process serial batches. Headline ratios use their complete first batch, including native initialization inside execution, divided by the median of three measured OpenHCS repetitions. Native reports retain one first batch and three subsequent batches. CP12 and CP16 have zero actual target observations and use the existing projection authority:

`T(N) = T(8, first) + (N - 8) * median(T(8, subsequent)) / 8`

Native prepared-invocation total adds the actual first anchor preparation duration once. Independent parallel CP processes are not presented as a stock CellProfiler feature.

The original [one/eight-assignment calibration](diagnostics/native-full30-calibration/README.md) preserves sixty actual native reports and discloses different CPU affinities. The original [projection validation](calibration/cold_first/cold-first-model-validation.json) covers three short workflows with genuine serial 8/12/16 batches under matched affinity; it does not establish measured target accuracy for all thirty workflows. These unchanged calibration attachments are retained evidence, not newly measured results.

## Reproduction

From the repository root:

```sh
python benchmark/results/matched_worker_sweep_20261008_latestproduction/protocol/render_sweep.py \
  --record benchmark/results/matched_worker_sweep_20261008_latestproduction \
  --protocol-manifest benchmark/results/matched_worker_sweep_20261008_latestproduction/protocol/current/protocol-manifest.json \
  --output-dir paper/figures/slas/benchmark-publication
```

Then use the reference-layout and composite regeneration commands in [paper/README.md](../../../paper/README.md). Retain the independently qualified coverage evidence when regenerating timing charts. The manuscript resolves numerical claim spans from the generated include; no separate manually maintained scalar source is introduced.
