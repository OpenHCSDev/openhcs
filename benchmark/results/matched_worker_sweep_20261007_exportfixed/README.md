# Qualified matched worker sweep

All seven modes are strictly qualified and immutably archived for all thirty workflows. Every mode has one warmup and three measured OpenHCS repetitions, with complete declared image, CSV, database and output-inventory parity. The figures are rendered through the existing May-style owner. Timed production is frozen at `d06b7226c82fc6de8ab6b644f3bec417f4b7b922`; later main changes are not retroactively assigned to these measurements.

The [seven-mode protocol](protocol/v6/protocol-manifest.json) retains the May schedule (workers/assignments: 1/1, 2/8, 3/12, 4/16), plus every worker count on twelve fixed assignments. Repeated assignments reuse the selected genuine source sample; they are computational replicates, not independent biological wells. Earlier protocols, retired commands, original failed captures and the original `matched_worker_sweep_20261007` record remain preserved.

## Execution and total speedup

Each ratio uses one complete native first-use-inclusive batch divided by the median of three measured OpenHCS repetitions. The existing [numerical include](figures/benchmark_claims.json) owns these summaries and manuscript tokens.

| OpenHCS assignments / workers | Native reference | Execution minimum / median | Total minimum / median |
| --- | --- | --- | --- |
| [1 / 1](data/first_use/singlewell/) | Actual first batch | 3.542× / 6.393× | 2.660× / 4.066× |
| [8 / 2](data/first_use/8assignments-2workers/) | Actual first batch | 2.661× / 6.804× | 2.540× / 6.071× |
| [12 / 1](data/first_use/12assignments-1worker/) | Projected; target n=0 | 2.557× / 4.560× | 2.335× / 4.274× |
| [12 / 2](data/first_use/12assignments-2workers/) | Projected; target n=0 | 2.670× / 7.327× | 2.576× / 6.852× |
| [12 / 3](data/first_use/12assignments-3workers/) | Projected; target n=0 | 2.894× / 9.015× | 2.755× / 7.999× |
| [12 / 4](data/first_use/12assignments-4workers/) | Projected; target n=0 | 2.993× / 10.781× | 2.843× / 9.209× |
| [16 / 4](data/first_use/16assignments-4workers/) | Projected; target n=0 | 2.944× / 10.301× | 2.848× / 9.168× |

Actual OpenHCS one-to-four-worker execution scaling on twelve fixed assignments has median 2.269222×, minimum 1.085641× (Neighbors) and maximum 3.093718× (Illumination Correction Example 2). These actual same-workload controls are distinct from CellProfiler-relative speedups and do not establish ideal fourfold scaling.

## Clock and native policy

Execution covers the complete `SERVER_PIPELINE_JOB`, including coordination, saving, exports, publication and finalization. OpenHCS total adds disjoint compilation and client coordination, counting nested durations once. External process/JVM/ZMQ/server startup, library readiness and scientific qualification are outside pipeline clocks. Numerical threads are one. Single-assignment timing uses CPU5; multi-assignment timing permits CPUs2–5. Process-tree peak RAM is unavailable; historical May RAM is never substituted.

CP1 and CP8 are actual stock, one-process serial batches. Natural native initialization inside its pipeline call remains included. Original native reports, clocks and outputs are retained unchanged, including independently completed native tail cases and the earlier failed suite terminal. CP12 and CP16 have zero actual target native observations and use:

`T(N) = T(8, first) + (N - 8) * median(T(8, subsequent)) / 8`

Native prepared-invocation total adds the actual first anchor preparation duration once. No independent-process native calibration is presented as a stock CellProfiler multiprocessing feature.

[Actual one/eight-assignment calibration](diagnostics/native-full30-calibration/README.md) preserves all sixty original report identities and discloses different allowed CPU affinities. [Projection validation](calibration/cold_first/cold-first-model-validation.json) covers three short workflows with actual serial 8/12/16 batches under matched affinity. The six twelve/sixteen same-session signed errors are −7.058% to +0.902%; original-campaign anchors against later targets give −14.034% to −3.124%, exposing cross-session variation. The separate two-sample model has at most 5.209% absolute error across nine comparisons but is not adopted. These diagnostics are not full-thirty-workflow measured target validation.

## Figures and original evidence

- [Single-sample execution and total, logarithmic](figures/measured_benchmark_publication_log.png) and [linear](figures/measured_benchmark_publication.png).
- May execution: [logarithmic](figures/may/execution/may_execution_mean_workflow_points_log.png), [linear](figures/may/execution/may_execution_mean_workflow_points.png), [paired clocks and ratios](figures/may/execution/first_use_workflow_metrics.csv).
- May total: [logarithmic](figures/may/total/may_total_mean_workflow_points_log.png), [linear](figures/may/total/may_total_mean_workflow_points.png), [paired clocks and ratios](figures/may/total/first_use_workflow_metrics.csv).
- Actual fixed-twelve execution [scaling](figures/fixed12/execution/scaling/derived_workflow_metrics.csv) and [efficiency](figures/fixed12/execution/efficiency/derived_workflow_metrics.csv); total [scaling](figures/fixed12/total/scaling/derived_workflow_metrics.csv) and [efficiency](figures/fixed12/total/efficiency/derived_workflow_metrics.csv).
- Original [reports](reports/), [qualified summaries and custody](data/first_use/), [commands and environment seals](protocol/). Generated provenance retains figure inputs, sources and output hashes.

The same renderer produces manuscript-consumable assets at `paper/figures/slas/benchmark-publication`; the existing paper-build owner resolves declared numerical spans from its generated include. No separate painter, parser or manually maintained numerical claim authority is introduced.

## Qualification infrastructure changes

Qualifier changes are outside timed server/worker clocks. The first two modes use serial qualification. Later comparisons use two forked tasks on CPUs0/1. The comparer overlays only the admitted artifact core; timed children continue loading clean D06. Actual core search roots are inventoried before and after each case.

The generic [export-reference repair](diagnostics/export-reference-repair/integration-summary.json) preserves complete output coverage. At the v5 boundary, [selected SQLite decoding](diagnostics/qualification-boundary/sqlite-reuse-selected-decoding/sqlite-select-actual-D06-receiving/proof.json), immutable measurement-view reuse and [combined receiving](diagnostics/qualification-boundary/combined-receiving/combined-actual-D06-receiving/proof.json) removed repeated qualification work while retaining exact full results. The [live native-cache identity proof](diagnostics/qualification-boundary/live-advanced-native-cache-identity-proof.json) records cold native-fact rebuild costs; warmed private timings do not predict initial live gaps.

At v6, the [planned projection fix](diagnostics/candidate-planned-projection/candidate-planned-projection-proof.json) moved anchor declarations into existing row records and removed repeated numeric-text parsing and runtime generic casts. Saved Grid qualification CPU fell 19.897→15.486 seconds; contended wall timings are not controlled speedup evidence. Source-bound native entries rebuilt safely. [Import admission](diagnostics/candidate-planned-projection/v6-source-overlay-import-admission.json) confirms only three audited qualifier files changed and timed children retained D06.

[Saved Grid scope counterevidence](diagnostics/candidate-planned-projection/saved12-grid-selection-proof.json) rejects the whole-plate semantic-projection hypothesis: the existing owner selects 1,800 W001 rows from 21,600 physical rows before projection. Historical comparisons using different qualifier versions do not establish workload scaling. Original source, receiving scripts and controls remain with each diagnostic.
