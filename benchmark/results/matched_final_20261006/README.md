# Matched benchmarks on e905e7705

All five captures qualify on production source `e905e77057e588f48df141634b4eb5b4a765095a`: the original 30 authored pipelines on 1 assignment/1 worker, and the fixed selected-three cohort on 9/1, 9/3, 16/1 and 16/4. Each case completed warmup and three measured repetitions with every declared-output, database, CSV, image and inventory difference list empty. Source, input and retained-native custody checks passed; controllers ended with the same clean source head. The earlier [56c3da776 checkpoint](../matched_postexport_20261006/README.md) remains unchanged.

Repeated assignments independently execute one selected source sample; they are not additional biological samples. The scaling cohort preserves the original declarations selected from earlier v15 frontiers plus the representative 3D pipeline. It was not reselected after final rankings changed. Original manifests, commands and terminals are retained in [protocol](protocol/singlewell/command.json).

## Single-assignment measurements

All 30 execution speedups over actual native CellProfiler exceed 2×: minimum **2.955×**, median **4.401×**. All 30 total speedups exceed parity: minimum **1.327×**, median **3.370×**. `ExampleIlluminationCorrection_Example3` is weakest on both clocks; 2 total results are below 2×.

[Execution summaries](data/singlewell/execution_summary.csv), [total summaries](data/singlewell/total_summary.csv) and [qualification custody](data/singlewell/summary_custody.json) retain exact durations and evidence references.

## Matched worker comparisons

Efficiency is `T(N,1)/(p*T(N,p))`, using identical assignment counts and source. Loss versus ideal is `1-efficiency`. Additional loss relative to CP is `1-(OH efficiency/CP efficiency)`; negative values mean OH scales better. These definitions are distinct. Native serial denominators below come from matching actual single-worker captures; native parallel medians are original simultaneous-clock makespans, not projections or the separate serial baseline embedded in a parallel capture.

### 9 assignments: one versus 3 workers

| Pipeline | OH one-worker execution (s) | OH 3-worker execution (s) | OH execution efficiency | Native execution efficiency | Additional execution loss relative to CP | Parallel execution / total speedup over CP |
|---|---:|---:|---:|---:|---:|---:|
| ExampleVitra | 8.994373 | 3.819623 | 78.49% | 82.58% | 4.95% | 2.551× / 2.287× |
| ExampleIlluminationCorrection_Example3 | 1.561352 | 0.714968 | 72.79% | 54.26% | -34.15% | 3.120× / 2.039× |
| cp_tutorial_3d_monolayer | 27.005527 | 11.518025 | 78.15% | 92.66% | 15.65% | 3.992× / 3.540× |

[Exact execution and total values](matched-nine-efficiency.json) retain all denominators and both loss definitions. Measured losses versus ideal exceed 15% across this cohort; native-relative losses are reported separately.

### 16 assignments: one versus 4 workers

| Pipeline | OH one-worker execution (s) | OH 4-worker execution (s) | OH execution efficiency | Native execution efficiency | Additional execution loss relative to CP | Parallel execution / total speedup over CP |
|---|---:|---:|---:|---:|---:|---:|
| ExampleVitra | 15.955950 | 6.799969 | 58.66% | 67.38% | 12.94% | 2.133× / 1.965× |
| ExampleIlluminationCorrection_Example3 | 2.786461 | 1.150517 | 60.55% | 64.46% | 6.07% | 2.154× / 1.466× |
| cp_tutorial_3d_monolayer | 49.028282 | 17.614147 | 69.59% | 84.20% | 17.35% | 4.144× / 3.669× |

[Exact execution and total values](matched-sixteen-efficiency.json) retain all denominators and both loss definitions. Measured losses versus ideal exceed 15% across this cohort; native-relative losses are reported separately.

## Single-core amortization

Qualified 1/1, 9/1 and 16/1 points show execution and total time per assignment. Compilation plus client overhead per assignment is the median paired difference `(total - full server execution)/assignment_count`, not a claimed kernel/plumbing decomposition. It amortizes with assignment count; execution per assignment can still increase. Actual counts and paired observations are retained in each [mode custody](data/singlewell/summary_custody.json).

## Clocks, science and immutable evidence

OpenHCS execution covers complete `SERVER_PIPELINE_JOB`, including plate exports and finalization. Total sums the disjoint compile and execute client submit/wait phases. Native execution covers continuous pipeline execution through post-run, including preparation and modules; native total covers the prepared invocation. One-time CPPipe loading, server/catalog/kernel readiness, JVM startup and subsequent scientific comparisons are excluded. Memory was not measured.

The existing converter admitted source/input/environment custody, complete typed native observations, original shard requests/barriers and physical clocks, actual worker overlap, complete inventories and strict database/CSV/image comparisons. [Lightweight reports and phase receipts](reports/singlewell/ExampleVitra/candidate_report.json) and [original commands, terminals, manifests and converter](protocol/singlewell/command.json) are byte-identical copies. External native inputs retain original locations in their content and are archived under each case's `original_native/` directory; no timing or path was rewritten. Scientific images, measurement CSVs and databases remain at captured original locations and are not duplicated here. Progress CSVs are timing evidence.

Figures use the existing measured May-style consumer in [the paper figure provenance](../../../paper/figures/slas/matched_final_20261006/execution/figure2_provenance.json). Figure provenance owns actual source/output hashes; this archive adds no substitute receipts or synthetic timings.
