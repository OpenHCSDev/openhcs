# Official30 measured CellProfiler comparison, 6 October 2026

All 30 workflows completed one warmup and three measured repetitions per engine, with zero differences in the declared persisted scientific comparisons. The original full-suite terminal returned 0 on clean, unchanged production source `d8678dbd443d78e0c4e5d90f4c2e867af61af80b`. Candidate runs used one fork worker, one source well per workflow, CPU5 and one numerical thread; native CellProfiler used the same physical input selection and CPU/thread scope. The original actual native observations were reused only where the production workload, input, environment, host/CPU/storage and complete-observation guards admitted them. These are measured timings, not projections.

| Clock | Minimum speedup | Median workflow speedup | Workflows below 2× |
|---|---:|---:|---:|
| Execution | 2.766816× | 4.212748× | 0 |
| Total | 1.374813× | 3.262432× | 3 |

The weakest execution workflow is `ExampleVitra`. The weakest total workflow is `ExampleIlluminationCorrection_Example3`. Each workflow's speedup is its native median divided by its OpenHCS median, excluding warmup. The cohort median is the median of these 30 ratios, not a ratio of pooled engine timings. Scientific comparisons use the existing CellProfiler numerical tolerances; zero reported differences does not mean bitwise equality for every scalar.

Native execution covers the continuous pipeline call including `prepare_run`, `prepare_group`, modules, `post_run` and cleanup. OpenHCS execution covers the completed server job, including ordinary plate exports. Native total is its measured invocation, excluding one-time CPPipe loading and JVM startup; OpenHCS total is the sum of the disjoint compile and execute client `SUBMIT_OPENHCS` and `WAIT_OPENHCS` phases. Server startup, registry/kernel readiness and scientific comparison are outside these timing scopes. Nested server, compilation and axis timings are retained for audit and are not added again. RAM was not measured.

This dated checkpoint supersedes the manuscript timing inputs from the [5 October checkpoint](../official30_matched_20261005/README.md), which remains intact. It does not claim measurements for later unqualified optimization branches. The three total results below 2× are illumination correction Example 3, CombineObjects and PercentPositive.

## One data authority and paper figures

- [Execution summary](data/singlewell/execution_summary.csv)
- [Total summary](data/singlewell/total_summary.csv)
- [Original conversion custody](data/singlewell/summary_custody.json)
- [Execution speedup distribution](../../../paper/figures/slas/official30_matched_20261006/execution/measured_execution_speedup_cumulative_distribution_log.png)
- [Total speedup distribution](../../../paper/figures/slas/official30_matched_20261006/total/measured_total_speedup_cumulative_distribution_log.png)

Figures exist only under `paper/figures/slas/official30_matched_20261006`; there is no duplicate benchmark figure bundle. They were rendered from the archived summaries through the existing manuscript builder and measured figure owner. Each scope's `figure2_provenance.json` records repository-relative summary/custody/plotting-source hashes and every actual output hash. The execution scope has 19 rendered/report outputs, the total scope 17, plus one existing provenance record each. The base-2 log execution distribution is the headline view because the ~390× AllMethod outlier compresses the linear distribution. Execution marks the 2× target; total marks native parity (1×), achieved by all 30 workflows. Wide per-workflow SVG panels are appropriate for the supplement. Captions and statistics retain every workflow, including WoundHealing and the three total speedups below 2×.

The May 13 historical figures and source tables remain untouched. Their one-observation timing scopes, projected native scaling and unresolved WoundHealing observation are not mixed with this matched bundle. Actual selected repeated-assignment scaling is a separate follow-up and is not claimed by these singlewell summaries.

## Retained lightweight original evidence

`protocol/` contains byte copies of the original command, terminal and manifest, plus the exact private converter whose hash appears in the original custody. `reports/CASE/` contains byte copies of each original pilot provenance, native report, native request and candidate report. `reports/CASE/candidate_evidence/REPETITION/measured_pipeline_receipt.json` preserves the original warmup and three measured phase receipts (120 receipts in total). Original filenames and record contents were not rewritten or synthesized. Report/receipt copies were checked against their original digests during archival.

Native and candidate reports retain the actual image/CSV/database comparison results, selected-input inventories and output hashes. Original private output/input paths in those records intentionally retain their original execution meaning. Large scientific images, databases and measurement CSVs are not duplicated here; the original persisted packet remains at `/home/ts/.local/state/openhcs-maintenance/20261006/final-official30-singlewell-matched-v15`. This light archive supports review of measured clocks and recorded qualification, not an independent replay of scientific comparisons without the original datasets and exports.

Re-render without changing the data authority:

```sh
PYTHONPATH=. python paper/figures/build_slas_benchmark.py --summary-source '1 well / 1 worker=benchmark/results/official30_matched_20261006/data/singlewell/execution_summary.csv' --scope execution --output-dir paper/figures/slas/official30_matched_20261006/execution
PYTHONPATH=. python paper/figures/build_slas_benchmark.py --summary-source '1 well / 1 worker=benchmark/results/official30_matched_20261006/data/singlewell/total_summary.csv' --scope total --output-dir paper/figures/slas/official30_matched_20261006/total
```

## Actual single-core amortization: 1 and 8 assignments

The same dated production source completed all three declared frontier workflows with eight repeated source assignments, one worker and CPU5, using fresh genuine serial CellProfiler observations. Warmup and three measured repetitions passed all five scientific comparison inventories, and the full-suite terminal returned0 on unchanged clean `d8678dbd443d78e0c4e5d90f4c2e867af61af80b`. Repeated assignments reuse one biological source sample; they are not eight independent biological wells.

- [Declared three-workflow cohort](protocol/selected-three-case-manifest.json)
- [Actual8/1 execution summary](data/8assignments-1worker/execution_summary.csv)
- [Actual8/1 total summary](data/8assignments-1worker/total_summary.csv)
- [Original8/1 conversion custody](data/8assignments-1worker/summary_custody.json)
- [Measured1+8 single-core figure](../../../paper/figures/slas/official30_matched_20261006/single-core-amortization/measured_single_core_amortization.png)

| Workflow | OH total/assignment,1→8 | OH execution/assignment,1→8 | OH nonexecution/assignment,1→8 |
|---|---:|---:|---:|
| Vitra |1.3398→1.3134s|1.0722→1.2598s|0.2627→0.0538s|
| Illumination Example3 |0.4352→0.2323s|0.1997→0.1797s|0.2362→0.0501s|
|3D monolayer |3.3858→3.3031s|2.7360→3.0293s|0.6495→0.2453s|

Execution and total use per-engine medians divided by the exact declared assignment count. Nonexecution uses the median paired total-minus-server-execution difference divided by that count; it covers compilation and client submission/polling, not a physical breakdown of pixel processing and runtime plumbing. These three medians do not have to sum exactly. Vitra and3D execution per assignment increase despite nonexecution amortization; the figure preserves that outcome. Lines connect actual measured points as visual guides, not projections.16-assignment and matched-count multicore comparisons remain pending and are not represented.

`reports/8assignments-1worker/` and `protocol/8assignments-1worker/` preserve exact lightweight original reports, four phase receipts per workflow, command and terminal. Large images, databases and measurement CSVs remain in the original packet under `/home/ts/.local/state/openhcs-maintenance/20261006/measured-scaling-current-frontiers-preparation-v1/8assignments-1worker/capture`. All archived copies were byte-verified. The single-well summaries above remain unchanged.
