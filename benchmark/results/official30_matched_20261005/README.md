# Official30 measured CellProfiler comparison, 5 October 2026

All 30 workflows completed one warmup and three measured repetitions per engine, with zero differences in the declared persisted scientific comparisons. The original full-suite terminal returned 0 on clean, unchanged production source `5ad1e69565493220572de0a9c1af29f558b5f920`. Candidate runs used one fork worker, one source well per workflow, CPU5 and one numerical thread; native CellProfiler used the same physical input selection and CPU/thread scope. The original actual native observations were reused only where the production workload, input, environment, host/CPU/storage and complete-observation guards admitted them. These are measured timings, not projections.

| Clock | Minimum speedup | Median workflow speedup | Workflows below 2× |
|---|---:|---:|---:|
| Execution | 2.536511× | 3.985424× | 0 |
| Total | 1.357623× | 2.933984× | 4 |

The weakest execution workflow is `cp_tutorial_translocation_final`. The weakest total workflow is `ExampleIlluminationCorrection_Example3`. Each workflow's speedup is its native median divided by its OpenHCS median, excluding warmup. The cohort median is the median of these 30 ratios, not a ratio of pooled engine timings. Scientific comparisons use the existing CellProfiler numerical tolerances; zero reported differences does not mean bitwise equality for every scalar.

Native execution covers the continuous pipeline call including `prepare_run`, `prepare_group`, modules, `post_run` and cleanup. OpenHCS execution covers the completed server job, including ordinary plate exports. Native total is its measured invocation; OpenHCS total is the sum of the disjoint compile and execute client `SUBMIT_OPENHCS` and `WAIT_OPENHCS` phases. Server startup, registry/kernel readiness and scientific comparison are outside these timing scopes. Nested server, compilation and axis timings are retained for audit and are not added again. RAM was not measured.

## One data authority and paper figures

- [Execution summary](data/singlewell/execution_summary.csv)
- [Total summary](data/singlewell/total_summary.csv)
- [Original conversion custody](data/singlewell/summary_custody.json)
- [Execution speedup distribution](../../../paper/figures/slas/official30_matched_20261005/execution/measured_execution_speedup_cumulative_distribution_log.png)
- [Total speedup distribution](../../../paper/figures/slas/official30_matched_20261005/total/measured_total_speedup_cumulative_distribution_log.png)

Figures exist only under `paper/figures/slas/official30_matched_20261005`; there is no duplicate benchmark figure bundle. They were rendered from the archived summaries through the existing manuscript builder and measured figure owner. Each scope's `figure2_provenance.json` records repository-relative summary/custody/plotting-source hashes and every actual output hash. The execution scope has 19 rendered/report outputs, the total scope 17, plus one existing provenance record each. The log execution distribution is the main headline view because the ~300× AllMethod outlier compresses the linear distribution. Wide per-workflow SVG panels are appropriate for the supplement. Captions and statistics retain every workflow, including WoundHealing and the four total speedups below 2×.

The May 13 historical figures and source tables remain untouched. Their one-observation timing scopes, projected native scaling and unresolved WoundHealing observation are not mixed with this matched bundle. Actual selected repeated-assignment scaling is a separate follow-up and is not claimed by these singlewell summaries.

## Retained lightweight original evidence

`protocol/` contains byte copies of the original command, terminal and manifest, plus the exact private converter whose hash appears in the original custody. `reports/CASE/` contains byte copies of each original pilot provenance, native report, native request and candidate report. `reports/CASE/candidate_evidence/REPETITION/measured_pipeline_receipt.json` preserves the original warmup and three measured phase receipts (120 receipts in total). Original filenames and record contents were not rewritten or synthesized. Report/receipt copies were checked against their original digests during archival.

Native and candidate reports retain the actual image/CSV/database comparison results, selected-input inventories and output hashes. Original private output/input paths in those records intentionally retain their original execution meaning. Large scientific images, databases and measurement CSVs are not duplicated here; the original persisted packet remains at `/home/ts/.local/state/openhcs-maintenance/20261005/final-official30-singlewell-matched-v10`. This light archive supports review of measured clocks and recorded qualification, not an independent replay of scientific comparisons without the original datasets and exports.

Re-render without changing the data authority:

```sh
PYTHONPATH=. python paper/figures/build_slas_benchmark.py --summary-source '1 well / 1 worker=benchmark/results/official30_matched_20261005/data/singlewell/execution_summary.csv' --scope execution --output-dir paper/figures/slas/official30_matched_20261005/execution
PYTHONPATH=. python paper/figures/build_slas_benchmark.py --summary-source '1 well / 1 worker=benchmark/results/official30_matched_20261005/data/singlewell/total_summary.csv' --scope total --output-dir paper/figures/slas/official30_matched_20261005/total
```
