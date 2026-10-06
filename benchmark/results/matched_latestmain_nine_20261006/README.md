# Latest-main matched nine-assignment worker comparison

This record retains fresh one-worker and three-worker OpenHCS observations for the unchanged selected-three cohort: Vitra, illumination correction Example 3, and the 3D monolayer workflow. Each pipeline performs nine independent repeated assignments of its selected biological source sample; these are not additional biological samples. Both modes completed a warmup and three measured repetitions on clean source `71aded26c26ec3d462ce7f622dd9d76eec737d01`, with all declared image, measurement CSV, database and output-inventory comparisons passing. The production/runtime and benchmark bytes are identical to the separately qualified full single-sample source, but their exact capture heads remain distinct rather than being relabeled.

The primary comparison uses actual **one-process stock CellProfiler** on the same assignments versus OpenHCS's built-in workers, including worker coordination, saving, plate exports and finalization. The existing nominal measured-source owner derives the denominator from the original qualified serial observations and checks source, pipeline declarations, assignments, process count and measured clock scope. Original same-mode CSVs retain their original calibration ratios and are not rewritten to construct the primary figure.

The separate calibration uses three externally orchestrated independent stock CP processes. This is not native CellProfiler multiprocessing and is not the primary product comparison. Its actual concurrent timings and original start-barrier custody are preserved. All retained-native observations passed the original workload/input/software/hardware/storage guards; no native timing is projected.

## Measured clocks and figure consumers

OpenHCS execution is the full `SERVER_PIPELINE_JOB`, including plate exports and finalization; CP execution includes preparation, modules and post-run. Total includes disjoint OpenHCS compile and execute submit/wait phases, compared with the prepared CP invocation. Endpoint/library/kernel readiness, one-time pipeline loading/JVM startup and subsequent scientific comparison are outside both clocks. Axis-only timing remains diagnostic evidence. RAM was not measured for these figure panels.

[Primary execution figures](../../../paper/figures/slas/matched_latestmain_nine_20261006/primary-execution/measured_execution_caption.md) and [primary total figures](../../../paper/figures/slas/matched_latestmain_nine_20261006/primary-total/measured_total_caption.md) supply Supplementary Figure 17. [Execution calibration](../../../paper/figures/slas/matched_latestmain_nine_20261006/independent-cp-calibration-execution/measured_execution_caption.md) and [total calibration](../../../paper/figures/slas/matched_latestmain_nine_20261006/independent-cp-calibration-total/measured_total_caption.md) remain separate controls. Exact per-workflow ratios are derived in their figure tables and checksum provenance rather than manually copied into prose. Average bars are arithmetic averages across the selected pipelines, not pooled elapsed time.

To reproduce the primary execution figure from the repository root:

```sh
python paper/figures/build_slas_benchmark.py \
  --summary-source '9 assignments/1 worker=benchmark/results/matched_latestmain_nine_20261006/data/9assignments-1worker/execution_summary.csv' \
  --summary-source '9 assignments/3 workers=benchmark/results/matched_latestmain_nine_20261006/data/9assignments-3workers/execution_summary.csv' \
  --native-baseline benchmark/results/matched_latestmain_nine_20261006/data/9assignments-1worker/execution_summary.csv \
  --scope execution \
  --output-dir paper/figures/slas/matched_latestmain_nine_20261006/primary-execution
```

Use `total` consistently in scope, summary filenames and output directory for total time. Omit `--native-baseline` and choose the distinct calibration output directory to reproduce the external-process control.

The [latest full 30-pipeline single-sample record](../matched_latestmain_20261006/README.md), [separate latest sixteen-assignment 3D checkpoint](../matched_lastconsumer_20261006/README.md) and [historical single-core amortization record](../matched_postgrid_20261006/README.md) remain separate. No cross-source rows are silently inserted into one qualified cohort. These are independent qualified observations, not a controlled before/after experiment or a claim that paging has been eliminated.

Original lightweight reports, warmup/phase receipts, controller commands, terminals, converter, source/environment seals and native start-barrier evidence are retained byte-for-byte. Images and scientific CSV/databases remain at original captured locations. Original absolute custody paths and SHA256 declarations are unchanged; the archived manifest is admitted against its original converter digest. [Archive verification](protocol/archive-byte-custody-qualification.json) confirms the retained original custody inputs.
