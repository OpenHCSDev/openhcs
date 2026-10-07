# Integrated-main matched single-sample benchmarks

This is the current full single-sample manuscript record: all 30 original authored CellProfiler workflows on one selected source well or sample, one OpenHCS worker, one numerical thread and one physical CPU core. Fresh OpenHCS observations were acquired on clean production source `e251f313f45a568405e3987e77e4f89e18d934e1`, after the native payload placement, native callable ABI, single invocation composition, CuPy module import and Li tolerance fixes merged into main, with ArrayBridge 0.3.7. Every workflow completed a warmup and three measured repetitions, and all 120 observations passed the complete declared image, measurement CSV, database and output-inventory comparisons. Source before/after, inputs, installed dependencies, rebuilt native binaries, clock receipts and retained-native original-output custody passed the strict converter.

This record is the fresh completed integrated-main run, with unchanged actual stock single-process CellProfiler observations reused only after the benchmark's source/input/environment/hardware/storage guards passed. Original reports and custody paths are not rewritten. The [preceding full-cohort record](../matched_latestmain_20261006/README.md) and the [separately qualified latest 3D sixteen-assignment checkpoint](../matched_lastconsumer_20261006/README.md) remain distinct and unchanged. The latter has a different exact capture head and is not inserted into this full single-sample cohort.

These are independent qualified observations, not a controlled before/after experiment. The weakest execution and total ratios and the medians can change between independently acquired records; the measurements do not establish that every pipeline became faster or attribute differences to a particular runtime patch. [Original converter summaries](data/singlewell/execution_summary.csv), [total summaries](data/singlewell/total_summary.csv) and [the complete saved overview](data/singlewell/performance-overview.json) retain the actual observations. No old rows are spliced into the current result.

## Measured clocks and manuscript consumer

OpenHCS execution is the complete `SERVER_PIPELINE_JOB`, including plate exports and finalization. Total is the sum of disjoint compile and execute client submit/wait phases. CellProfiler execution includes pipeline preparation, modules and post-run; total is its prepared invocation. One-time CPPipe loading, JVM initialization, endpoint/function-library/kernel readiness and subsequent scientific comparison are outside both clocks. Axis-only execution remains diagnostic evidence in original custody and is not substituted for full-server execution. RAM is not supplied in these figure panels.

The existing measured figure owner derives [the current Figure 2 and manuscript claim include](../../../paper/figures/slas/benchmark-publication/benchmark_claims.json) from this record, and records all source/output hashes in [figure provenance](../../../paper/figures/slas/benchmark-publication/figure2_provenance.json). Abstract, methods, results and caption spans consume that one include through the existing paper-build controller; no numerical headline is copied manually into manuscript prose.

```sh
python paper/figures/build_slas_benchmark.py \
  --publication-record benchmark/results/matched_integrated_main_20261007 \
  --output-dir paper/figures/slas/benchmark-publication --frozen
```

The final full single-sample record is explicitly designated for the current manuscript after qualification. This designation does not claim that performance optimization is finished. Supplementary Figure 17 separately uses the latest qualified sixteen-assignment 3D primary comparison: actual stock single-process CellProfiler versus built-in OpenHCS workers. Externally orchestrated independent CP processes are retained as a separately labeled calibration, not a native CellProfiler multiprocessing feature.

## Original evidence

The [command, terminal and source/environment seal](protocol/singlewell/command.json), original converter, manifest, lightweight case reports and original measured phase receipts are retained byte-for-byte. Captured images, scientific CSVs and databases remain at their original physical locations and are not duplicated. The converter's absolute original paths and SHA256 values remain in [qualified custody](data/singlewell/summary_custody.json); the archived manifest is admitted against the original digest rather than relocated by assumption. No timing, scientific output or custody path was changed to create the figures.
