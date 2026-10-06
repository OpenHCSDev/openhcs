# Matched benchmarks on e905e7705

This draft archive retains the qualified measurements from the production source `e905e77057e588f48df141634b4eb5b4a765095a`. The earlier [56c3da776 checkpoint](../matched_postexport_20261006/README.md) remains unchanged.

Full-30 single-well and nine-assignment one-/three-worker captures are qualified. Sixteen-assignment one-worker capture is also qualified; the four-worker capture is still running. Final figure rendering and reading-copy review follow the complete collection.

## Single-well measurements

All 30 workflows completed warmup plus three measured repetitions with no declared-output or output-inventory differences. Execution speedup over native CellProfiler is 2.955× minimum and 4.401× median. Total speedup is 1.327× minimum and 3.370× median. The shortest illumination workflow is weakest on both clocks.

[Execution summaries](data/singlewell/execution_summary.csv), [total summaries](data/singlewell/total_summary.csv) and [qualification custody](data/singlewell/summary_custody.json) retain the exact durations and original evidence references.

## Nine-assignment worker comparison

| Workflow | OH one-worker execution (s) | OH three-worker execution (s) | Execution speedup over CP | Additional scaling loss relative to CP |
|---|---:|---:|---:|---:|
| ExampleVitra | 8.994373 | 3.819623 | 2.551× | 4.95% |
| ExampleIlluminationCorrection_Example3 | 1.561352 | 0.714968 | 3.120× | OH scales better |
| cp_tutorial_3d_monolayer | 27.005527 | 11.518025 | 3.992× | 15.65% |

Execution efficiency is the one-worker median divided by three times the three-worker median on the same nine assignments. Additional loss relative to CP is one minus the ratio of the two engines’ efficiencies. These are distinct from loss versus ideal threefold scaling. Native serial and parallel medians are genuine matched observations; repeated assignments reuse one biological sample.

[Full execution and total efficiency values](matched-nine-efficiency.json) retain both denominators, speedups and loss definitions.

## Clocks and evidence

OpenHCS execution covers the full server job, including plate exports. Its total covers compilation and client coordination. Native execution covers continuous pipeline execution, including preparation, modules and post-run work; native total covers the measured invocation. One-time endpoint, library, kernel, pipeline-loading and JVM startup, and scientific comparison are outside the declared pipeline clocks. Memory was not measured in these captures.

The existing converter admitted source/input/environment custody, complete native observations, native shard barriers and physical clocks, actual worker overlap and all declared-output comparisons. The copied summaries and custody files are byte-identical to the qualified originals. Original lightweight reports and phase receipts will be included before this draft is ready to merge. Scientific images, tables and databases stay at their captured original locations; they are not duplicated in this archive.
