# Qualified last-consumer 3D checkpoint

This record contains the original 3D monolayer pipeline on 16 repeated assignments, using one and four built-in OpenHCS workers. Both captures qualified on production source `2cda84a3691e6f2c87bff4c9f7a540aea9e0c902`, subsequently merged through PR #1072. Every warmup and three measured repetitions passed the declared image, measurement CSV, database and inventory comparisons: 128 assignment executions in total. Installed environment and native binaries were unchanged. Repeated assignments are independent executions of the same biological sample, not additional biological samples.

The primary comparison uses **one stock CellProfiler process** on the same 16 assignments, compared with OpenHCS's integrated worker execution. The separately shown CP parallel calibration uses four externally orchestrated independent stock processes. It is not a native CellProfiler multiprocessing feature and has no OpenHCS worker coordination. Neither denominator is projected. Original matched CSVs still contain their original same-mode calibration ratios; the existing nominal measured-source family derives the primary baseline at rendering time from the qualified single-process observations. Source, pipeline declaration, assignment identity, clock scope and native process count are checked before pairing. Scientific custody and timing records are not rewritten.

Execution is the complete OpenHCS `SERVER_PIPELINE_JOB`, including plate exports and finalization; CellProfiler execution includes preparation, pipeline modules and post-run. Total includes disjoint OpenHCS compile and execute submit/wait phases and the prepared CellProfiler invocation. Server/function-library/kernel startup and subsequent scientific comparison are excluded. Axis-only execution is retained in original custody as diagnostic evidence and is not substituted for the full server clock. Process RAM was not measured for the figure panels.

The [previous full 30-pipeline record](../matched_postgrid_20261006/README.md) is unchanged. This checkpoint covers one pipeline and two 16-assignment modes, and must not be represented as a fresh full-cohort minimum or median. The restarted latest-main 30-pipeline capture is separate until qualification finishes.

## Reproduction

Use the existing May-style measured figure owner. Run from the repository root; repeat the primary command with `total` in the scope, summary filenames and output directory for total time:

```sh
python paper/figures/build_slas_benchmark.py \
  --summary-source '16 assignments/1 worker=benchmark/results/matched_lastconsumer_20261006/data/16assignments-1worker/execution_summary.csv' \
  --summary-source '16 assignments/4 workers=benchmark/results/matched_lastconsumer_20261006/data/16assignments-4workers/execution_summary.csv' \
  --native-baseline benchmark/results/matched_lastconsumer_20261006/data/16assignments-1worker/execution_summary.csv \
  --scope execution \
  --output-dir paper/figures/slas/matched_lastconsumer_20261006/primary-execution
```

Omit `--native-baseline` and use the distinct `independent-cp-calibration-execution` output directory to reproduce the externally orchestrated calibration. Its labels explicitly identify independent CP processes. Each figure bundle retains source/output checksum provenance, original converter custody and measured clock definitions.

[Primary execution figures](../../../paper/figures/slas/matched_lastconsumer_20261006/primary-execution/measured_execution_caption.md), [primary total figures](../../../paper/figures/slas/matched_lastconsumer_20261006/primary-total/measured_total_caption.md), [execution calibration](../../../paper/figures/slas/matched_lastconsumer_20261006/independent-cp-calibration-execution/measured_execution_caption.md) and [total calibration](../../../paper/figures/slas/matched_lastconsumer_20261006/independent-cp-calibration-total/measured_total_caption.md) are available for manuscript integration. They do not change the current single-well manuscript claim include.

Original lightweight reports, phase receipts, source/environment seals, controllers, converter, terminals and retained-native barrier records are archived. Images and scientific CSV/databases remain at their original captured locations and are not duplicated. Original absolute custody paths remain evidence; the archived manifest is admitted against its original converter SHA256. The native observations were reused only after the benchmark's unchanged actual input/environment/source/storage guards passed.
