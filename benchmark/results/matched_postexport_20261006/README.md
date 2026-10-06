# Actual post-export matched checkpoint,6 October2026

This archive contains **all 30 complete single-assignment workflows and three workflows at nine assignments on one/three workers and sixteen assignments on one/four workers**. Actual runtime source was clean and unchanged `56c3da776ccc12688b4566f7b0c0ef728e6bc7c6`. Each workflow passed warmup and three measured repetitions with all five declared scientific difference inventories empty. Repeated source assignments reuse one biological source sample; they are not independent biological wells. In the serial mode, both engines used one numerical thread and one worker on CPU5. Native observations are genuine fresh serial measurements. The parallel modes use three workers on CPU1/4/5 and four workers on CPU1/2/4/5, with one numerical thread per worker.

The declared cohort retains the prior qualified single-well execution frontier Vitra, total frontier illumination correction Example3, and representative3D monolayer. It is frozen from the original selected manifest (`1085923452648828edc5de64d56b59e7e0e36608bcc4169041777f3112d9adc2`), not reselected after later timing ranks change.

| Workflow | Median OH completed server job | Median OH client total |
|---|---:|---:|
|ExampleVitra|8.755770s|9.206690s|
|ExampleIlluminationCorrection_Example3|1.560411s|1.924041s|
|cp_tutorial_3d_monolayer|26.519159s|28.799471s|

- [Actual9/1 execution summary](data/9assignments-1worker/execution_summary.csv)
- [Actual9/1 total summary](data/9assignments-1worker/total_summary.csv)
- [Original qualification custody](data/9assignments-1worker/summary_custody.json)
- [Exact captured cohort declarations](protocol/selected-three-case-manifest.json)

Execution compares native continuous pipeline execution, including preparation through cleanup, to the complete OpenHCS server job including ordinary exports and metadata publication. Native total covers the measured invocation excluding one-time CPPipe loading/JVM startup; OpenHCS total sums disjoint compile+execute client SUBMIT+WAIT phases. Startup/library/kernel readiness and scientific comparison are outside both scopes. Nested phase timings are retained, not double-counted. RAM is not measured.

For the9/1 capture, all summaries/custody, original native requests/reports, candidate reports, pilot provenance,12 original phase receipts, command, terminal, exact cohort manifest and converter were copied byte-for-byte. Original paths and source identity inside those records remain unchanged. Large images, measurement CSVs and databases are not duplicated; originals remain under `/home/ts/.local/state/openhcs-maintenance/20261006/measured-scaling-current-frontiers-preparation-v1/9assignments-1worker/capture`.

The older [d867 checkpoint](../official30_matched_20261006/README.md) remains explicitly historical and unchanged. The qualified full30 single-assignment, balanced nine-assignment pair, sixteen-assignment pair and actual 1/9/16 single-core amortization figures below use this same source revision.

## Actual matched nine-assignment three-worker comparison

The three-worker capture also terminated0 on clean unchanged56c3 source. All three cases completed warmup and three measured repetitions with all five declared scientific difference inventories empty, nine actual OpenHCS axes and three distinct workers, each owning exactly three axes. Native whole-batch and all three original shard reports passed complete-observation/partition/environment/barrier admission. Native parallel times use their actual simultaneous clocks, not independent-duration maxima.

| Workflow | OH9/1 execution | OH9/3 execution | OH efficiency | CP9/1 execution | CP9/3 execution | CP efficiency |9/3 CP/OH speedup |
|---|---:|---:|---:|---:|---:|---:|---:|
|ExampleVitra|8.755770s|4.542147s|64.256%|24.136220s|9.742642s|82.579%|2.1449×|
|ExampleIlluminationCorrection_Example3|1.560411s|0.873794s|59.526%|3.631126s|2.230507s|54.265%|2.5527×|
|cp_tutorial_3d_monolayer|26.519159s|12.440811s|71.054%|127.803890s|45.977632s|92.657%|3.6957×|

Efficiency compares the same nine repeated assignments: one-worker median divided by three times the three-worker median. Every OpenHCS result loses more than the accepted approximately15%; this checkpoint does not satisfy that target. CellProfiler speedup is a separate comparison against each engine's measured three-worker execution and must not be substituted for OpenHCS parallel efficiency.

- [Actual9/3 execution summary](data/9assignments-3workers/execution_summary.csv)
- [Actual9/3 total summary](data/9assignments-3workers/total_summary.csv)
- [Original9/3 custody](data/9assignments-3workers/summary_custody.json)

The lightweight archive includes original shard requests/reports, collection/equivalence and exact barrier markers admitted by the native owner, plus original candidate receipts and whole reports. Each was copied byte-for-byte and checked against custody. The paired figures use measured observations; no projected timing or memory result is supplied.

### Qualified paired figures and caption

- [Actual9/1 versus9/3 execution](../../../paper/figures/slas/matched_postexport_20261006/matched-nine-execution/measured_execution_seconds.png)
- [Actual9/1 versus9/3 total](../../../paper/figures/slas/matched_postexport_20261006/matched-nine-total/measured_total_seconds.png)

**Caption:** Actual matched nine-assignment execution and prepared-service total times, comparing one worker (`9/1`) with three workers (`9/3`). The cohort retains the prior single-well timing frontiers and representative3D workflow; assignments reuse one biological source sample. Bars show independent engine medians over three measured repetitions after warmup on the same56c3 source. Native parallel bars derive genuine simultaneous shard clocks; OpenHCS execution includes the whole server job and plate exports. Native total excludes one-time CPPipe loading/JVM startup while OH total includes per-job compilation; readiness and scientific comparisons are excluded. The Average row is an arithmetic presentation summary, not another observed workflow. Figures use the existing May-style owner and retain complete source/output hash provenance. Its shared grouped-chart style places method legends outside the bar domain, so tall bars cannot obscure method identities. The nine-assignment comparison does not meet the 15%-loss threshold.

The CP efficiencies in the preceding matched-mode table compare native serial timings from the9/1 capture with native parallel timings from the9/3 capture. Separately, the9/3 capture also retains a genuine whole-batch serial native baseline, used to qualify its shards. Its **within-capture** physical efficiencies are:

| Workflow | Serial CP inside9/3 capture | Parallel CP9/3 | Within-capture CP efficiency |
|---|---:|---:|---:|
|ExampleVitra|23.080005s|9.742642s|78.966%|
|ExampleIlluminationCorrection_Example3|3.277442s|2.230507s|48.979%|
|cp_tutorial_3d_monolayer|123.242523s|45.977632s|89.350%|

These efficiencies differ from the cross-capture82.579/54.265/92.657% figures above because they use different genuine serial observations. Neither native comparison establishes OpenHCS efficiency or biological replication.

## Qualified all30 single-assignment checkpoint

All30 original workflows completed warmup and three measured repetitions on clean unchanged56c3 source. Every declared CSV, database, image and output-inventory comparison was empty. Existing native complete-observation, original input and CPU/storage/environment guards admitted the genuine native reference observations; none was projected or retimed. One selected source sample, one worker and one numerical thread were used per workflow.

Execution speedup has a **minimum of2.8641569× and median of4.3600681×**. The weakest execution result is ExampleTrackObjects: native continuous pipeline execution8.4006380s versus the full OpenHCS server job2.9330230s. Prepared-service total speedup has a **minimum of1.3994865× and median of3.3009166×**; illumination correction Example3 is weakest. All30 execution ratios exceed2× and all30 total ratios exceed native parity. The three total ratios below2× are illumination correction Example3, CombineObjects and PercentPositive.

- [Actual all30 execution summary](data/singlewell/execution_summary.csv)
- [Actual all30 total summary](data/singlewell/total_summary.csv)
- [Original all30 qualification custody](data/singlewell/summary_custody.json)
- [Captured full30 declarations](protocol/singlewell/original-full30-manifest.json)
- [Execution distribution](../../../paper/figures/slas/matched_postexport_20261006/execution/measured_execution_speedup_cumulative_distribution_log.png)
- [Total distribution](../../../paper/figures/slas/matched_postexport_20261006/total/measured_total_speedup_cumulative_distribution_log.png)

The all30 lightweight archive retains byte-identical summaries/custody, command/terminal/full manifest, original native requests/reports, candidate reports, pilot provenance and all120 warmup/measured phase receipts. The same exact converter source is retained in protocol/. No scientific images, measurement CSVs or databases are duplicated. Originals remain under `/home/ts/.local/state/openhcs-maintenance/20261006/final-official30-singlewell-matched-v16`; retained native reports continue to declare their original observation locations. The figures consume the repo archival CSV through the existing May-style measured owner and retain exact input/output digests and original custody.

Compared with the separately retained d867 checkpoint, the observed execution median changed from4.2127485× to4.3600681× and the total median from3.2624316× to3.3009166×. These are two dated complete observations, not a causal isolated-patch comparison. The nine-assignment cohort remains the prior frontiers plus representative3D, regardless of the new weakest all30 result. The fixed cohort is shared by the actual 1/9/16 single-core panel. Parallel-efficiency acceptance remains unresolved.

## Qualified sixteen-assignment comparison

All three workflows completed warmup plus three observed repetitions at sixteen assignments on one and four workers. All scientific and output-inventory differences are empty. Whole-batch and four simultaneous native shard reports passed their existing complete-observation, assignment, environment and barrier checks. Source and input custody remained unchanged.

| Workflow | OH16/1 execution | OH16/4 execution | OH execution efficiency | CP/OH16/4 execution | CP/OH16/4 total |
|---|---:|---:|---:|---:|---:|
|ExampleVitra|16.588015s|7.496244s|55.321%|1.9348×|1.7906×|
|ExampleIlluminationCorrection_Example3|2.786619s|1.116406s|62.402%|2.2197×|1.4711×|
|cp_tutorial_3d_monolayer|48.900777s|17.608818s|69.427%|4.1448×|3.4162×|

Execution efficiency is the one-worker median divided by four times the four-worker median for the same sixteen assignments. All three results miss the approximately 15%-loss threshold. The Vitra four-worker execution ratio also falls below 2×; the all30 single-assignment headline must not be generalized to this workload.

The native four-worker capture also measures a serial whole-batch reference. Its within-capture physical efficiencies are 65.644% (Vitra), 60.310% (illumination) and 79.54% (3D). These describe native scaling, separately from OpenHCS efficiency and from the matched CP/OH ratios.

- [Actual16/1 execution](data/16assignments-1worker/execution_summary.csv) and [total](data/16assignments-1worker/total_summary.csv).
- [Actual16/4 execution](data/16assignments-4workers/execution_summary.csv), [total](data/16assignments-4workers/total_summary.csv) and [original qualification custody](data/16assignments-4workers/summary_custody.json).
- [Matched sixteen-assignment execution figure](../../../paper/figures/slas/matched_postexport_20261006/matched-sixteen-execution/measured_execution_seconds.png) and [total figure](../../../paper/figures/slas/matched_postexport_20261006/matched-sixteen-total/measured_total_seconds.png).
- [Actual 1/9/16 single-core amortization](../../../paper/figures/slas/matched_postexport_20261006/single-core-amortization/measured_single_core_amortization.png).

Original lightweight reports, requests, progress, phase receipts, command and terminal records are retained byte-for-byte. Scientific images, measurement CSVs and databases remain at their captured original locations. Every panel retains its source/output hashes and original timing/science custody. Connecting lines in the amortization panel are guides between measured points; they do not estimate unobserved assignment counts.
