# Actual post-export matched checkpoint,6 October2026

This archive contains **all30 complete single-assignment workflows and three complete9-assignment workflows on one and three workers**. The16-assignment captures are pending. Actual runtime source was clean and unchanged `56c3da776ccc12688b4566f7b0c0ef728e6bc7c6`. Each workflow passed warmup and three measured repetitions with all five declared scientific difference inventories empty. Nine repeated source assignments reuse one biological source sample; they are not independent biological wells. In the serial mode, both engines used one numerical thread and one worker on CPU5. Native observations are genuine fresh serial measurements. The parallel mode uses three actual workers on CPU1/4/5, with one numerical thread per worker.

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

The older [d867 checkpoint](../official30_matched_20261006/README.md) remains explicitly historical and unchanged. Actual16/1 and16/4 data are pending; the new single-assignment full30 data are qualified below. No pair or amortization figure is rendered until its corresponding captures fully qualify on the same source head.

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

The lightweight archive includes original shard requests/reports, collection/equivalence and exact barrier markers admitted by the native owner, plus original candidate receipts and whole reports. Each was copied byte-for-byte and checked against custody. No final amortization figure,16-assignment row, projected timing or memory result has been fabricated.

### Qualified paired figures and caption

- [Actual9/1 versus9/3 execution](../../../paper/figures/slas/matched_postexport_20261006/matched-nine-execution/measured_execution_seconds.png)
- [Actual9/1 versus9/3 total](../../../paper/figures/slas/matched_postexport_20261006/matched-nine-total/measured_total_seconds.png)

**Caption:** Actual matched nine-assignment execution and prepared-service total times, comparing one worker (`9/1`) with three workers (`9/3`). The cohort retains the prior single-well timing frontiers and representative3D workflow; assignments reuse one biological source sample. Bars show independent engine medians over three measured repetitions after warmup on the same56c3 source. Native parallel bars derive genuine simultaneous shard clocks; OpenHCS execution includes the whole server job and plate exports. Native total excludes one-time CPPipe loading/JVM startup while OH total includes per-job compilation; readiness and scientific comparisons are excluded. The Average row is an arithmetic presentation summary, not another observed workflow. Figures use the existing May-style owner and retain complete source/output hash provenance. Its shared grouped-chart style places method legends outside the bar domain, so tall bars cannot obscure method identities. No final amortization, unmeasured16-assignment point or15%-loss acceptance is claimed.

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

Compared with the separately retained d867 checkpoint, the observed execution median changed from4.2127485× to4.3600681× and the total median from3.2624316× to3.3009166×. These are two dated complete observations, not a causal isolated-patch comparison. The nine-assignment cohort remains the prior frontiers plus representative3D, regardless of the new weakest all30 result. No final16-assignment amortization or accepted parallel-efficiency claim is made.
