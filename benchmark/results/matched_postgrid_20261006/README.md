# Matched benchmarks on eb773573c

This is the final current manuscript record designated after the five fresh captures qualified on production source `eb773573cced496fe5ee7bfeef7b961674958c1d`. It contains the original 30 authored pipelines on one assignment/one worker and the unchanged selected-three cohort on 9/1, 9/3, 16/1 and 16/4. Every case completed a warmup and three measured repetitions with all declared-output, database, CSV, image and inventory difference lists empty. Source, inputs, complete retained-native observations, physical clocks and original-output custody passed. Controllers ended at the same clean source revision. The earlier [e905 checkpoint](../matched_final_20261006/README.md) remains unchanged.

All five captures used the same refreshed environment and rebuilt native binaries. The exact installed startup-reader dependency revision and package/binary records are retained in [the environment evidence](protocol/environment/zmqruntime-installed-source.json). Earlier first-environment captures and the failed startup attempt are historical evidence, not inputs to these summaries. Repeated assignments execute the same selected biological sample independently; they are not additional biological samples. The selected cohort retains prior v15 frontiers (Vitra and illumination Example 3) plus the representative 3D monolayer pipeline, not the latest single-well ranking. [Original command and manifest custody](protocol/singlewell/command.json) retains the actual declarations.

## Single-assignment measurements

Across all 30 pipelines, execution speedup over actual native CellProfiler has minimum **2.785×** and median **4.264×**. Compile-plus-run total speedup has minimum **1.348×** and median **3.338×**. All execution results exceed 2× and all total results exceed parity; 3 total results are below 2×. ExampleTrackObjects is weakest on execution; illumination Example 3 is weakest on total. These prose values describe this record; the manuscript's numeric spans derive from the qualified CSV/custody through the existing publication owner.

[Execution summaries](data/singlewell/execution_summary.csv), [total summaries](data/singlewell/total_summary.csv) and [qualification custody](data/singlewell/summary_custody.json) retain exact durations and evidence references.

## Matched worker comparisons

Execution efficiency is `T(N,1)/(p*T(N,p))`, with the same number of assignments and source for both observations. Loss versus ideal is `1-efficiency`. Additional loss relative to native is `1-(OH efficiency/CP efficiency)`; a negative value means OpenHCS scales better. Total efficiency uses the corresponding total clocks separately. Native serial denominators below come from the matching single-worker capture, while native parallel medians are actual simultaneous shard makespans, not projections or the different serial baseline embedded in a parallel capture.

### 9 assignments: one versus 3 workers

| Pipeline | OH serial execution (s) | OH parallel execution (s) | OH execution efficiency | Native execution efficiency | Additional loss relative to native | Parallel execution / total speedup over native |
|---|---:|---:|---:|---:|---:|---:|
| ExampleVitra | 8.959977 | 3.954952 | 75.52% | 82.58% | 8.55% | 2.463× / 2.206× |
| ExampleIlluminationCorrection_Example3 | 1.568722 | 0.723104 | 72.31% | 54.26% | -33.26% | 3.085× / 2.025× |
| cp_tutorial_3d_monolayer | 27.118808 | 12.142256 | 74.45% | 92.66% | 19.65% | 3.787× / 3.374× |

[Exact execution and total denominators and efficiencies](matched-nine-efficiency.json) retain both definitions. These measured conditions do not establish ideal linear scaling.

### 16 assignments: one versus 4 workers

| Pipeline | OH serial execution (s) | OH parallel execution (s) | OH execution efficiency | Native execution efficiency | Additional loss relative to native | Parallel execution / total speedup over native |
|---|---:|---:|---:|---:|---:|---:|
| ExampleVitra | 16.247885 | 5.656813 | 71.81% | 67.38% | -6.56% | 2.564× / 2.319× |
| ExampleIlluminationCorrection_Example3 | 2.821338 | 1.020210 | 69.14% | 64.46% | -7.26% | 2.429× / 1.526× |
| cp_tutorial_3d_monolayer | 50.524603 | 17.043156 | 74.11% | 84.20% | 11.98% | 4.282× / 3.774× |

[Exact execution and total denominators and efficiencies](matched-sixteen-efficiency.json) retain both definitions. These measured conditions do not establish ideal linear scaling.

## Single-core amortization and limits

Actual one-worker points at 1, 9 and 16 repeated assignments show execution and total time per assignment. Nonexecution overhead is the median paired difference `(total - server execution)/assignment_count`, including compilation and client coordination; it is not a fabricated kernel/plumbing split. Compilation amortizes while execution per assignment can still rise. Connecting lines do not predict unmeasured workload sizes.

The 3D workflow has additional scaling loss relative to native: approximately 19.7% at three workers and 12.0% at four workers for execution. The [same-step passive counter comparison](diagnostics/3d-same-step-scaling-counter-comparison.json) finds 3.39–3.66 s of additional work within the critical four-assignment lane, with only 25–33 ms outside steps. Its sampled system-time increase has lower bounds of 1.61–2.04 s and user-time increase 0.75–1.00 s. Serial 3D had zero process swap and major faults; parallel mapped processes reached roughly 0.4–0.55 GiB of anonymous process swap each, with hundreds or thousands of major faults. Swap onset occurred during measured repetition 0's third assignments, at steps 17–21. Process RSS or swap ranges must not be summed as unique physical memory. These observations support a working-set/reclaim contribution, but do not establish the responsible allocation owner, transparent-huge-page causality or a guaranteed fix. CPU0 sampled external process counters at 100 ms, with status at one second; no profiler was attached and no runtime hook was changed. Serial observation missed its initial two minutes but covered all 3D jobs. Host capacity was approximately 15 GiB without an imposed cgroup memory maximum/high limit; later free-memory readings and historical session-wide peak memory are not benchmark-specific pressure proof.

The [separate TrackObjects allocation-policy comparison](diagnostics/passive-policy-comparison.json) did not reproduce the earlier default-policy spike and saved only about 34 ms, below the admitted material threshold. It was inconclusive and did not justify a production change. It is not substituted for this record's timings.

Original joined passive-counter inputs remain at captured locations; their exact SHA256 values are retained here for custody, without copying large raw process samples:

- `/home/ts/.local/state/openhcs-maintenance/20261006/scaling-passive-kernel-observation-v2/16-1-step-counter-join.json`: `60e8694caf1bc5b0b601dd3e326af55b9270a631967b1015b952c05c3321b65f`.
- `/home/ts/.local/state/openhcs-maintenance/20261006/scaling-passive-kernel-observation-v2/16-4-step-counter-join.json`: `d44854beadb45a00c4f487288b507aa8f212a37212e630ecce5af2e36f606e2c`.

## Clocks and immutable evidence

OpenHCS execution is the complete `SERVER_PIPELINE_JOB`, including plate exports and finalization. Total sums disjoint compile and execute client submit/wait phases. Native execution is continuous pipeline execution including preparation, modules and post-run; native total is the prepared invocation. One-time CPPipe loading, JVM initialization, endpoint/catalog/kernel readiness and subsequent scientific comparison are outside both clocks. RAM was not measured in these benchmark figures.

[Lightweight original reports and phase receipts](reports/singlewell/ExampleVitra/candidate_report.json) and [commands, terminals, manifests and converter](protocol/singlewell/command.json) are byte-identical copies. Original native requests retain their actual input/output paths; their original reports and barrier records are archived under each case's `original_native/` directory. No timing, scientific record or original custody path was rewritten. Scientific images, measurement CSVs and databases remain at captured original locations and are not duplicated here. Progress CSVs are timing evidence.

The current [composite Figure 2 and derived manuscript claim provenance](../../../paper/figures/slas/benchmark-publication/figure2_provenance.json) and [single-core amortization provenance](../../../paper/figures/slas/matched_postgrid_20261006/single-core-amortization/figure2_provenance.json) use the existing measured May-style figure owner. No projected native timing or unmeasured RAM panel is included.
