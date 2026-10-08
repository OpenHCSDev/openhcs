---
bibliography: ../openhcs_references.json
csl: ../styles/elsevier-vancouver.csl
reference-section-title: References
link-citations: true
link-bibliography: true
---

# OpenHCS supplementary material

Development history and full instructions are kept in the [archived supplementary source](editorial_history_20261007.md). Measurement tables, pipelines and input evidence remain linked below.

## Supplementary Figure 1. Runtime composition and preparation

![Array grouping, named results, scheduling and preparation.](../figures/slas/supp_workflow_infrastructure.png){width=4.8in}

::: {custom-style="ImageCaption"}
(I, A–D) Array axes and groups supply image views to per-plane, stack or stack-reduction functions. Named labels remain available to later measurements; sequential timepoints complete in order while wells can run in parallel. (II) Compiled plans, prepared functions and a worker map form the execution bundle. The [figure assembly and interface records](#figure-assembly-and-interface-records) link the source artwork; main Figures 1–2 show the native workflow and process topology.
:::

## Supplementary Figure 2. Translocation response and compartment eligibility

![Full-plate eligibility fractions and independent held-out translocation endpoints.](../figures/slas/supp_translocation.png){width=5.7in}

::: {custom-style="ImageCaption"}
(A–B) Eligible-nucleus fractions in 96 BBBC013 wells, including four development wells. Dots show four wells per dose; marks and whiskers show their mean and sample SD. Main Figure 4E shows the response curves. (C–D) An earlier independent held-out trial used mean cell-level GFP ratios, with four wells per control condition. The two trials used different well summaries: mean GFP ratio and median log2 ratio. Supplementary Data 7–8 give the methods and source data.
:::

## Supplementary Figure 3. Nuclear-instance evaluation and object separation

![Independent-author scores and prospective held-out assays.](../figures/slas/supp_nuclear_instances.png){width=5.7in}

::: {custom-style="ImageCaption"}
(I, A–B) Final BBBC039 segmentations from two independent authors on 200 fields, with pooled object F1 of 0.898 and 0.906 at intersection over union ≥ 0.5. (II, A–B) Earlier prospective BBBC039 F1/Dice on 50 held-out fields and BBBC007 boundary support on 12. Each trial used four development fields. Boundary support is the fraction of predicted boundary pixels within two pixels of a manual outline. Supplementary Data 7–8 provide counts and per-field scores.
:::

## Supplementary Figure 4. Independent morphology checks and remaining ambiguities

![Independent orthogonal localisation, retinal borders and unsupported body growth.](../figures/slas/supp_morphology_checks.png){width=5.4in}

::: {custom-style="ImageCaption"}
(A–C) Nuclear centres from an independent volume analysis in XY, XZ and YZ. (D–F) Retinal border region shown raw, with first and final outlines; a possible split remains at display window 0–42, gamma 1. (G–I) A faint DNA pair remains merged at window 0–151. (J–L) A nuclear seed lacks actin-supported body growth at window 0–104, gamma 1. The panels show separate trials; colours identify objects within each image. Supplementary Data 8 links the source captures and matching records.
:::

## Supplementary Figure 5. Laboratory treatment responses compared with MetaXpress

![Five additional well-level morphology responses to FC-A and Y27632 after assisted repair.](../figures/slas/supp_neurite_treatment_endpoints.png){width=5in}

::: {custom-style="ImageCaption"}
(A–B) Detected cells; (C–D) total outgrowth; (E–F) branches per cell; (G–H) mean cell process length; (I–J) mean cell median process length. Twenty matched wells were analysed after assisted repair. Each curve is normalized to its own DMSO mean; dots show two technical wells per dose and whiskers their sample SD. Mean outgrowth per detected cell is included in the linked six-endpoint sheet.
:::

### Treatment evaluation and endpoint definitions

For the laboratory neurite comparison, we applied the frozen recipe settings
to nine fields in each of 20 FC-A and Y27632 wells using the current production
backend. An evaluation-only source key linked coded inputs to physical wells.
Each well's endpoint was the unweighted mean of nine field-level measurements:
outgrowth per detected cell, cell count, total outgrowth, branches per cell,
and mean and median process length. For the last two endpoints, we first
averaged the corresponding per-cell values within each field, including
zero-growth cells. Overlapping fields were not deduplicated; total outgrowth
therefore denotes a mean field total, not unique whole-well length. Treatment means
were divided by the same drug curve's zero-dose DMSO mean, with two technical
wells at each concentration. Existing MetaXpress well exports supplied the
comparison response, not manual tracing truth. This fixed-recipe transfer was
separate from autonomous pipeline authoring.

We retained these predictions when subsequent visual inspection identified
shafts included in soma masks, spurious soma-edge branches and supported paths
lost during tracing. Repairs informed by those external observations were
evaluated separately as assisted development, not autonomous authoring. The
comparison retained the same channels, pixel calibration, field sampling and
well aggregation. Matched raw-image, soma-mask and path views were used to
check recovered shafts and genuine branches alongside unsupported routes;
agreement with MetaXpress fold changes was not a tuning criterion.

The commercial export contains 120 well summaries from two plates. The repaired run used DAPI w1 and calcein w2, declared XY spacing 1.3556 µm per pixel, neurite response 30 and candidate admission 0.03. The completed 180-field evaluation used repaired ownership propagation and branch counting; detected-cell counts were unchanged in every field relative to the preceding assisted checkpoint. That comparison concerns the latest ownership/junction fix.

Each FC-A and Y27632 concentration has two technical wells. Y27632 is labelled Y27 in the export. The [six-endpoint sheet](../figures/slas/personal_neurite_effects_repaired.png) includes mean outgrowth per detected cell and the endpoints in Supplementary Figure 5.

Every endpoint is divided by the same drug
curve's DMSO mean. Dots show the two technical
wells at each concentration. Marks and whiskers show their mean and sample
standard deviation after division by the observed control mean; they do not
propagate uncertainty in that denominator or represent confidence intervals.
Dose positions are equally spaced for display, not a fitted concentration–response
model. Paired treatment panels use the same vertical scale. The plot and
numerical tables are generated from the same well measurements.

Each OpenHCS well endpoint is the unweighted mean of its nine field-level
measurements. Total outgrowth is therefore a mean field total, not unique
whole-well length.
The commercial endpoint is an existing well export whose exact site weighting
and software settings are not retained. The
[MetaXpress 6 Neurite Outgrowth guide](https://www.moleculardevices.com/sites/default/files/en/assets/training-material/dd/img/metaxpress-6-software-application-modules-neurite-outgrowth.pdf)
defines total outgrowth in micrometres with diagonal-length correction, primary
processes as outgrowths attached to cell bodies, and branches as branching
junctions rather than daughter-process counts. It does not specify how the
module distinguishes crossings from branches. These documented definitions
do not establish identical segmentation or topology for the retained export;
absolute lengths and counts are not treated as equivalent.
Within-method ratios avoid a constant unit conversion but do not remove those
measurement differences. Neither method is manual ground truth, and two
technical wells do not establish biological replication or significance.

OpenHCS process lengths describe the connected paths assigned to a
soma-adjacent root, including daughter branches, rather than individual
segments between graph junctions. Per-cell mean and median process lengths
are averaged within each field, including zero-growth cells, then across its
nine fields. Branches require at least three same-neuron paths and distinct
admitted image arms around the junction. Paths sharing one image corridor
and graph stars confined within a foreground cap do not add branch events;
resolved crossings are not automatically branches. These
definitions specify the OpenHCS measurements without asserting that the
commercial algorithm uses identical topology or aggregation.

The [joined physical-well table](personal_neurite_repaired_morphometry/joined_wells.csv)
and [treatment-effect table](personal_neurite_repaired_morphometry/treatment_effects.csv)
retain well identities, means, sample standard deviations, counts, raw deltas,
fold changes and fractional-change differences. Cell-count changes accompany
outgrowth to expose denominator changes without inferring toxicity. The
[source hashes](personal_neurite_repaired_morphometry/source_evidence.json) identify the
exact submitted pipeline, source key, commercial export and all 180 native
summaries. The comparison script processes tables only and does not tune images.
Overlapping fields are not deduplicated, so averaged field counts are not unique
whole-well neuron counts. Unselected wells are not filled with zero.
The [original frozen comparison](personal_neurite_baseline_morphometry/treatment_effects.csv)
is retained separately for before/after evaluation; it was not overwritten.

Additional [branch and primary-process totals](personal_neurite_branch_diagnostics/joined_wells.csv)
and their [treatment responses](personal_neurite_branch_diagnostics/treatment_effects.csv)
test whether smaller estimated branching fold changes are explained by the cell denominator.
At 40 µM, total-branch fold changes are 1.65 versus 3.01 for FC-A and 1.73
versus 3.03 for Y27632 (OpenHCS versus MetaXpress). Branches per primary
process likewise give smaller estimated fold changes: 1.31 versus 2.48 and 1.29 versus
2.23, respectively. The difference therefore persists without a cell-count
denominator. OpenHCS totals are means of field totals, and its branch/process
endpoint is the mean of the nine field ratios. The commercial comparison
uses ratios of exported well totals; its internal site weighting and primary
process definition remain unspecified. These diagnostic ratios are not proof
of equivalent topology or of which method is more accurate. Their
[source record](personal_neurite_branch_diagnostics/source_evidence.json)
identifies the same completed assisted evaluation, not an additional autonomous trial.

### Assisted transfer results

Following externally informed repairs, analysis of all 180 fields in 20 matched
wells recovered increasing outgrowth-per-cell responses to FC-A and Y27632
(Figure 5; Supplementary Figure 5). At 40 µM, OpenHCS fold changes were
1.77 and 1.76, respectively, versus MetaXpress's 1.98 and 2.05. Total-outgrowth
estimated fold changes were also smaller. Branches-per-cell fold changes were 1.65 versus
3.00 for FC-A and 1.82 versus 3.26 for Y27632. OpenHCS control branch counts
per cell were approximately 10–11% higher, but treated counts were 38–39%
lower. Cell counts were unchanged in all 180 fields across the latest
ownership/junction fix relative to the preceding assisted checkpoint;
the difference persisted in total branches and branches per primary process.
Control excess alone therefore does not explain the smaller estimated branching fold changes. Remaining
branch recall, assignment and measurement-definition differences cannot be
separated without spatial ground truth. Both methods recovered concordant
positive outgrowth responses with different measured magnitudes. This is an
assisted-development evaluation, separate from autonomous authoring.

## Supplementary Figure 6. Total speedup by workflow and assigned sample count

![Total speedups for each workflow, revision and worker configuration on linear and logarithmic axes.](../figures/slas/benchmark-publication/assignments/assignment_total_speedups.png){width=4.8in}

::: {custom-style="ImageCaption"}
(A1–A2) Illumination correction Example 3; (B1–B2) Vitra; (C1–C2) 3D monolayer.
Columns use linear and logarithmic axes. Points are CellProfiler/OpenHCS median
total-time ratios over three repetitions. Colour identifies revision; shape
identifies worker count. Lines join matched configurations. Supplementary Data 3
gives the protocol and numerical tables.
:::

## Supplementary Figure 6 (continued). Matched worker comparisons

![Matched one- versus two-, three- and four-worker comparisons, retaining separate capture revisions.](../figures/slas/supp_worker_comparisons.png){width=5in}

::: {custom-style="ImageCaption"}
**(A)** Eight assignments of three workflows on revision `d8678dbd4`: one versus
two OpenHCS workers. (B) Nine assignments of the same three workflows on
revision `71aded26c`: one versus three OpenHCS workers. Within each row,
execution and compile-plus-run total are separate groups. Each dot is one
workflow's ratio against one stock CellProfiler process on the same assignments.
Bars give arithmetic means, black lines medians, and annotations the minimum,
median, mean and maximum. Each row uses its own revision and cohort. (C)
Sixteen assignments of 3D monolayer on revision `2cda84a369`: one versus
four OpenHCS workers. There is one workflow, so minimum, median, mean and
maximum coincide and are marked “all”. Supplementary Data 3 gives the protocol
and source tables.
:::

## Supplementary Figure 6 (continued). Individual workflow runtimes

![Paired execution and total runtime for all thirty workflows.](../figures/slas/benchmark-publication/measured_benchmark_workflow_runtimes.png){width=6in}

::: {custom-style="ImageCaption"}
**(A)** Execution; **(B)** compile-plus-run total. Paired bars show median CellProfiler
and OpenHCS durations for each of the thirty workflows in main Figure 6, with
one worker and one numerical thread. Both panels use the same logarithmic
seconds scale. Row annotations give CellProfiler/OpenHCS ratios of engine medians from three measured
repetitions. All thirty workflows passed their declared-output comparisons.
:::

The [linear-scale aggregate view](../figures/slas/benchmark-publication/measured_benchmark_publication.png)
shows the same aggregate measurements on linear axes.

## Supplementary Table 1. Reusable libraries and their roles

| Library | Role in OpenHCS |
| --- | --- |
| [metaclass-registry](https://github.com/OpenHCSDev/metaclass-registry) | Discovers classes implementing a shared interface and makes them available for selection. |
| [python-introspect](https://github.com/OpenHCSDev/python-introspect) | Reads a function's parameters, types, defaults and documentation. |
| [ObjectState](https://github.com/OpenHCSDev/objectstate) | Tracks editable settings and resolves shared defaults and local overrides. |
| [pyqt-reactive](https://github.com/OpenHCSDev/pyqt-reactive) | Generates parameter controls and updates them as settings change. |
| [pycodify](https://github.com/OpenHCSDev/pycodify) | Generates editable Python representations and manages their imports. |
| [ArrayBridge](https://github.com/OpenHCSDev/arraybridge) | Converts arrays between supported libraries and manages their computational resources. |
| [PolyStore](https://github.com/OpenHCSDev/PolyStore) | Reads, writes and streams data through supported storage interfaces. |
| [ZMQRuntime](https://github.com/OpenHCSDev/zmqruntime) | Coordinates communication, startup, shutdown and progress between processes. |

## Supplementary Data 1. CellProfiler workflow comparison



### Import, export and comparison methods

Imported `ExportToDatabase` modules run once per plate after image-group processing. They collect the selected images, objects, measurements, relationships, thumbnails and grouping information into CellProfiler Analyst tables [@Jones2008]. The export produces a self-contained SQLite database and matching `.properties` files. Non-SQLite databases, custom filter rows, `.workspace` generation and some historical aggregation settings remain unsupported; unsupported requests fail or are identified in the compatibility documentation.

The OpenHCS 0.8.5 [release test](ci_official30_085/README.md) preceded the unified 30-workflow value comparison below.

The subsequent matched performance evaluation retained the complete 30-workflow manifest and compared the declared table, database and image outputs in a warmup and three measured repetitions per engine. All 120 OpenHCS observations completed without declared-output differences against complete native CellProfiler runs. These current-source observations, their output inventories and their timing boundaries are separate from the historical release comparison and are retained in the [minimum-threefold integrated-main matched benchmark record](../../benchmark/results/matched_min3_integrated_main_20261007/README.md).

For the five workflows without file exports, terminal image or object-label exports were appended while preserving the original processing modules and settings. Native CellProfiler generated eight additional reference artifacts. A subsequent unified run compiled and executed all 30 workflows afresh and compared each candidate with its selected native reference values. Object labels were compared exactly after singleton-axis normalization; numerical images used the stated float tolerances. The unified run used OpenHCS 0.8.5 current source on Python 3.12.3 with NumPy 2.1.3 and SciPy 1.18.1. Native references used CellProfiler 4.2.8.1 on Python 3.9.25 with NumPy 1.24.4 and SciPy 1.9.0. Supplementary Data 1 links the export definitions, reference inventory, per-workflow comparisons and exact source identities separately from the historical release CI records.

The corpus contains 22 workflows and associated image sets from the official CellProfiler 3 examples repository, seven workflows and image sets from the official CellProfiler tutorials repository, and one workflow from the supplement to the CellProfiler 4 performance study [@CellProfilerExamples; @CellProfilerTutorials; @Stirling2021]. The CellProfiler project and the cited dataset contributors retain authorship and provenance for these materials. The retained manifest maps workflow names to pipeline and image locations; Supplementary Data 1-3 provide the corresponding comparison, coverage and throughput tables.


This supplement indexes source tables and evaluation records. Figure scripts
derive panels and plotted-row exports from the linked files; paths are relative
to this file.

The acquisition scripts pin the official CellProfiler examples to
`4972b59e670a4ae96c3d453803c92eeff378d054`, the official tutorials to
`264a8155da21a2d468051f78211bed2e580a8934`, and the CellProfiler 4 benchmark
supplement to `40abc2e600fd46b74c213999dd25c5245048dc92`.



### Unified 30-workflow value comparison

The [unified evidence directory](../../benchmark/results/official30_unified_value_comparison_20260916/README.md)
preserves one immutable run in which all 30 workflows were compiled and executed
afresh through isolated ZMQ execution endpoints. All 30 selected reference-value
comparisons were equivalent and reported zero differences. Its fresh
[reference inventory](../../benchmark/results/official30_unified_value_comparison_20260916/reference_inventory.csv)
contains 21 CSV profiles, three SQLite profiles and six image- or array-only
profiles. Image comparison executed for seven workflows, including the completed
translocation overlay compared alongside its SQLite values.

The [observations](../../benchmark/results/official30_unified_value_comparison_20260916/observations.csv),
[phase timings](../../benchmark/results/official30_unified_value_comparison_20260916/phase_timing.csv),
and [summary](../../benchmark/results/official30_unified_value_comparison_20260916/summary.csv)
retain the comparison results. The original observations identify the candidate
as OpenHCS 0.8.5 and retain endpoint, executable and submitted-pipeline provenance.
The original run environment was not recorded in this bundle; versions from later runs cannot supply it.

### Five-workflow image and object-label exports

Five source workflows compute images or objects without exporting files. The
[export-extension manifest](../../benchmark/manifests/official30_value_completion_20260914.json)
selects versions of those workflows with terminal exports added. Its generated
pipelines retain the original processing modules and settings. Native CellProfiler
produced the exported references; OpenHCS processed the same scoped inputs.

| Workflow | Exported values compared | Result |
| --- | --- | --- |
| Combine objects | Combined-object labels | Exact label agreement |
| Translocation starter | Nuclear labels | Exact label agreement |
| Illumination Example 1, EachMethod | Corrected green image | Float-tolerance agreement |
| Illumination Example 2 | Uncorrected, small-block-corrected and large-block-corrected nuclear labels | Exact agreement for all three label images |
| Illumination Example 3 | Polynomial-corrected and convex-hull-corrected images | Float-tolerance agreement for both images |

The [per-artifact comparison table](../../benchmark/results/official30_value_completion_20260914/label_aware_exact_commit_run/artifact_comparisons.csv)
records eight passing artifacts. All five integer label images agree exactly
after normalization of singleton dimensions. The three numerical images have
zero pixels outside the absolute and relative tolerances of `1e-6`; their
maximum absolute difference is `2.9802322387695312e-8`. The
[per-workflow observations](../../benchmark/results/official30_value_completion_20260914/label_aware_exact_commit_run/observations.jsonl)
link these comparisons to fresh candidate executions and the retained native
outputs.

The [run environment](../../benchmark/results/official30_value_completion_20260914/label_aware_exact_commit_run/run_environment.json)
identifies OpenHCS execution source `7ca8ecb8e73a882ef0f15616d57b00f0dabf73e0`,
Python 3.12.3, NumPy 2.1.3 and SciPy 1.18.0. Native references were generated
with CellProfiler 4.2.8.1 on Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0.
Each candidate ran through a fresh matching OpenHCS endpoint. Source revisions,
native-reference origin and endpoint identities are retained with the results.
These exported references are incorporated into the unified 30-workflow run;
the earlier five-workflow audit and release records retain their own protocols
and identities.



## Supplementary Data 2. Archived CellProfiler coverage

- [Module names and associated workflows](../../benchmark/results/labmeeting_20260513/official30_well_throughput/figures/module_coverage_cppipe_modules.csv).
- [Individual settings and recorded handling categories](../../benchmark/results/labmeeting_20260513/official30_well_throughput/figures/module_coverage_cppipe_settings.csv).
- [Processing registration and corpus membership](../../benchmark/results/labmeeting_20260513/official30_well_throughput/figures/module_coverage_absorbed_modules.csv).

These files describe the archived coverage report. Setting categories distinguish
bound parameters, artifact contracts, infrastructure, and intentionally ignored
settings. Registration or a handling category is not itself an output-equivalence
test. Module aliases and source/export roles differ between the tables, so their
category totals must not be added as mutually exclusive classes. They are not a
current-version compatibility matrix.

## Supplementary Data 3. Worker measurements

### Measured panels and numerical tables

- [Current aggregate speedups, logarithmic view](../figures/slas/benchmark-publication/measured_benchmark_publication_log.png), using the same thirty workflows as main Figure 6 and the paired-runtime continuation of Supplementary Figure 6.
- [Every plotted assignment-count observation](../figures/slas/benchmark-publication/assignments/assignment_total_speedups.csv), including exact source revision, worker count, native and OpenHCS total clocks and their ratio.
- [Eight-assignment measured source record](../../benchmark/results/official30_matched_20261006/README.md), including the matched one-process baseline used for the two-worker comparison.
- [Retained nine- and sixteen-assignment paired clock panels](../figures/slas/supp_matched_scaling.png), with the original separate capture heads.
- [Single-core amortization: execution, total and paired nonexecution time](../figures/slas/matched_postgrid_20261006/single-core-amortization/measured_single_core_amortization.png).
- [Nine-assignment execution ratios](../figures/slas/matched_latestmain_nine_20261006/primary-execution/measured_execution_metrics_long.csv) and [total ratios](../figures/slas/matched_latestmain_nine_20261006/primary-total/measured_total_metrics_long.csv), with the [qualified source record](../../benchmark/results/matched_latestmain_nine_20261006/README.md).
- [Sixteen-assignment execution ratios](../figures/slas/matched_lastconsumer_20261006/primary-execution/measured_execution_metrics_long.csv) and [total ratios](../figures/slas/matched_lastconsumer_20261006/primary-total/measured_total_metrics_long.csv), with the [qualified source record](../../benchmark/results/matched_lastconsumer_20261006/README.md).
- Additional independent-CellProfiler-process controls: [nine-assignment execution](../figures/slas/matched_latestmain_nine_20261006/independent-cp-calibration-execution/measured_execution_seconds.png), [nine-assignment total](../figures/slas/matched_latestmain_nine_20261006/independent-cp-calibration-total/measured_total_seconds.png), [sixteen-assignment execution](../figures/slas/matched_lastconsumer_20261006/independent-cp-calibration-execution/measured_execution_seconds.png) and [sixteen-assignment total](../figures/slas/matched_lastconsumer_20261006/independent-cp-calibration-total/measured_total_seconds.png).

Single-core amortization uses one worker and one numerical thread, with actual
medians over three measured repetitions after warmup at 1, 9 and 16 repeated
assignments of one biological source sample. Connecting lines join observations.
OpenHCS nonexecution time is the median paired difference between total and full
server execution per assignment; it is not a kernel/runtime decomposition.
Those observations passed declared-output comparisons on revision `eb773573c`.
Their selected workflows were not reselected from the final single-sample rankings.
The [earlier three-workflow sixteen-assignment checkpoint](../../benchmark/results/matched_postgrid_20261006/README.md)
and its [passive-counter diagnostics](../../benchmark/results/matched_postgrid_20261006/diagnostics/3d-same-step-scaling-counter-comparison.json)
remain separate records. Increased system time, process swap and major faults
support a working-set/reclaim contribution; they do not identify an allocation
owner or establish that later fixes eliminate paging.

### Matched scaling protocol

The earlier revision `eb773573c` supplies the measured 1, 9 and 16-assignment
series for illumination correction Example 3, Vitra and 3D monolayer.
Revision `d8678dbd4` supplies matched eight-assignment
observations with one and two workers for all three workflows, with its own
same-revision single-assignment observations. The later nine-assignment record at `71aded26c`
supplies one- and three-worker observations for all three workflows; the later
sixteen-assignment record at `2cda84a369` supplies one- and four-worker
observations for the 3D monolayer only. The current full-cohort revision
`3894ca3a0` supplies one-assignment, one-worker observations, not a current
multiworker sweep. Two-, three- and four-worker captures have different revisions,
assignment counts and cohort sizes; they are not a single matched 1–4-worker sweep.
Eight, nine and sixteen assignments repeat each workflow's existing source sample;
they are not independent biological wells. No averages across unlike workflows
or revisions are used here.

Execution includes worker coordination, saving, plate exports and finalization.
Total includes disjoint compile and execute client submit/wait phases. Endpoint,
library and kernel readiness and subsequent scientific comparison are outside
the clocks; native total excludes one-time pipeline loading and JVM startup.
Main Figure 6 reports the full single-sample cohort. The tables above give exact
ratios, independent-CellProfiler-process controls and single-core amortization.

Warmup and three measured repetitions passed each workflow's declared-output
comparisons. The original [eight-/nine-assignment sheet](../figures/slas/supp_matched_worker_speedups.png)
and [four-worker sheet](../figures/slas/supp_matched_worker_speedups_continued_2.png)
provide the inputs to the consolidated worker-comparison layout.

The selected-workflow comparisons use one stock CellProfiler process and the
declared OpenHCS worker count. Additional independent CellProfiler processes
provide a calibration.

## Figure assembly and interface records

The [supplement generator](../figures/build_slas_supplement.py) combines existing artwork and saves editable SVG, PDF and PNG outputs. It changes layout only; measurements, segmentation and display contrast are unchanged.

Source illustrations show [array grouping and scheduling](../figures/slas/runtime_composition.png), [function preparation](../figures/slas/compiler_preparation.png), [connected images and measurements](../figures/slas/outputs_and_inspection.png), [custom-function registration](../figures/slas/custom_function_extension.png), [CellProfiler translation](../figures/slas/cellprofiler_translation.png), and [Fiji/napari inspection](../figures/slas/inspectable_results.png).

The [native code/field interaction record](../figures/slas/authoring_verified_roundtrip_provenance.json) documents the parameter-edit round trip. Main Figure 1 uses the [two-plate capture](../figures/slas/figure1_two_plate_native_20261007/capture_evidence.json), with ExampleHuman's nine-step recipe displayed, and the native [custom-function form](../figures/slas/custom_extension_live_parameters_capture_provenance.json) and [code capture](../figures/slas/custom_extension_live_code_capture_provenance.json). The [capture-source record](../figures/slas/custom_extension_live_evidence.json) identifies the source state at capture. The custom function has gain 1.2 and offset 0.0; the [code readback](../figures/slas/custom_extension_live_code_document.json) identifies the same function. These captures show authoring controls; the function was not executed on an assay.

The [translation source](../figures/slas/cellprofiler_translation_provenance.json) maps ExampleCometAssay to 12 OpenHCS steps and checks the generated Python round trip. Image and ROI inspection examples are attributed in the [gallery source record](../../website/assets/gallery/release-media-record.json).

## Supplementary Data 4. Method-directed NeuronCyto demonstration

A gpt-5.6-sol agent analysed NeuronCyto II image 1 through MCP using a method-directed brief. The brief specified channel roles, normalization, neurite enhancement, nucleus and soma segmentation, rooted neurite assignment, and morphology outputs. The original run produced nine neurons, ten nuclei, eight branches, 25 graph paths and 1,982 pixels of total outgrowth. It demonstrates authoring, execution and inspection; no manual segmentation score was supplied.

The [original evaluation](../../website/assets/agent/cold-start-workflow-record.json) contains the prompt, input hashes, software/model versions, tool calls, outputs and viewer checks. The [figure source](../figures/slas/figure3_provenance.json) identifies the original recording. Later corrections and replays used the same images with their own pipelines and outputs.

Figure artwork uses unmodified Lucide icons under the [licence](../figures/assets/lucide/LICENSE); the [source record](../figures/assets/lucide/SOURCE.txt) identifies their revision.

### Current-source replay after algorithm development

A separate OpenHCS 0.8.5 replay used the same two public images with
nuclear-supported soma detection and soma-rooted path assignment. It produced
eight neuronal cell bodies, eight nuclei, 18 processes, two branch events,
one resolved crossover and 24 graph paths. The eight per-cell table totals
agree with the graph distance features and sum to 2556.137 pixels under unit
spacing. The [current replay summary](current_neurite_replay_summary.md)
identifies its execution, saved source and native receipts separately from
the original demonstration and the OpenHCS 0.7.14 correction.

### Published manual-tracing references

The [NeuronCyto II publication](https://doi.org/10.1002/cyto.a.22872) supplies independent measurements
for image 1 in its supplementary files 8–10. The two input TIFFs used here are
byte-identical to `CrossOvers_Images/1_w1.tif` and `1_w2.tif` in the public
`Testing image.zip` archive. The checksums are listed in the original run record.

| Published reference | Image 1 entry | Source file |
| --- | --- | --- |
| Manually traced neurons | Eight per-cell entries | Supplement 9 |
| Neurite length by branch order | Primary 3,633.672; secondary 198.929; tertiary 0; total 3,832.601 | Supplement 8 |
| Crossover count | Three crossovers; NeuronCyto II resolved two | Supplement 10 |

Lengths above retain the numerical units of the source tables. The eight
per-cell reference lengths are 426.82, 172.375, 751.962, 395.04, 669.783,
343.629, 587.841 and 485.152. These entries give a reference against which to
investigate the nine reported neurons. Spatial cell matching, measurement-unit
alignment and agreement on the definition of neurite length are needed before
computing per-cell accuracy. The public testing archive contains the images;
downloadable manual trace coordinates have not been located. The published
crossover count and the OpenHCS branch count measure different quantities.

Main Figure 5A/B and D–F are full-resolution presentations of the frozen raw
arrays, body-label planes and graph-path archives, rather than reduced native
viewer screenshots. The [source manifest](../figures/slas/frozen_neurite_views.json)
records the six original file hashes and the recorded raw display windows.
Dark label colours and vector strokes are display choices only; no analysis
was rerun or coordinates changed. Figure 5C uses an unmodified embedded JPEG
from page 4 of the published article PDF, giving a 450-pixel panel crop instead
of the earlier 225-pixel web crop. Its source, extraction and attribution are
recorded in the [published-reference record](../figures/slas/neuroncyto_published_reference/source.json).

The [reference audit](neuroncyto_reference_audit.md) records the source links,
file checksums and ROI identifiers. These measurements were examined after the
recorded agent run and were not supplied to the agent during authoring.



## Supplementary Data 5. Complex CellProfiler workflow imports

The [derived workflow report](complex_cellprofiler_workflows.md) lists every
imported step, its function names and call count for the advanced segmentation
and 3D monolayer tutorials. It links the source pipelines and generated editable
Python. The generator checks function identities and parameters after reloading
each document and records the hashes of the source pipelines, importer and
function implementations.

These are import and code-round-trip checks. Supplementary Data 1 separately
records the release CI executions and selected output comparisons for both
workflows.

## Supplementary Data 6. Workflow regression tests

The tests exercise representative authoring and validation cases alongside the
recorded UI demonstration. The following source files are pinned to commit
`7a7d21fee726905b87b9020cebf0bdfc350631f4`; these three test files are unchanged
from the OpenHCS 0.8.5 release commit.

| Tested behavior | Source tests |
| --- | --- |
| Nested and inherited configuration, parameter order, enum identity and function-step reconstruction | [Python generation tests](https://github.com/OpenHCSDev/openhcs/blob/7a7d21fee726905b87b9020cebf0bdfc350631f4/tests/unit/test_pycodify_formatters.py) |
| Rejection of incompatible memory types, grouping, required axes and stack configuration | [Compiled-function validation tests](https://github.com/OpenHCSDev/openhcs/blob/7a7d21fee726905b87b9020cebf0bdfc350631f4/tests/unit/test_funcstep_contract_validator.py) |
| Rejection of a function-detail request using a stale catalog revision | [Function-catalog tests](https://github.com/OpenHCSDev/openhcs/blob/7a7d21fee726905b87b9020cebf0bdfc350631f4/tests/unit/test_function_catalog_zmq.py) |

The [unit-test job](https://github.com/OpenHCSDev/openhcs/actions/runs/34870874969/job/104066142788)
passed while selecting `tests/unit` and `tests/core`. These focused tests include
controlled fixtures and isolate the stated behavior. The real-corpus execution
and value comparisons are provided by the separate Official30 job in
Supplementary Data 1.

## Supplementary Data 7. Prospective agent-authored assay validation

### Earlier prospective held-out results

The three prospectively authored workflows were applied without scientific parameter changes after their held-out partitions were disclosed (Supplementary Figures 2–3 and Supplementary Data 7). On the 50 BBBC039 fields, 4,733 of 5,720 reference nuclei matched at intersection over union at least 0.5. Pooled precision was 0.680, recall was 0.827 and object F1 was 0.746; mean field foreground Dice was 0.935. The workflow predicted 6,964 nuclei, 1,244 more than the reference, and the overlap diagnostic identified more split reference instances than merged predictions. The first blind pipeline therefore recovered nuclear foreground well while over-segmenting instances.

On the 12 BBBC007 fields, 29,450 of 43,875 relevant predicted adjacent-cell boundary pixels were within two pixels of a manual outline, a pooled fraction of 0.671. The workflow predicted 1,274 nuclei and 1,273 cells; every predicted nucleus overlapped a cell and one cell shared two nuclei. The manual outlines enclosed 1,082 closed nuclear interiors, while 12 open or frame-connected regions were excluded. Because the boundary score is directed from predictions to the outline union, it can reward an incomplete segmentation and does not establish object correspondence.

The BBBC013 run produced matched nuclear and cytoplasmic measurements for 14,262 cells across all 92 held-out wells. Wortmannin controls separated with Z-prime 0.751 and mean nuclear-to-cytoplasmic GFP ratios of 7.235 and 0.915 for positive and negative controls. LY294002 controls gave Z-prime 0.554 and means of 7.219 and 1.127. Both held-out dose series showed the expected increase in nuclear translocation. This result evaluates recovery of the assay response; BBBC013 does not supply manual masks with which to score segmentation.

The [validation report](independent_agent_validation.md) records the prospective
design, quantitative results, limitations, prediction-manifest hashes and
infrastructure findings for BBBC039, BBBC007 and BBBC013. Each trial used a
fresh gpt-5.6-sol author through the connected OpenHCS desktop and MCP surface.
Four development fields or wells were visible before the scientific pipeline
was frozen; held-out references and treatment metadata were then scored by the
typed evaluator in
[`benchmark/annotated_validation.py`](../../benchmark/annotated_validation.py).

The tracked [evidence index](independent_validation/README.md) links each exact
frozen pipeline and held-out score receipt. Prediction arrays and source-image
archives remain outside the paper package because the BBBC013 held-out result
tree alone contains 1,472 artifacts and 672 MB. The score receipts bind their
prediction manifests and the common corpus manifest by SHA-256. The
[preparation record](../../benchmark/annotated_validation_20260915.md) explains
the deterministic partitions, image normalization and evaluation definitions;
the preparation manifest records the downloaded source identities.

The prospective held-out panels in Supplementary Figures 2–3 are generated by
[`build_slas_independent_validation.py`](../figures/build_slas_independent_validation.py)
from the three score receipts. Its
[plot data](../figures/slas/independent_agent_validation_plot_data.csv) and
[provenance receipt](../figures/slas/independent_agent_validation_provenance.json)
retain the plotted rows and source/output hashes.

## Supplementary Data 8. Autonomous analysis evidence

### Linked source artwork and assisted mosaic evidence

Main Figure 5 shows public shafts and autonomous laboratory-field analysis.
The separate [assisted nine-field mosaic artwork](../figures/slas/p001_stitched_dev13_native.png)
and [retained overlap/core layout](../figures/slas/supp_neurite_morphology.png)
document acquisition-placed stitching, not another quantitative comparison.
One pooled percentile pair was fitted per complete nine-field channel stack
before assembly. Faint segments and crowded ownership remained incomplete.
The [completed all-channel continuation](task_only_analysis/p001-allchannel25-qualified-completion.rst)
reported 1,740 soma candidates and 123,054 micrometres of computed outgrowth
at the declared spacing. These continuation totals do not belong to the earlier
sampled panels and are not ground-truth lengths or a unique biological census.

The independent BBBC039 repeat matched 20,207 of 23,615 reference instances,
with 1,164 excess predictions and 3,408 misses. The earlier author matched
20,521, with 1,153 excess predictions and 3,094 misses. Pooled F1 values are
0.898 and 0.906, respectively, at intersection over union ≥ 0.5. The
[original independent-author sheet](../figures/slas/bbbc039_independent_repeat.png)
and its source record retain this comparison; annotation-empty fields coincide
at the scatter origin.

Original artwork retains wider context and source records:
[process architecture](../figures/slas/process_architecture.png),
[runtime composition](../figures/slas/runtime_composition.png),
[compiler preparation](../figures/slas/compiler_preparation.png),
[typed extension](../figures/slas/custom_function_extension.png),
[full-plate translocation](../figures/slas/translocation_fresh23.png),
[translocation development](../figures/slas/bbbc013_development_repair.png),
[H001 scored review](../figures/slas/h001_scored_native.png),
[volume repair](../figures/slas/h002_fresh22_split_repair.png),
[orthogonal localisation](../figures/slas/h002_fresh10_native.png),
[retinal review](../figures/slas/retina_fresh16_repair.png),
[retinal development](../figures/slas/retinal_development_repair.png),
[paired DNA repair](../figures/slas/h003_native_repair.png),
[actin support checks](../figures/slas/h003_fresh19_matched.png),
[public shaft/junction review](../figures/slas/h004_assay_review.png) and
[public main shafts](../figures/slas/h004_main_shafts.png).
Retinal source: user-provided R0010 RBPMS images; physical calibration unverified.
DNA/actin source: BBBC007v1 A02, Sabatini laboratory, Whitehead Institute; CC0.

### Scientific instructions supplied to authors

The [instruction archive](task_only_analysis/original_task_briefs.json) maps trial identifiers to original documents and byte hashes. The table summarizes scientific instructions and uses trial labels with the dataset prefix omitted. Full trial and session identifiers, operational paths, display settings and resource restrictions remain in the archive. The thick-shaft-only target was clarified after the neurite run and was not part of its original brief.

| Brief | Trial labels | Scientific instruction |
| --- | --- | --- |
| 1: BBBC007 nuclei and cells | `FRESH651_88`; `FRESH08_96`; `FRESH10_ROTATION_89`; `RETAINED_DEV13_94`; `FRESH19_95`; `FRESH26_96` | Segment nuclei and seeded cells from paired DNA/actin images across 16 source sets, with labels and object tables. Source bindings and optional custom-function tracks were supplied. |
| 2: Paired DNA and actin: full released sixteen-source collection | `FRESH19_95` | Analyse all sixteen paired DNA/actin fields, choosing the method from image measurements and packaged guidance. Inspect separated regions before selecting the final pipeline. |
| 3: BBBC013 GFP translocation | `REPEAT94`; `DEV02_94`; `DEV89`; `REMEDIATION02_89`; `FRESH13_88`; `FRESH15_96 (session)`; `FRESH15_96 (session)`; `FRESH20_88`; `FRESH23_96` | Measure nuclear and cytoplasmic GFP in 96 paired source sets and produce cell/well response tables. Source bindings, catalogue tracks and optional statistics extensions were supplied. |
| 4: BBBC039 nuclei | `FRESH594_88`; `FRESH612_96`; `FRESH656_88`; `FRESH08_88`; `FRESH10_COVERAGE_96`; `FRESH13_88` | Segment nuclear instances in 200 source sets and save label images and object measurements. The brief supplied source bindings and catalogue-only authoring. |
| 5: H001: bright-object segmentation | `FRESH10_96`; `FRESH586_96`; `FRESH19_89`; `FRESH22_96`; `FRESH25_FOURTH_95`; `FRESH25_ROTATION_94` | Segment bright objects in one two-dimensional image and report pixel areas and count. Review raw images and labels across positions and intensity windows. |
| 6: H002: 3-D centre detection | `CAPACITY_DEV94`; `FRESH651_95`; `FRESH656_96`; `FRESH10_89`; `FRESH10_ROTATION_96`; `FRESH13_89`; `FRESH15_89`; `FRESH22_89`; `FRESH23_ROTATION_89` | Detect nuclear centres in a three-dimensional volume and report z/y/x voxel coordinates and count. Inspect separated slices and orthogonal views; physical spacing was unverified. |
| 7: Paired nucleus and cell segmentation | `POSTPAUSE_88`; `FRESH656_96`; `FRESH656_88`; `FRESH09_95`; `FRESH10_96`; `FRESH15_96`; `FRESH16_94`; `FRESH23_89`; `FRESH25_89`; `FRESH26_89` | Segment nuclei and actin-supported cells in one paired field, preserving w1/w2 identity. Explicit source pairing and distributed multi-window review were required. |
| 8: H004 blind neurite-outgrowth analysis | `FRESH08_95`; `FRESH10_89`; `FRESH20_95`; `FRESH22_94`; `FRESH25_ROTATION_89` | Infer channel roles in one paired neurite field and measure supported somata and outgrowth. Review faint paths, background connections and crossing ownership before evaluation. |
| 9: Paired-field soma and neurite-outgrowth analysis | `FRESH20_95` | Analyse paired soma/neurite images, infer channel roles and save object/path measurements in pixel units. Keep the first attempt and later self-directed repairs. |
| 10: Blind neurite-outgrowth development task | `STITCH_DEV94`; `FRESH13_96`; `STITCH_DEV13_94`; `INPUT_REPAIRED22_88` | Analyse nine paired fields from one coded well, with w1 DAPI, w2 FITC and declared spacing 1.3556 µm per pixel. Choose the method independently and report uncertain crossing ownership. |
| 11: Personal nine-field neurite analysis | `INPUT_REPAIRED22_88`; `ALLCHANNEL_RETAINED_DEV25_88` | Analyse nine paired DAPI/calcein fields and their acquisition layout, including authorized mosaic work. Report fieldwise geometry without counting overlapping fields as unique cells. |
| 12: Personal nine-field neurite analysis: retained development | `RETAINED_REPAIR23_88` | Continue a saved nine-field analysis and assembled mosaics, reviewing misses, bridges and ownership. This is a retained-development continuation. |
| 13: Unavailable pooled-stack scientific brief | `POOLED_STACK_DEV25_88` | The brief for this trial was not kept. |
| 14: R0010 independent-author development trial | `REPAIR10_94`; `STAGED_96`; `FRESH656_95`; `FRESH09_96`; `FRESH13_89`; `FRESH22_96`; `FRESH23_94`; `FRESH25_94`; `FRESH26_94` | Segment RBPMS-positive retinal somata in one development CZI and report labels, measurements and count. RBPMS/Hoechst hints and distributed review were supplied. Its historical inherited-context statement does not describe the audited fresh09/fresh26 launches. |
| 15: Retinal whole-mount RBPMS analysis | `STAGED_96`; `FRESH656_95`; `FRESH09_96`; `FRESH13_89`; `FRESH22_96`; `FRESH23_94`; `FRESH25_94`; `FRESH26_94` | Segment RBPMS-positive somata in the retinal development field, confirming channels from raw images. Preserve the first attempt, self-directed repairs and matched regional review. |
| 16: Retinal whole-mount RBPMS analysis | `FRESH22_96`; `FRESH23_94`; `FRESH25_94` | Analyse the authorized retinal development input with RBPMS/Hoechst hints and packaged MCP guidance. Report uncertain soma identity, extent and boundaries. |

The three earlier prospective trials have no recoverable original instruction file. Their design and data partitions are described in Supplementary Data 7. The historical Brief 14 records inherited conversation. Original launch records for R0010_FRESH09_96 and R0010_FRESH26_94 identify new execution sessions, with memory disabled and no parent thread, resume or fork. The historical context statement therefore does not classify these two trials. Their launch-source references are indexed by the [trial resource CSV](task_only_analysis/trial_resources.csv) and [accounting reference](task_only_analysis/trial_resources.rst). Other trials mapped to Brief 14 have not been audited for launch context.

The current skill describes intended inspection and repair practice. Its later additions are not evidence that earlier authors followed those instructions. Main Figure 3 separates this intended workflow from a recorded H001 example; its wall times come from the original resource catalogue, and its candidate sequence comes from the author's retained report. No universal count of review rounds is inferred from screenshot totals.

Supplementary Figures 2–5 group additional evidence by assay. Main Figure 4 shows
translocation and volume localisation; main Figure 5 shows public and personal
field-by-field neurite analysis. The assisted mosaic is retained as linked
development evidence below, not an additional display figure. Reference evaluation
follows pipeline selection; examples lacking exhaustive annotations do not
receive an accuracy percentage.

- [Bright-object analysis](task_only_analysis/h001-fresh25-qualified-review.rst).
- [Volume localisation](task_only_analysis/h002-fresh23-paired-localisation.rst).
- [Paired-channel analysis](task_only_analysis/h003-fresh26-qualified-completion.rst).
- [Retinal soma localisation](task_only_analysis/retinal-fresh26-qualified-completion.rst).
- [Personal nine-field mosaic](task_only_analysis/p001-allchannel25-qualified-completion.rst).
- [Independent field-by-field laboratory neurite analysis](../../figure-collection-20261004/P001-FRESH13-NINE-FIELD-REVIEW.rst), with frozen pipeline and output identities, sampled raw/path review and remaining limitations.
- [Public translocation assay](task_only_analysis/bbbc013-fresh23-qualified-completion.rst).
- [Public neurite analysis](task_only_analysis/h004-fresh20-qualified-completion.rst).
- [BBBC039 frozen predictions on image-uninspected fields](task_only_analysis/bbbc039-uninspected-fields.rst),
  with the [field-level scores and exposure flags](task_only_analysis/bbbc039-uninspected-fields.csv)
  and [source and image-opening evidence](task_only_analysis/bbbc039-uninspected-fields.json).
- [BBBC013 endpoint selection and development-well inclusion](task_only_analysis/bbbc013-fresh23-endpoint-provenance.rst).
- [Trial wall times, usage and dated model/software identities](task_only_analysis/trial_resources.rst),
  with the [complete resource catalogue](task_only_analysis/trial_resources.csv).

The [frozen nine-field pipeline source](task_only_analysis/pipelines/p001-fresh13.py)
is supplied unchanged, with SHA256
`8b9a70c205103ec9d1600b0592cfb9481bf989e449f049aee176803069f34203`.
It retains the recorded output root and viewer endpoint; for reproduction,
relocate only input/output destinations and use the source-document MCP
validation, compilation and execution workflow with the recorded installation.
Do not execute the file as an alternative analysis route. The input manifest
and interpretation limits are identified in the linked review.

The following source files are also supplied byte-for-byte from the authors'
selected frozen attempts. Their run identities and original hashes remain in
the linked analysis records; no candidate was reselected using reference scores.

| Analysis and run | Selected attempt | Frozen pipeline |
|---|---|---|
| Bright objects, fresh25 | REPAIR02 | [Source](task_only_analysis/pipelines/h001-fresh25.py) |
| Volume localisation, fresh23 | REPAIR05 | [Source](task_only_analysis/pipelines/h002-fresh23.py) |
| DNA/actin, fresh26 | REPAIR03 | [Source](task_only_analysis/pipelines/h003-fresh26.py) |
| Retinal somata, fresh26 | repair03 | [Source](task_only_analysis/pipelines/retina-fresh26.py) |
| Public neurites, fresh20 | repair03 | [Source](task_only_analysis/pipelines/h004-fresh20.py) |
| Translocation, fresh23 | FULL_S08 | [Source](task_only_analysis/pipelines/bbbc013-fresh23.py) |
| BBBC039, fresh612 | final_full200 | [Source](task_only_analysis/pipelines/bbbc039-fresh612.py) |
| BBBC039, fresh10 coverage | FULL200 | [Source](task_only_analysis/pipelines/bbbc039-fresh10.py) |
| BBBC007, fresh26 | REPAIR05 | [Source](task_only_analysis/pipelines/bbbc007-fresh26.py) |

The two BBBC039 sources correspond to the plotted full-200 result (pooled
F1 0.906) and the independent coverage repeat (0.898), respectively. Both
require the original [image metadata table](task_only_analysis/pipelines/bbbc039/source_manifest.csv);
fresh10 also imports the supplied [source binding](task_only_analysis/pipelines/bbbc039/source_bindings.py).
Relocate its original import directory and metadata location to these supplied
files when reproducing the workflow. The binding's SHA256 is
`fdbe5bd37084b6f03a10dd8617fb503e26dbc73e011cda655cb1b028a2597dcc`.
It matches fresh10's original source-identity record and an identical copy in
fresh612's frozen manifest, but is not directly listed in fresh10's final manifest.
The BBBC007 source is the final REPAIR05 analysis of all 16 paired fields,
not an earlier candidate; its relative `source_sets.csv` location refers to the
supplied [paired-field metadata](task_only_analysis/pipelines/bbbc007/source_sets.csv).

The volume pipeline also requires the original [centre-detection custom function](task_only_analysis/pipelines/h002-fresh23/custom_function.py).
The translocation pipeline requires its original [compartment measurements](task_only_analysis/pipelines/bbbc013-fresh23/bbbc013_compartment_qc_v4.py),
[assay statistics](task_only_analysis/pipelines/bbbc013-fresh23/bbbc013_assay_statistics_v1.py)
and [dose-response summary](task_only_analysis/pipelines/bbbc013-fresh23/bbbc013_dose_response_v2.py)
functions. Register these sources through MCP under their recorded function
names before validating the corresponding pipeline. Reproduction also requires
the recorded inputs, metadata and software version. Preserve scientific
settings while relocating destinations and use an isolated viewer endpoint.
These are frozen analysis artifacts, not additions to the processing library.
The retinal and volume sources in this table correspond to Data 8's named
trials, not the different retinal trial in Supplementary Figure 4 or the
volume trial in main Figure 4.

The personal mosaic and explicitly labelled development examples retain assisted
provenance; they are not counted as fresh unguided trials. Recovery of principal
neurite shafts is the relevant illustrated result, not exhaustive filopodial
tracing or definitive neuron ownership at crossings.

Original attempts, unsuccessful candidates and delivery history remain in the
linked records and the [archived evidence inventory](https://github.com/OpenHCSDev/openhcs/blob/7f318f36969cae281964a31f4f43899a45a9a8f3/paper/supplementary/README.md#supplementary-data-8-task-only-authoring-and-independent-repair).
They are not additional experimental replicates.

For NeuronCyto II image 1, the published manual-reference table contains eight
traced-cell entries, without spatial identifiers or an exhaustive-coverage
statement. The official testing archive contains the two source images but no
manual spatial tracing files. Aggregate agreement therefore does not establish
shaft recall, neuron ownership or calibrated length accuracy. The
[reference audit](neuroncyto_reference_audit.md) retains the source-table
checksums, image correspondence and interpretation. The manual-reference
construction is described by [Ong et al. (2016)](https://doi.org/10.1002/cyto.a.22872).

The [image-1 length comparison](neuroncyto_length_evaluation/conclusion.rst)
verifies that the H004 first prediction used the same source field. It reports
4,085.1925 pixels of rooted outgrowth; the published manual total is 3,832.601
in unspecified units. These values are descriptive, not an accuracy ratio:
the length definitions and units have not been aligned, and the retained
reference has no spatial traces or cell correspondences. The
[aggregate table](neuroncyto_length_evaluation/aggregate_lengths.csv) keeps the
first prediction separate from the overextended final attempted repair. Main
Figure 5 illustrates the initial shaft candidate, not that repair. The intended
thick-shaft endpoint was clarified after the run; the original brief and all
predictions remain unchanged. This clarification is not evidence that the
original author received that more specific target.
The [primary-source follow-through](neuroncyto_length_evaluation/unit_followthrough.rst)
records the article and user-guide checks and the remaining unit requirement.

## Additional paired-channel results

A further BBBC007 author analysed sixteen paired fields after self-directed repair, producing 1,428 nuclear and seeded-cell IDs. Saved masks reconcile reported areas and same-ID nucleus containment. The [final-candidate analysis](task_only_analysis/bbbc007-fresh26-final-candidate.rst) describes a possible remaining merge and crowded-boundary uncertainty.

An independent paired DNA/actin author recovered three crowded nuclear omissions and removed two candidates with no actin-supported growth beyond their nuclear seeds. Its final 56 nuclei and 54 cell regions have reconciled labels, areas and parent relationships. The [completed analysis](task_only_analysis/h003-fresh26-qualified-completion.rst) contains matched raw/label review and own-nucleus containment checks.
