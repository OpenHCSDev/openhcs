---
bibliography: ../openhcs_references.json
csl: ../styles/elsevier-vancouver.csl
reference-section-title: References
link-citations: true
link-bibliography: true
---

# OpenHCS supplementary material

Additional images, measurements and methods support the main results. The [earlier supplement](README_before_readability_20261015.md) preserves detailed run histories, source inventories and extra chart variants.

## Supplementary Figure 1. Runtime composition and preparation

![Array grouping, named results, scheduling and preparation.](../figures/slas/supp_workflow_infrastructure.png){width=4.8in}

::: {custom-style="ImageCaption"}
(I, A–D) Array axes and groups supply image views to per-plane, stack or stack-reduction functions. Named labels remain available to later measurements; sequential timepoints complete in order while wells can run in parallel. (II) Compiled plans, prepared functions and a worker map form the execution bundle. The [figure assembly and interface records](#figure-assembly-and-interface-records) link the source artwork; main Figures 1–2 show the native workflow and process topology.
:::

## Supplementary Figure 2. Translocation response and compartment eligibility

![Full-plate eligibility fractions and independent held-out translocation endpoints.](../figures/slas/supp_translocation.png){width=5.7in}

::: {custom-style="ImageCaption"}
(A–B) Protein translocation analysis 2: fraction of nuclei with measurable cytoplasm in 96 BBBC013 wells, including four development wells. Dots show four wells per dose; marks and whiskers show their mean and sample standard deviation (variation among wells). Main Figure 5E shows the response curves. (C–D) Protein translocation analysis 1: mean cell-level GFP ratios on held-out wells, with four wells per control condition. Z′ measures separation between positive and negative controls relative to their variation; higher is better, and values above 0.5 indicate an excellent assay. Analyses 1 and 2 use different well summaries: mean GFP ratio and median log2 ratio, respectively. Supplementary Data 7–8 give the methods and source data.
:::

## Supplementary Figure 3. Nuclear-instance evaluation and object separation

![Independent-author scores and prospective held-out assays.](../figures/slas/supp_nuclear_instances.png){width=5.7in}

::: {custom-style="ImageCaption"}
(A–B) Nuclear detection analyses 3 and 2 on 200 BBBC039 fields, with pooled F1 of 0.898 and 0.906, respectively. F1 balances missed and false detections; 1 is best. Matching required intersection over union ≥ 0.5: overlap covering at least half the total area of the two outlines together. (C–D) Nuclear detection analysis 1 on 50 held-out fields and cell-boundary analysis 1 on 12 held-out fields. Each used four development fields. Dice measures area overlap, with 1 indicating identical areas. Boundary support is the fraction of predicted boundary pixels within two pixels of a manual outline; it does not measure whether every manual border was found. Supplementary Data 7–8 provide counts and per-field scores.
:::

## Supplementary Figure 4. Independent morphology checks and remaining ambiguities

![Independent orthogonal localisation, retinal borders and unsupported body growth.](../figures/slas/supp_morphology_checks.png){width=5.4in}

::: {custom-style="ImageCaption"}
(A–C) Nuclear centres from an independent volume analysis in XY, XZ and YZ. (D–F) Retinal border region shown raw, with first and final outlines; a possible split remains at display window 0–42, gamma 1. (G–I) A faint DNA pair remains merged at window 0–151. (J–L) A nuclear seed lacks actin-supported body growth at window 0–104, gamma 1. The panels show separate trials; colours identify objects within each image. Supplementary Data 8 links the source captures and matching records.
:::

## Supplementary Figure 5. Laboratory treatment responses compared with MetaXpress

![Additional endpoint responses from all three independent blind agents.](../figures/slas/supp_neurite_autonomous_endpoints.png){width=5.7in}

::: {custom-style="ImageCaption"}
(A–B) Detected cells; (C–D) total outgrowth; (E–F) branches per cell; (G–H) mean cell process length. Each blind agent completed the same 180 fields in 20 wells. Curves use each drug's own DMSO mean; dots are two technical wells per dose per analysis or method, with sample SD whiskers. Analysis curves are not pooled. Paired drug panels share vertical limits. Main Figure 4A–B shows mean outgrowth per cell.
:::

## Supplementary Figure 5, continued. Process length and branching definitions

![Median process length, branch and primary-process responses from all three blind agents.](../figures/slas/supp_neurite_autonomous_endpoints_continued.png){width=5.7in}

::: {custom-style="ImageCaption"}
(I–J) Mean cell median process length; (K–L) total branches; (M–N) total primary processes; (O–P) branches per primary process. Normalization, technical wells and whiskers are as above. Total quantities are mean field totals, not deduplicated whole-well measurements. OpenHCS branch/process values are means of field ratios; MetaXpress values are ratios of exported well totals. These remain distinct algorithm-defined endpoints.
:::

### Three independent analyses of the same treatment assay

Three new gpt-6.1-sol agents received the same [task brief](personal_neurite_autonomous/TASK.rst), [acquisition information](personal_neurite_autonomous/ACQUISITION.json), MCP access and OpenHCS guide. Each analysed 20 coded wells with nine fields per well. Treatment identities, MetaXpress measurements and assisted results remained hidden until all three methods and outputs were finalized. The [trial record](personal_neurite_autonomous/cohort.json) identifies software, instructions, development images and final outputs.

All three recovered increased mean and total outgrowth at every nonzero dose of both drugs. At 40 µM, mean-outgrowth-per-cell fold changes were 1.646, 1.323 and 1.601 for FC-A, and 1.694, 1.487 and 1.660 for Y27632. Assisted values were 1.766 and 1.765; MetaXpress values were 1.977 and 2.053. These are independent analyses of the same two technical wells per dose, not additional biological replicates.

Image review showed substantial shaft and branch recovery, but did not establish complete tracing or anatomically correct branch counts. Analysis 3 explicitly noted that limitation. Its report also records execution starting before a resource check finished; treatment identities and reference measurements remained hidden. Original pipelines, reports and matched-well data are retained for [Analysis 1](personal_neurite_autonomous/author114/author-report.txt), [Analysis 2](personal_neurite_autonomous/author115/author-report.txt) and [Analysis 3](personal_neurite_autonomous/author116/author-report.txt), with full file links in the earlier supplement.

## Supplementary Figure 5, continued. Scientist-assisted analysis

![Five additional well-level morphology responses to FC-A and Y27632 after assisted repair.](../figures/slas/supp_neurite_treatment_endpoints.png){width=5in}

::: {custom-style="ImageCaption"}
(Q–R) Detected cells; (S–T) total outgrowth; (U–V) branches per cell; (W–X) mean cell process length; (Y–Z) mean cell median process length. Twenty matched wells were analysed after assisted repair. Each curve is normalized to its own DMSO mean; dots show two technical wells per dose and whiskers their sample SD. Mean outgrowth per detected cell is included in the linked six-endpoint sheet.
:::

### How neurite measurements were compared

OpenHCS well values are unweighted means of nine field values. For process length, each field first averages the per-cell means or medians, including zero for cells without processes. The agents' separate summaries used only cells with processes; the comparison tables use all detected cells. Missing measurements are never filled with zero. Overlapping fields were not deduplicated: total outgrowth and cell counts are **mean field totals**, not unique whole-well totals.

Each curve is divided by its own drug's zero-dose DMSO mean. Dots are two technical wells per dose; whiskers are their sample standard deviation after normalization. They are not confidence intervals and do not include uncertainty in the control mean. Doses are equally spaced for display; no concentration–response model was fitted.

MetaXpress measurements are an algorithm comparison, not manual ground truth. Its exact site weighting and settings were not retained. The [MetaXpress guide](https://www.moleculardevices.com/sites/default/files/en/assets/training-material/dd/img/metaxpress-6-software-application-modules-neurite-outgrowth.pdf) defines primary processes as outgrowths attached to cell bodies and branches as junctions, but does not specify crossing resolution. OpenHCS process lengths include connected daughter branches assigned to a soma-adjacent root, rather than individual segments between junctions. Its branch counts require at least three same-neuron paths with distinct image-supported arms; resolved crossings do not automatically count as branches. Thus equal endpoint names do not establish identical topology.

The assisted analysis used DAPI and calcein, spacing 1.3556 µm/pixel, neurite response 30 and candidate threshold 0.03. External image review informed repairs to soma-edge branches and missing paths; MetaXpress fold changes were not a tuning target. The [settings record](personal_neurite_repaired_morphometry/source_evidence.json), [matched wells](personal_neurite_repaired_morphometry/joined_wells.csv), [treatment effects](personal_neurite_repaired_morphometry/treatment_effects.csv) and [original comparison](personal_neurite_baseline_morphometry/treatment_effects.csv) preserve the separate versions. Changes to path assignment and branching left cell counts unchanged in all 180 fields.

At 40 µM, assisted branches-per-cell fold changes were 1.65 versus 3.00 for FC-A and 1.82 versus 3.26 for Y27632 (OpenHCS versus MetaXpress). Smaller responses also persisted in [total branches and branches per primary process](personal_neurite_branch_diagnostics/treatment_effects.csv), so cell-count denominators alone cannot explain them. OpenHCS branch/process values average field ratios; MetaXpress values divide exported well totals. Without spatial ground truth, tracing, assignment and measurement-definition differences cannot be separated. Both methods recovered positive outgrowth responses.

## Supplementary Figure 6. Measured speed gains from additional workers

![Measured OpenHCS execution scaling for all thirty workflows at a fixed twelve-sample workload.](../figures/slas/submission_benchmark_schedule.png){width=6.5in}

::: {custom-style="ImageCaption"}
Measured OpenHCS execution scaling with twelve repeated samples held fixed and 1, 2, 3 or 4 workers. Each point is one workflow's one-worker time divided by its time at the indicated worker count; all thirty workflows appear in each configuration. Times are medians of three repetitions after warmup. Bars show arithmetic means, black lines medians and the dashed line equal runtime. These measurements require no CellProfiler projection.
:::

Additional serial CellProfiler comparisons and one-worker batch plots are linked in Supplementary Data 3. Main Figure 6 already shows measured single-worker comparisons and the matching-core estimates; those charts are not repeated here.

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

## Supplementary Table 2. Software ecosystems and project-hosted learning resources

**Development history and extension interfaces.** Release dates and first descriptions are distinguished below; they are not interchangeable measures of a project's age.

| Platform | Release or description | Implementation and extension route |
| --- | --- | --- |
| ImageJ / Fiji | ImageJ released in 1997; Fiji first released in 2007. | Java-based ImageJ supports plugins and macros; Fiji packages ImageJ with community plugins and an updater [@Schneider2012; @Schindelin2012]. |
| CellProfiler | Released in 2005; first described in 2006. | Configurable analysis modules; the later Python implementation also supports plugin modules [@Carpenter2006; @McQuin2018; @Weisbart2024]. |
| Icy | Introduced in 2011. | Java plugins, scripting and graphical workflows [@deChaumont2011; @deChaumont2012]. |
| napari | First minor release in 2019. | Python viewing and analysis; plugin packages add readers, writers and interactive tools [@NapariRelease2019; @NapariPlugins]. |
| PyImageJ | Described in 2022. | Connects Java-based ImageJ and Python within a Python process; napari-imagej uses this bridge within napari [@Rueden2022PyImageJ; @NapariImageJ]. |
| OMERO | Data-management system described in 2012. | Shared image storage, metadata management and access from analysis tools [@Allan2012]. |
| BioImageIT | Described in 2022. | Links image-data management with analysis tools and packaged processing environments [@Prigent2022]. |

Web inventories were inspected on 15 October 2026. Counts describe the named collections, not every resource available for a platform. A project-hosted resource can be community-contributed; hosting does not imply that every item is maintained or validated. Plugins, tutorial pages, script files and complete workflows are different units and should not be ranked as equivalent capabilities.

| Platform | Extensions | Tutorials and training | Scripts and workflows |
| --- | --- | --- | --- |
| ImageJ / Fiji | >500 plugins reported in 2012 [@Schneider2012]; historical count. | 26 pages under “Tutorials on this site” in the [index](https://imagej.net/tutorials/). | 402 top-level macro/script files in the [archive](https://imagej.net/ij/macros/). |
| CellProfiler | 24 [supported plugins](https://plugins.cellprofiler.org/supported_plugins.html); >90 built-in modules reported separately [@Weisbart2024]. | 10 main [tutorial exercises](https://tutorials.cellprofiler.org/). | 16 [application collections](https://cellprofiler.org/examples), each potentially containing multiple pipelines. |
| Icy | 448 [plugins](https://icy.bioimageanalysis.org/plugins/) [@IcyCatalogue]. | 6 project-produced [training PDFs](https://icy.bioimageanalysis.org/trainings/), including a shortcut reference. | 82 [scripts](https://icy.bioimageanalysis.org/scripts/); 87 [graphical protocols](https://icy.bioimageanalysis.org/protocols/). |
| napari | 680 plugins in the [dashboard](https://napari.org/weather-report/) [@NapariDashboard]. | 4 worked tutorials in the [index](https://napari.org/stable/tutorials/index.html). | 115 examples in the [code gallery](https://napari.org/stable/gallery.html). |
| BioImageIT | [Python tools](https://bioimageit.readthedocs.io/en/stable/documentation/tool_integration.html) with declared dependencies and environments; total not established. | 2 worked tutorials in the [documentation index](https://bioimageit.readthedocs.io/en/latest/documentation/documentation.html). | No separate total established from the inspected index. |

**Counting rules.** Tutorial counts exclude navigation links, translations of the same exercise, linked external courses, how-to sections and video playlists. The CellProfiler count runs from beginner segmentation through UnmixColors, excluding bonus material, profiling resources and older-version tutorials. ImageJ archive counts use unique top-level filenames ending in `.txt`, `.ijm` or `.js`, excluding `AA_ReadMe.txt`, subdirectories and ZIP bundles; a file can contain several macros. Napari examples are unique `gallery/*.html` destinations. Icy uses its catalogue totals and the six PDFs under “Our own course and tutorial,” not six equivalent tutorials. An unestablished count is not zero.

**Community support.** Rueden et al. reported approximately 10,000 image.sc users and more than 15,000 posts per year in 2019 [@Rueden2019Forum]. Ouyang et al.'s 2023 sample found installation mentioned in 9.9% of opening posts and approximately 19% of roughly 500 threads [@Ouyang2023]. Napari's dashboard reported 1,460 tagged topics and 938 participating users on 15 October 2026 [@NapariDashboard]. Posts are individual messages; topics are discussion threads. The napari total does not distinguish bugs, usage questions, integration requests or announcements. Comparable per-platform bug/help counts were not established: direct image.sc access was unavailable, and neither the published sample nor project resource catalogues provide that breakdown. Missing counts must not be interpreted as absence of support requests, and raw forum volume is not a failure rate.

## Supplementary Data 1. CellProfiler workflow comparison

### What was compared

The 30-workflow collection contains 22 official CellProfiler examples, seven tutorials and one workflow from the CellProfiler 4 performance study [@CellProfilerExamples; @CellProfilerTutorials; @Stirling2021]. The [benchmark report](../../benchmark/results/matched_min3_integrated_main_20261007/README.md) identifies pipelines, images and reference outputs.

Every declared image, CSV and database export matched in one warmup and three measured repetitions: 120 OpenHCS observations. This coverage describes exported files, not every internal image or measurement column. The [per-workflow file counts](README_before_readability_20261015.md#declared-exported-file-coverage) retain the complete inventory.

Five workflows had no file exports. We appended terminal image or label exports without changing their processing settings, producing eight additional native CellProfiler references listed in the [export manifest](../../benchmark/manifests/official30_value_completion_20260914.json). All five label images matched exactly after removing singleton dimensions. All three numerical images matched within absolute and relative tolerances of `1e-6`; maximum absolute difference was `2.9802322387695312e-8`. The [comparison table](../../benchmark/results/official30_value_completion_20260914/label_aware_exact_commit_run/artifact_comparisons.csv) lists each output.

The [recorded environment](../../benchmark/results/official30_value_completion_20260914/label_aware_exact_commit_run/run_environment.json) was OpenHCS on Python 3.12.3, NumPy 2.1.3 and SciPy 1.18.0, against CellProfiler 4.2.8.1 on Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0. A subsequent [unified run](../../benchmark/results/official30_unified_value_comparison_20260916/README.md) re-executed all 30 workflows and reported zero selected-reference differences. Its [inventory](../../benchmark/results/official30_unified_value_comparison_20260916/reference_inventory.csv) contains 21 CSV, three SQLite and six image/array-only profiles. That run's environment was not recorded; the earlier audit's versions cannot establish it.

### Database exports and automated checks

Imported `ExportToDatabase` steps run once per plate and produce a SQLite database plus CellProfiler Analyst properties files [@Jones2008]. Non-SQLite databases, custom filters, workspace generation and some historical aggregation options remain unsupported.

The [integration workflow](../../.github/workflows/integration-tests.yml) defines Linux, Windows and macOS checks across Python versions, storage types, microscope inputs and installed desktop paths. The [30-workflow comparison](../../tests/integration/test_cellprofiler_official30_zmq.py) executes through ZeroMQ against retained native values. Full checks run nightly, on release tags and on demand; publication requires success on the release commit. Pull requests run focused checks. These automated checks are separate from timed benchmarks. The earlier [OpenHCS 0.8.5 release record](ci_official30_085/README.md) retains its own test results.

## Supplementary Data 2. Module coverage

Main Figure 6A assigns each of 85 modules its strongest available test: 54 in complete workflows, 29 in individual tests and two tested only through shared code. Shared-code tests do not establish that each module's own algorithm works. The [module table](../figures/slas/benchmark-publication/reference-layout/reference_module_coverage.csv) identifies the evidence for every module.

Older [module](../../benchmark/results/labmeeting_20260513/official30_well_throughput/figures/module_coverage_cppipe_modules.csv), [setting](../../benchmark/results/labmeeting_20260513/official30_well_throughput/figures/module_coverage_cppipe_settings.csv) and [registration](../../benchmark/results/labmeeting_20260513/official30_well_throughput/figures/module_coverage_absorbed_modules.csv) inventories are historical, not a current compatibility matrix. Registration and supported-setting categories are not output-equivalence tests, and their overlapping counts must not be added.

## Supplementary Data 3. Timing methods and additional charts

### Measured times

With one sample and one worker, median processing speedup was [pending]{.benchmark-claim key=execution_median}-fold (minimum [pending]{.benchmark-claim key=execution_min}); including pipeline setup, it was [pending]{.benchmark-claim key=total_median}-fold (minimum [pending]{.benchmark-claim key=total_min}). Main Figure 6B shows all 30 workflows.

OpenHCS times are medians of three repetitions after warmup. Setup includes client compilation and submission/wait; nested worker time is counted once. Both CellProfiler timing measures include its internal initialization. External application/server startup, OpenHCS library loading and warmup are excluded. Batches repeat the same image sample to measure processing, not biological variation.

With twelve samples held fixed, every workflow ran faster with two, three and four OpenHCS workers than with one, for processing alone and with setup included. These are measured times throughout (Supplementary Figure 6).

### Estimated CellProfiler times

Main Figure 6C estimates CellProfiler time for the same cores and samples as OpenHCS. It divides the work evenly among independent single-threaded processes, each paying its own initialization cost. For N samples and C processes:

`Estimated time = T8_first + (N/C − 8) × median(T8_warm)/8`

Here `T8_first` is the measured first eight-sample batch and `T8_warm` a later batch after initialization. Total time adds pre-pipeline overhead once per process. The estimate assumes no slowdown from running processes together. The measured eight-sample batch had one numerical thread with access to four cores; the estimate assumes that rate on one core per process. Matching multicore CellProfiler runs were not measured.

The [calibration](../../benchmark/results/matched_worker_sweep_20261008_latestproduction/calibration/cold_first/cold-first-model-validation.json) tested three workflows at 8, 12 and 16 samples. Maximum absolute prediction error was 7.06% using the same-session eight-sample model, versus 5.21% using a two-sample model; an earlier-session eight-sample model underpredicted by up to 14.03%. These are not multicore confidence intervals. Counts of 3, 4 and 6 samples per process fall below the validated range. Combined memory use was not measured.

### Data and chart links

- [Benchmark protocol](../../benchmark/results/matched_worker_sweep_20261008_latestproduction/README.md), [measured one- and eight-sample CellProfiler calibration](../figures/slas/benchmark-publication/native_actual1_actual8_calibration/actual_native_batch_calibration.csv), and [Figure 6 measured/estimated values](../figures/slas/submission_benchmark_summary_projection.csv).
- Every processing time and ratio: [variable batches](../figures/slas/benchmark-publication/may/execution/first_use_workflow_metrics.csv) and [setup plus processing](../figures/slas/benchmark-publication/may/total/first_use_workflow_metrics.csv).
- Twelve-sample OpenHCS scaling: [processing](../figures/slas/benchmark-publication/fixed12/execution/scaling/derived_workflow_metrics.csv) and [setup plus processing](../figures/slas/benchmark-publication/fixed12/total/scaling/derived_workflow_metrics.csv).
- Serial CellProfiler comparison: [all batch configurations](../figures/slas/supp_benchmark_assignments.png). Unlike main Figure 6C, CellProfiler stays serial.
- One-worker charts: [processing speedup](../figures/slas/benchmark-publication/serial_batch/execution/serial_cp_relative_speedup_log.png), [seconds per sample](../figures/slas/benchmark-publication/serial_batch/execution/serial_seconds_per_sample_log.png) and [reduction from batching](../figures/slas/benchmark-publication/serial_batch/execution/serial_amortization_factor.png). Corresponding [setup-plus-processing charts](README_before_readability_20261015.md#supplementary-figure-6-continued-one-worker-batch-comparisons) are retained separately.

In the one-worker twelve-sample charts, CellProfiler times are estimated from measured eight-sample batches; OpenHCS times are measured. Different CPU affinities in single-sample and batch captures mean these comparisons do not isolate initialization alone.

## Figure assembly and interface records

Figures reuse retained images and measurements; editorial changes do not rerun analyses or alter segmentation. The [figure generator](../figures/build_slas_supplement.py) and accompanying source records identify crops, display choices and original files. Lucide icons retain their [licence](../figures/assets/lucide/LICENSE).

Main Figure 1 uses the [two-plate capture](../figures/slas/figure1_two_plate_native_20261007/capture_evidence.json) and [custom-function form/code recording](../figures/slas/custom_extension_live_evidence.json). Gain 1.2 and offset 0.0 identify the same function in the form and [Python readback](../figures/slas/custom_extension_live_code_document.json). This demonstrates authoring; the function was not executed on an assay. A separate [interaction record](../figures/slas/authoring_verified_roundtrip_provenance.json) documents parameter changes propagating between Python and graphical controls.

## Supplementary Data 4. Public NeuronCyto demonstration and references

The [original gpt-5.6-sol demonstration](../../website/assets/agent/cold-start-workflow-record.json) used a method-directed brief specifying normalization, segmentation and neurite assignment. It produced nine neurons, ten nuclei, eight branches, 25 graph paths and 1,982 pixels of outgrowth. It demonstrates authoring and inspection, not unassisted method selection or manual-reference accuracy. A [later OpenHCS 0.8.5 replay](current_neurite_replay_summary.md) is recorded separately.

The NeuronCyto II publication [@NeuronCytoII] provides eight manually traced cell entries for image 1, aggregate length 3,832.601 in unspecified units, and three crossovers, of which its algorithm resolved two. Our two input TIFFs match the public image files byte-for-byte. Manual trace coordinates were not located; cell correspondence, length definitions and units remain unaligned.

A separate [image-1 comparison](neuroncyto_length_evaluation/conclusion.rst) found 4,085.1925 pixels of rooted outgrowth in the first H004 prediction. This is not an accuracy ratio against the published total. The [reference audit](neuroncyto_reference_audit.md) and [unit checks](neuroncyto_length_evaluation/unit_followthrough.rst) retain the evidence. The final attempted repair extended beyond the intended main-shaft target, which was clarified only after that run. Main Figure 4C–E shows the initial result, not the later revision.

Main Figure 4C–D and F–H use full-resolution raw arrays and saved paths identified by the [source manifest](../figures/slas/frozen_neurite_views.json). Figure 4E is the published algorithm's output, not manual ground truth: an unmodified embedded JPEG from the article, cropped to 450 pixels and attributed in the [source record](../figures/slas/neuroncyto_published_reference/source.json).

## Supplementary Data 5. Complex workflow imports

The [workflow report](complex_cellprofiler_workflows.md) lists imported steps and editable Python for the advanced-segmentation and 3D-monolayer tutorials. It checks that function identities and settings survive Python export and reload. These are import/editing checks; Supplementary Data 1 separately reports execution and output agreement.

## Supplementary Data 6. Workflow regression tests

The [Python-generation](https://github.com/OpenHCSDev/openhcs/blob/7a7d21fee726905b87b9020cebf0bdfc350631f4/tests/unit/test_pycodify_formatters.py), [function-validation](https://github.com/OpenHCSDev/openhcs/blob/7a7d21fee726905b87b9020cebf0bdfc350631f4/tests/unit/test_funcstep_contract_validator.py) and [catalogue-revision](https://github.com/OpenHCSDev/openhcs/blob/7a7d21fee726905b87b9020cebf0bdfc350631f4/tests/unit/test_function_catalog_zmq.py) tests cover inherited settings, reconstruction, invalid image dimensions/memory types and stale catalogue requests. These files are pinned to a revision unchanged from OpenHCS 0.8.5. The [test job](https://github.com/OpenHCSDev/openhcs/actions/runs/34870874969/job/104066142788) passed. These focused checks do not replace the real-workflow comparisons in Data 1.

## Supplementary Data 7. Earlier held-out analyses

Each fresh gpt-5.6-sol author used four development fields or wells, then fixed its method before receiving the held-out inputs. [Final pipelines and scores](independent_validation/README.md) and the [validation report](independent_agent_validation.md) preserve that prospective design.

| Analysis | Held-out data | Result |
| --- | --- | --- |
| Nuclear detection 1 | 50 BBBC039 fields | 4,733 of 5,720 reference nuclei matched; precision 0.680, recall 0.827, F1 0.746; mean field Dice 0.935. |
| Cell-boundary analysis 1 | 12 BBBC007 fields | 29,450 of 43,875 predicted border pixels within two pixels of a manual outline: 0.671. |
| Protein translocation 1 | 92 BBBC013 wells | 14,262 cells measured; Z′ 0.751 for Wortmannin and 0.554 for LY294002. |

Precision is the fraction of detections matched to references; recall is the fraction of references found. F1 balances both, and Dice measures area overlap; 1 is best for each. Nuclear matching required intersection over union ≥ 0.5. The nuclear analysis predicted 6,964 objects and often split reference nuclei, despite high area overlap.

Boundary agreement checks predicted borders only; it does not show that every manual border was recovered or that cells match one-to-one. The cell-boundary analysis predicted 1,274 nuclei and 1,273 cells; every nucleus overlapped a cell. Manual outlines enclosed 1,082 closed nuclear interiors, excluding 12 open/frame-connected regions.

Protein translocation analysis 1 used each well's mean cell-level nuclear/cytoplasmic GFP ratio. Positive/negative control means were 7.235/0.915 for Wortmannin and 7.219/1.127 for LY294002. Z′ measures their separation relative to well variation; both exceeded 0.5. BBBC013 has no manual masks for segmentation scoring. Analysis 2 instead used median log2 ratios on 96 wells including development, so the two results are not a controlled before–after comparison.

## Supplementary Data 8. Agent-developed analyses

### Results and reference types

Names identify the task; numbers distinguish independently developed methods. Corrections remain part of the same analysis. **Held-out** means the method was fixed before those inputs were released. **Uninspected** means the agent did not open those fields during development, determined retrospectively. **Development** results may include images used to choose the method.

| Assay | Model | Data partition | Endpoint | Result |
|---|---|---|---|---|
| Nuclear detection 1 (BBBC039) | gpt-5.6-sol | 50 held-out fields | Object F1; foreground Dice | 0.746; 0.935 |
| Nuclear detection 2 (BBBC039) | gpt-6.1-sol | 175 uninspected; all 200 fields | Pooled object F1, respectively | 0.910; 0.906 |
| Nuclear detection 3 (BBBC039) | gpt-6.1-sol | 175 uninspected; all 200 fields | Pooled object F1, respectively | 0.906; 0.898 |
| Nuclear detection 4 (BBBC039) | gpt-6.1-sol | 175 uninspected; all 200 fields | Pooled object F1, respectively | 0.906; 0.904 |
| Nuclear detection 2, repair | gpt-6.1-sol | Same three development fields | Object F1, first to final | 0.908 to 0.934 |
| Cell-boundary analysis 1 (BBBC007) | gpt-5.6-sol | 12 held-out fields | Directed boundary fraction | 0.671 |
| Cell-boundary analysis 2 (BBBC007) | gpt-6.1-sol | 16 fields including development | Directed boundary fraction | 0.743 |
| Cell-boundary analysis 3 (BBBC007) | gpt-6.1-sol | 16 fields including development | Directed boundary fraction | 0.740 |
| Paired nuclear/cell detection (H003) | gpt-6.1-sol | One development field | Nuclei; actin-supported cells | 56; 54 |
| Protein translocation 1 (BBBC013) | gpt-5.6-sol | 92 held-out wells | Control Z′, Wortmannin; LY294002 | 0.751; 0.554 |
| Protein translocation 2 (BBBC013) | gpt-6.1-sol | 96 wells including four development wells | Control Z′, LY294002; Wortmannin | 0.849; 0.726 |
| Bright-object detection 1 (H001) | gpt-6.1-sol | One development image | Computational-reference F1, first to final | 0.929 to 0.944 |
| Bright-object detection 2 (H001) | gpt-6.1-sol | One development image | Final labels; matched image review | 62; no reference score |
| 3D nuclear localisation 1 (H002) | gpt-6.1-sol | One development volume | Centres within 30 voxels; mean matched error | 15 of 15; 4.80 voxels |
| 3D nuclear localisation 2 (H002) | gpt-6.1-sol | One development volume | Centres within 30 voxels; mean matched error | 15 of 15; 4.86 voxels |
| Retinal cell detection 1 | gpt-6.1-sol | One development field | Detected objects; image review | 102 |
| Retinal cell detection 2 | gpt-6.1-sol | One development field | Candidates; border candidates | 136; 10 |
| Public-image neurite tracing | gpt-6.1-sol | One development field | Principal-shaft recovery | Matched image review |
| Laboratory-image neurite tracing | gpt-6.1-sol | Nine development fields | Soma and path recovery | Matched image review |
| Neurite drug-response analyses 1–3 | gpt-6.1-sol | 180 fields each; six/four/eight development fields | Control-normalized outgrowth response | Both drug responses recovered by all three; magnitudes varied |

Object scores use computational labels for H001 and independent nuclear annotations for BBBC039. BBBC007 uses manual outlines; H002 has partial manual centre annotations. Retinal and neurite demonstrations without spatial ground truth are evaluated by paired raw/result review, not an accuracy percentage.

### Errors that remain

Eleven predictions in 3D nuclear localisation analysis 1 had no matching annotation. Because the annotations cover only some centres, these cannot be classified as false detections from this reference alone. The 3D split-cell repair in main Figure 5H is a separate analysis. Retinal examples include uncertain borders, and paired DNA/actin examples include a faint merged pair and a nuclear seed without supported cell-body growth (Supplementary Figure 4).

Across the 175 uninspected BBBC039 fields, missed nuclei made up 73–78% of the three agents' errors:

| Agent | Fields with F1 ≥ 0.90 | Fields below 0.80 | Median field F1 | Missed nuclei | False detections | Fields with more misses than false detections |
|---|---:|---:|---:|---:|---:|---:|
| Nuclear detection 2 | 121 | 6 | 0.919 | 2,661 | 951 | 171 |
| Nuclear detection 3 | 117 | 7 | 0.917 | 2,929 | 806 | 173 |
| Nuclear detection 4 | 121 | 6 | 0.915 | 2,743 | 1,033 | 171 |

The same six fields scored below 0.80 for all three agents. In the hardest field, all missed 57–59 of 69 nuclei. The [per-field table](task_only_analysis/bbbc039-uninspected-fields.csv) identifies those images. On three inspected fields, analysis 2's repair recovered 14 missed nuclei and raised F1 from 0.908 to 0.934, but split reference nuclei increased from 28 to 43. That repair was not separately evaluated across all fields.

A further [paired-channel analysis](task_only_analysis/h003-fresh26-qualified-completion.rst) recovered three crowded nuclear omissions and removed two cells without actin-supported growth, leaving 56 nuclei and 54 cells. [Cell-boundary analysis 3](task_only_analysis/bbbc007-fresh26-final-candidate.rst) produced 1,428 nuclear and cell IDs across sixteen fields, with remaining merge/boundary uncertainty. Retinal source images were user-provided R0010 RBPMS images with unverified physical calibration; DNA/actin images were BBBC007v1 A02 from the Sabatini laboratory, Whitehead Institute (CC0).

The [assisted nine-field mosaic](../figures/slas/p001_stitched_dev13_native.png) is development work, not another fresh autonomous trial. Its [continuation](task_only_analysis/p001-allchannel25-qualified-completion.rst) reported 1,740 soma candidates and 123,054 µm of computed outgrowth, but overlapping fields, uncertain ownership and absent spatial ground truth prevent interpreting those totals as a unique biological census.

### Instructions and reproducibility

The [original instruction archive](task_only_analysis/original_task_briefs.json), [trial resource table](task_only_analysis/trial_resources.csv) and [neurite cohort record](personal_neurite_autonomous/cohort.json) identify briefs, model/software versions, timing and retained outputs. Nuclear detection analyses 2–4 received different guide revisions; the three drug-response analyses received the same revision. Guide versions and original instruction files were not retained for the three earlier held-out analyses.

Briefs supplied biological tasks and, in some cases, technical guidance: source bindings and allowed catalogue tracks, nuclear/cytoplasmic GFP measurement, seeded cell segmentation or channel hints. These were not tests of scientists writing completely unaided prompts. An archived retinal brief mentions inherited conversation, but launch records for retinal analyses 1–2 show fresh sessions with memory disabled; other trials attached to that brief were not checked. The current guide includes later improvements and must not be treated as the exact guide given to earlier agents. The [earlier supplement](README_before_readability_20261015.md#scientific-instructions-supplied-to-authors) summarizes all sixteen briefs.

| Analysis | Final pipeline |
|---|---|
| Bright-object detection 2 | [Source](task_only_analysis/pipelines/h001-fresh25.py) |
| 3D nuclear localisation 2 | [Source](task_only_analysis/pipelines/h002-fresh23.py) |
| Paired nuclear/cell detection | [Source](task_only_analysis/pipelines/h003-fresh26.py) |
| Retinal cell detection 2 | [Source](task_only_analysis/pipelines/retina-fresh26.py) |
| Public-image neurite tracing | [Source](task_only_analysis/pipelines/h004-fresh20.py) |
| Protein translocation 2 | [Source](task_only_analysis/pipelines/bbbc013-fresh23.py) |
| Nuclear detection 2 | [Source](task_only_analysis/pipelines/bbbc039-fresh612.py) |
| Nuclear detection 3 | [Source](task_only_analysis/pipelines/bbbc039-fresh10.py) |
| Cell-boundary analysis 3 | [Source](task_only_analysis/pipelines/bbbc007-fresh26.py) |

The [nine-field neurite pipeline](task_only_analysis/pipelines/p001-fresh13.py) is also supplied. These are the agents' selected sources, unchanged by reference scoring. Reproduction requires the recorded software and inputs; relocate file destinations and viewer endpoints without changing scientific settings.

Additional supplied dependencies are the BBBC039 [image metadata](task_only_analysis/pipelines/bbbc039/source_manifest.csv) and [source binding](task_only_analysis/pipelines/bbbc039/source_bindings.py), BBBC007 [paired-field metadata](task_only_analysis/pipelines/bbbc007/source_sets.csv), 3D [centre-detection function](task_only_analysis/pipelines/h002-fresh23/custom_function.py), and translocation [compartment measurements](task_only_analysis/pipelines/bbbc013-fresh23/bbbc013_compartment_qc_v4.py), [statistics](task_only_analysis/pipelines/bbbc013-fresh23/bbbc013_assay_statistics_v1.py) and [dose summary](task_only_analysis/pipelines/bbbc013-fresh23/bbbc013_dose_response_v2.py). Register custom functions under their recorded names before validation and execution. The original records identify which trial each source supports; the retinal and 3D sources above are not the distinct trials shown in Supplementary Figure 4 and main Figure 5, respectively.

Original attempts, unsuccessful revisions and complete source inventories remain in the [earlier supplement](README_before_readability_20261015.md) and its linked records. They are not additional experimental replicates.
