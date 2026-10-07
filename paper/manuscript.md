---
bibliography: openhcs_references.json
csl: styles/elsevier-vancouver.csl
reference-section-title: References
link-citations: true
link-bibliography: true
---

# OpenHCS: autonomous image analysis that domain experts can audit

**Authors:** Tristan Simas, Jathav Puvirajan, and Alyson Fournier

**Affiliation:** McGill University, Montreal, Quebec, Canada

**Correspondence:** Tristan Simas, <tristan.simas@mail.mcgill.ca>

**Short title:** OpenHCS: autonomous microscopy analysis

**Keywords:** microscopy; image analysis; self-driving laboratory; autonomous analysis; agentic AI; high-content screening

## Abstract

Turning microscopy images into measurements takes specialist decisions about channels, preprocessing, segmentation and quality control. We developed OpenHCS so an AI agent can build and repair an analysis from a task brief while the scientist inspects images, masks and measurements in napari or Fiji and edits the same pipeline through a GUI, Python or the Model Context Protocol. All 30 imported CellProfiler workflows reproduced the compared native outputs, exactly for labels and within 1e-6 for measurements. One-core execution was a median [TODO: refreshed execution speedup, matched benchmark]-fold faster. Blind agents received a task brief, packaged guidance and MCP access and finalized their pipelines before reference scoring. On 175 BBBC039 fields that none of the three agents opened, nuclear segmentations reached pooled object F1 of 0.906 to 0.910. [TODO: choose held-out or later translocation Z′ results with Tristan.] Agents also localized 3D nuclear centres and recovered retinal cell bodies and principal neurite shafts; assigning neurites at crossings remains open. Scientists can delegate analysis construction and execution and keep the images and settings needed to judge the result.

## Introduction

An investigator may know which cells, neurites or subcellular signals matter to an experiment without knowing how to turn their images into reliable measurements. Image analysis adds specialist decisions: identifying channels, choosing preprocessing, setting segmentation parameters and checking results across samples. A pipeline that executes successfully can still miss dim structures or divide a cell incorrectly. Delegating this work therefore requires more than a table of answers. The investigator needs to see what was measured and decide whether it represents the biology.

OpenHCS lets an agent construct and repair an analysis from a task brief while the scientist inspects the images, masks and measurements in familiar viewers. GUI controls, Python and MCP edit one pipeline (Figure 1). Function signatures and docstrings supply the controls and agent-facing descriptions, so laboratory Python functions and imported CellProfiler workflows enter the same analysis. The scientist can revise settings and rerun the pipeline as the experiment changes.

Fiji/ImageJ, CellProfiler, Icy and BioImageIT provide desktop processing workflows, and napari supports multidimensional inspection [@Schneider2012; @Schindelin2012; @Carpenter2006; @McQuin2018; @deChaumont2012; @Prigent2022; @Napari]. MCMICRO combines interchangeable modules for multiplexed tissue imaging [@Schapiro2022]; OpenHCS connects processing, source images and viewers through one editable pipeline. BioImage.IO Chatbot connects community resources to analysis extensions, Omega generates and runs Python in napari, and Agentic-J generates scripts and coordinates Fiji tools with debugging and quality-assurance agents [@Lei2024; @Royer2024; @Johanns2026]. OpenHCS gives agents the same validated workflow that scientists edit, allowing submitted settings and intermediate images to be inspected directly. [TODO: BIABench citation and finding, from the primary autonomous-evaluation paper.]

We compared imported workflows with native CellProfiler outputs, measured execution and compile-plus-run time, and tested blind agents constructing and repairing analyses from task briefs. Reference annotations, well-level assay responses and matched image review supplied task-specific endpoints. Self-driving laboratories need unattended image analysis to turn microscopy into measurements for the next experiment. SiLA-based systems connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]; OpenHCS supplies the analysis step while the scientist chooses the biological question.




## Materials and Methods

### Pipeline model

An OpenHCS pipeline is an ordered sequence of functions and settings: for example, selecting a nuclear channel, segmenting nuclei and measuring the resulting labels. Steps use shared defaults unless they declare overrides.

Compilation identifies each step's inputs, checks compatibility and prepares function calls, array conversions and output destinations, resolving defaults and overrides. Workers receive this prepared plan (Supplementary Figure 1).

Function signatures supply parameter names, types and defaults for the controls and editable Python. Backend declarations permit conversions between compatible CPU, GPU and deep-learning libraries. Functions declare whether they support volumes or image planes.

Registering a custom function adds it to the editor and MCP catalog; its signature and docstring supply controls and searchable descriptions (Figure 1II).

Source mappings select channels, planes or stacks and divide images into processing groups. Later steps inherit or replace these choices. Sample, site, channel, plane and time identities remain separate from storage paths, linking measurements to their source images through stacking and processing.

Microscope handlers interpret acquisition-specific layouts and metadata. Bio-Formats-backed discovery provides image-plane records from microscopy containers. The OME-Zarr source reads declared axes, channels, pixel scale and image or plate structure. Explicit source mappings assign roles where acquisition metadata are insufficient. Experimental OMERO support supplies managed images and metadata through the same source model.

Reusable libraries supply discovery, settings, generated interfaces, array conversion, storage and process coordination; OpenHCS supplies microscopy functions, source handlers and viewers (Supplementary Table 1).

### Execution and viewers

Steps produce named images, labels, measurements, object relationships and files. Function contracts declare inputs and outputs; compilation connects later operations to their sources. Results retain the producing step, source coordinates and processing group. Saving and viewer delivery are independent choices (Supplementary Data 4).

napari and Fiji receive selected outputs together with their source coordinates and producing step. The streaming service checks that each viewer is ready and waits for pending display updates to finish. Viewer sessions remain available for inspection after execution. Local files, in-memory data, Zarr-backed stores and OMERO provide storage routes; the OME-Zarr array source is read-only.

The execution server coordinates analysis runs and remains available between requests. Within a run, each worker processes its assigned samples using the prepared plan and reuses loaded libraries and initialized array backends. Worker resources are released when that execution finishes. Worker count controls how many samples can be processed concurrently. Workers normally run in separate processes; a configuration option selects threads instead.

### Agent access through MCP

Through MCP, an AI client requests defined operations for discovering functions, editing and validating pipelines, running analyses, and inspecting progress and results [@MCP]. Each operation's declaration specifies its request and result types, implementation, changes it can make, data access and security requirements. The MCP interface is generated from these declarations, which also govern execution.

Function-discovery operations return descriptions derived from registered processing functions. An agent uses those descriptions to select functions and edit the shared workflow. Registering an additional function makes it available through the existing catalog and workflow operations without requiring a function-specific MCP tool.

Desktop operations edit and run the live workflow; headless operations use a separate execution context. Local clients use standard input/output. Desktop connections are authenticated, stale workflow revisions are rejected, and file access is restricted to permitted paths. Hosted HTTP provides selected read-only operations in isolated workspaces.

### Figure 2. One editable workflow connects editing, execution and inspection

![Shared editing, execution, workers, viewers and image storage.](figures/slas/shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
Forms, Python and MCP act on one editable workflow; CellProfiler imports enter the same definition. The ZeroMQ execution server compiles pipelines, coordinates workers and returns progress to the editor. Workers read source images, save outputs and stream results to separate napari or Fiji viewers. Logos identify import, storage, processing and viewing integrations, not separate analysis steps. CPU/GPU support depends on the selected functions; OMERO support is experimental. Supplementary Figure 1 expands the runtime and preparation details.
:::

### CellProfiler import and output comparison

CellProfiler `.cppipe` files are parsed into modules and settings. Setup modules define image sources; registered processing and export modules become editable OpenHCS steps. Each module declaration specifies the images, objects, measurements and relationships its function needs, together with whether it runs per image group or across the plate. The same function is exposed in the GUI, Python and MCP.

Named images and objects connect imported measurements to their inputs, as illustrated by the Comet Assay (Supplementary Data 4). For the advanced segmentation and 3D monolayer tutorials, reloading generated Python checked preservation of function identities and parameters [@CellProfilerTutorials]. Supplementary Data 5 provides their step sequences and source records.

Comparisons use absolute and relative tolerances of `1e-6` for numerical values and image pixels, with no out-of-tolerance pixels; identifiers and categorical values are compared exactly after documented CellProfiler-compatible normalizations. Object-label images are compared exactly after singleton-axis normalization. For five workflows lacking exports, terminal image or object-label exports supplied reference artifacts without changing their processing settings. Supplementary Data 1 records export definitions, output inventories, software versions and historical release-CI results; Supplementary Data 2 documents the imported corpus and setting coverage.

### Autonomous trial design

Three prospective public-assay trials gave fresh gpt-5.6-sol agents a bounded development partition, biological task, channel identities and desktop/MCP access. Annotations, treatment metadata, held-out images, evaluation code, earlier pipelines and repository source were withheld. Functions and parameters were frozen before disclosing held-out paths; evaluation changed only input and output roots. These were single attempts, not estimates of reliability. Supplementary Data 7 retains partitions, original archives and evaluation artifacts.

The primary outcome is the author's final frozen result after its own inspection
and repairs. Self-directed iteration remains autonomous when the author receives
no external scientific corrections or reference feedback. First-attempt results
describe initial method selection and the extent of repair, not the criterion
for autonomous success. Continuations receiving external scientific corrections
provide assisted-development evidence and are reported separately.

The scientific brief states the target and requested outputs; acquisition facts and operational instructions accompany it. For example, the retinal trial requested: “Produce RBPMS-positive soma instance labels, per-object measurements, qualified counts and a complete PipelineDocument with compile/execution receipts. Report uncertain identity, extent and dividing boundaries explicitly.” Its brief also supplied RBPMS/Hoechst channel hints and instructed metadata confirmation. These are biological targets with technical output and review requirements, not an unrestricted natural-language usability test. The inspected original briefs and their technical hints are retained in Supplementary Data 8.

The packaged skill describes the specialist workflow: inspect channels and representative raw regions, measure feature scales, retrieve applicable function contracts, build and execute a pipeline, and compare matched raw-only, result-only and combined views. It calls for diagnosis at the earliest failing stage, rechecking a positive and a regression control, and retaining the author's selected frozen result. These instructions describe intended practice; the recorded attempts and captures establish which actions each author actually performed. General lessons can improve a later frozen skill, but reference answers and dataset-specific settings remain outside fresh authoring inputs.

Fresh gpt-6.1-sol agents received the brief, packaged skill and MCP, but no reference labels or accepted settings. Public assay briefs included catalogue tracks and typed source bindings; BBBC007 specifically requested seeded-cell segmentation. Authors retained attempts, tool calls and matched views. The coordinator evaluated frozen predictions after authoring ended, without returning scores. These trials are distinct from the earlier prospective held-out evaluation (Supplementary Data 8).

We compared first completed scientific settings with the final settings on exactly the same inputs. Technical corrections needed to submit or execute a pipeline remain part of the record; the first completed prediction is not necessarily the first tool call. H001 used a single notebook-derived bright-object image and its predeclared computational label reference. BBBC039 used independent nuclear annotations, with a paired first/final comparison on three fields and a separate final evaluation across all 200 fields. Some of those fields were inspected during development, so the 200-field result measures reference agreement rather than unseen generalization. Existing instance scorers used one-to-one matching at intersection over union at least 0.5.

| Input and task | Evaluation evidence | Supported result and limit |
|---|---|---|
| H001 bright objects | Pinned notebook instance labels | Object F1 after one-to-one matching; computational reference, not manual biological truth |
| BBBC039 nuclei | Independent instance annotations; full corpus and retrospective image-uninspected subset | Pooled object F1; development and retrospective uninspected subsets distinguished |
| BBBC007 DNA/actin | Manual-outline union | Fraction of predicted boundary pixels near the reference; not boundary recall or exhaustive instance accuracy |
| H002 3-D centres | Manual centre annotations | Matched-centre voxel distance; annotations not established as exhaustive |
| R0010 retinal somata | Distributed matched raw/result review | Autonomous repair retained neighbours and reduced nuisance masks; manual-reference accuracy unmeasured |
| H004 public neurites | Matched raw shafts and nuisance controls | Retained initial principal-shaft recovery; final repair exceeded the shaft target, and per-neuron crossing ownership remains unresolved |
| Laboratory neurites, nine fields | Matched raw/path review in three sampled fields | Autonomous completion and recovery of thin paths after self-directed repair; overlapping fields not stitched or deduplicated, per-neuron ownership unresolved |
| Laboratory neurites, 20-well transfer | MetaXpress well responses; two technical wells per drug/concentration | Concordant positive outgrowth responses with smaller estimated fold changes; assisted transfer, not a separate autonomous authoring trial or manual-trace score |
| BBBC013 translocation | Well-level control and dose summaries; 96 wells | Assay responses recovered in contributing cohorts; compartment coverage varied and whole-cell accuracy unmeasured |

Table 1. Endpoints, references and scope of autonomous image analysis.

Predictions were frozen before reference comparison; scores were not returned to authors. Visual-review rows provide no numerical accuracy estimate.


For BBBC039, we also scored the frozen final predictions on fields whose images
were not opened by the analysis agents. Original image-delivery records excluded
25 fields opened by at least one of the three agents, leaving a common 175-field
comparison. This retrospective subset is distinct from the prospectively
withheld images above. Supplementary Data 8 records the exclusions, frozen
predictions and each trial's wall time, model and software versions. We report
recorded input, cached-input and output tokens as computational usage. For
selected independent trials, the supplement also estimates API-dollar and
Codex-credit equivalents at published rates observed on 6 October 2026.
These rate scenarios are not actual subscription charges; billing amounts
were not recorded.

### Endpoints and references

BBBC039 supplied four development and 50 held-out fields with independent nuclear instance annotations. One-to-one matching used an intersection-over-union threshold of 0.5; reported measures include object precision, recall and F1, foreground Dice, signed count error, and explicitly defined split and merge diagnostics. BBBC007 supplied four development and 12 held-out DNA/actin fields with manual outlines. Its directed boundary measure reports the fraction of predicted adjacent-cell boundary pixels within two pixels of the manual-outline union. The outlines do not provide exhaustive object correspondence, so this score is not an instance-accuracy estimate.

BBBC013 supplied four development and 92 held-out wells from a two-drug FKHR-GFP translocation assay. The frozen endpoint was the per-well mean of cell-level mean nuclear GFP divided by mean cytoplasmic GFP. Each cell required the same retained object identity in the nuclear and cytoplasmic measurements. Z-prime used sample standard deviations across the four positive and four negative control wells for each drug; cells were not treated as independent replicates. BBBC013 provides treatment truth rather than manual segmentation truth. Prediction bytes were frozen before the evaluator opened held-out annotations or treatment metadata. The exact pipelines, typed score receipts, limitations and infrastructure repairs are retained in Supplementary Data 7.

H001 used a notebook-derived bright-object image and a predeclared computational label reference, scored by one-to-one object matching. H002 used manual centre annotations and a 30-voxel matching radius; distances are reported in voxels. [TODO: H002 precision, from annotation of 11 unmatched centres.]

Retinal soma and neurite analyses were assessed with matched raw, result and combined views across multiple regions. [TODO: retinal soma reference, from hand-marked centres in four to six crops.] [TODO: neurite ownership reference, from crossing labels in two to three fields.]

### Performance measurement

The matched single-sample evaluation used CPU execution with one worker and one numerical thread on one physical core. OpenHCS revision [pending]{.benchmark-claim key=source_revision} ran with Python 3.12; native CellProfiler 4.2.8.1 ran with Python 3.9 in its separate environment. Each workflow used one selected source well or sample, which can contain multiple image sets, with unchanged processing settings and the declared comparison outputs. A warmup preceded three measured repetitions. Complete retained native observations were reused only after the workload, inputs, outputs, software environment and hardware checks passed; OpenHCS observations were acquired on the same clean source revision across all 30 workflows.

Execution timing covers the native pipeline call, including preparation of the run and groups, module processing and post-run work; OpenHCS timing covers the complete server execution job, including ordinary output publication and plate exports. Process, JVM and execution-server startup, function-library readiness, warmup and scientific comparison are excluded. The separate total metric compares the prepared native invocation with the sum of disjoint OpenHCS client compilation and execution submission/wait phases. Nested server and worker durations are not added again. Each workflow's speedup is the ratio of the two engines' independently calculated median durations; the reported cohort median is the median of those 30 ratios. Original reports, summaries, source checksums and figure provenance are retained with the matched benchmark record.

Historical performance protocols and their different timing and output policies are retained in the supplement. They are not combined with the matched execution and total-time comparisons.

## Results

### Scientists and agents revise the same analysis

One workflow supplies the desktop controls, generated Python and MCP operations (Figure 1). In a code-to-control check, an MCP request changed the normalization step's high percentile from 99.8 to 99.6 and the form showed 99.6. A field-edit request restored 99.8, and generated Python contained the restored value (Supplementary material, Figure assembly and interface records). Scientists can open an agent-authored pipeline, inspect linked images and measurements in napari or Fiji, and revise the settings before rerunning it. Figure 2 shows how the editor, execution server and viewers share this workflow.

### Figure 1. Scientists can inspect and edit the agent's analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(I)** Native OpenHCS 0.8.7 workspace with ExampleHuman and ExampleFly folders loaded and the editor displaying the nine-step ExampleHuman recipe. One continuous crop of the 2048 × 1536 capture excludes the monitoring dashboard; no stitching, vertical stretching or duplicate insets are used. Blue outlines identify existing controls. This authoring demonstration did not execute analysis or restart the execution service. Full original capture and earlier editing records: Supplementary Data 3.
:::

### Figure 1, continued. The laboratory's own Python joins the shared analysis

![Real Python declaration and docstring, generated controls, live editable Python and agent-facing parameter descriptions.](figures/slas/submission_custom_function.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(II)** The syntax-highlighted `paper_rescale_signal` declaration, including its NumPy backend decorator and docstring, supplies the shown form defaults and MCP descriptions; no function-specific form or tool was written. Native OpenHCS 0.8.7 form and code views show the same function with gain 1.2 and offset 0.0, verified against its code-document readback. These records establish authoring, not assay execution or a parameter-editing round trip. Supplementary Data 3 retains capture records and limitations.
:::

### Autonomous analysis

Table 2. Autonomous-analysis trial summary. Uninspected fields were selected retrospectively; held-out partitions were withheld prospectively. [TODO: complete author-by-author rows and skill versions from Supplementary Data 7–8.]

| Assay | Model | Data partition | Endpoint | Result |
|---|---|---|---|---|
| BBBC039, earlier trial | gpt-5.6-sol | 50 held-out fields | Object F1; foreground Dice | 0.746; 0.935 |
| BBBC039, three later authors | gpt-6.1-sol | 175 commonly uninspected fields | Pooled object F1 | 0.906 to 0.910 |
| BBBC039, three later authors | gpt-6.1-sol | 200 fields including development | Pooled object F1 | 0.898 to 0.906 |
| BBBC039, paired repair | [TODO: model, Supplementary Data 8] | Same three development fields | Object F1, first to final | 0.908 to 0.934 |
| BBBC007, earlier trial | gpt-5.6-sol | 12 held-out fields | Directed boundary fraction | 0.671 |
| BBBC007, two later authors | [TODO: models, Supplementary Data 8] | 16 fields including development | Directed boundary fraction | 0.743 and 0.740 |
| BBBC007, paired field | [TODO: model, Supplementary Data 8] | One development field | Nuclei; actin-supported cells | 56; 54 |
| BBBC013, earlier trial | gpt-5.6-sol | 92 held-out wells | Control Z′, Wortmannin; LY294002 | 0.751; 0.554 |
| BBBC013, later trial | [TODO: model, Supplementary Data 8] | 96 wells including four development wells | Control Z′, LY294002; Wortmannin | 0.849; 0.726 |
| H001 | [TODO: model, Supplementary Data 8] | One development image | Computational-reference F1, first to final | 0.929 to 0.944 |
| H002 | [TODO: model, Supplementary Data 8] | One development volume | Centres within 30 voxels; mean matched error | 15 of 15; 4.80 voxels |
| Retina, repair trial | [TODO: model and context classification, original launch] | One development field | Detected objects; image review | 102 |
| Retina, repeat trial | [TODO: model and context classification, original launch] | One development field | Candidates; border candidates | 136; 10 |
| Public neurites | [TODO: model, Supplementary Data 8] | One development field | Principal-shaft recovery | Matched image review |
| Laboratory neurites | [TODO: model, Supplementary Data 8] | Nine development fields | Soma and path recovery | Matched image review |
| Additional authors and models | [TODO: new trial sources] | [TODO: partition] | [TODO: endpoint] | [TODO: result] |

The earlier prospective trials recovered nuclear foreground and translocation responses but over-segmented nuclear instances and left uncertain actin-defined boundaries. On held-out fields, BBBC039 pooled object F1 was 0.746 and foreground Dice was 0.935; BBBC007's directed boundary fraction was 0.671. Across 92 BBBC013 held-out wells, control Z-prime was 0.751 for Wortmannin and 0.554 for LY294002. These single-attempt trials are distinct from the later self-repair evaluations below. Supplementary Figures 2–3 and Supplementary Data 7 provide counts, scoring definitions and treatment summaries.

Three independent nuclear-analysis authors reached pooled object F1 of 0.906 to 0.910 on the 175 BBBC039 fields none of them opened. Across all 200 fields, including development fields, F1 was 0.898 to 0.906 (Figure 4B). A same-input repair raised F1 from 0.908 to 0.934 on three fields. In the full-corpus repeat, 61 fields improved, 123 decreased and 16 were unchanged (Supplementary Figure 3). The earlier gpt-5.6-sol trial reached F1 0.746 and foreground Dice 0.935 on 50 prospectively held-out fields (Table 2). [TODO: field-level error pattern, from the per-field scores and matched images.]

Two later BBBC007 authors reached directed boundary fractions of 0.743 and 0.740 across 16 DNA/actin fields; the earlier held-out trial reached 0.671 across 12 fields (Figure 4C; Table 2). In one paired-field analysis, the agent detected 56 nuclei and kept 54 actin-supported cells after removing two seed-only candidates. Each cell mask included all pixels of its associated nucleus. Figure 4F shows a same-region merge repair.

The later BBBC013 author completed all 96 wells and obtained control Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 4E). Cytoplasmic compartments were eligible for 14,631 of 17,320 nuclei (84.5%). The agent selected the per-well median eligible-cell log2 nuclear-to-cytoplasmic GFP ratio. Four wells contributed to each treatment group. The earlier held-out trial obtained Z′ of 0.751 for Wortmannin and 0.554 for LY294002 across 92 wells (Table 2).

The H002 author recovered all 15 annotated 3D centres within 30 voxels, with mean matched error of 4.80 voxels (Figure 4D,I). Eleven predictions had no matching annotation. A different author repaired an internal body partition at Z=36 while keeping its neighbour separate (Figure 4H). [TODO: precision, from classification of the eleven unmatched predictions.]

The retinal repair trial detected 102 objects after improving fragmented soma footprints while keeping a neighbouring pair separate (Figure 4G). A repeat detected 136 candidates, including ten at the border. Distributed raw/result review covered bright somata, diffuse rings and crowded regions (Supplementary Figure 4). [TODO: independent versus inherited-context classification of these trials, from original launch records and Tristan's decision.] [TODO: manual-reference result, from annotated soma centres.]

One autonomous author analysed all nine laboratory neurite fields and revised its neurite admission settings after inspecting thin processes (Figure 5II). Matched sparse and dense views showed recovery of raw-visible paths with the same soma labels in the reviewed field. In the public NeuronCyto II field, the initial pipeline recovered principal shafts and junctions (Figure 5I); the final repair extended beyond that target. The initial result is shown alongside the published algorithm output. [TODO: spatial ownership comparison, from crossing annotations.]

The H001 author matched 59 of 64 computational-reference objects and raised F1 from 0.929 to 0.944 through self-directed repair (Figures 3B and 4A). The matched views show correction of an elongated object's split and recovery of a pair lost during an intermediate revision.

### Figure 3. Delegated specialist work leaves an analysis the scientist can inspect

![Skill-directed workflow with Fiji and napari inspection, followed by the recorded H001 decisions and matched raw/repair images.](figures/slas/submission_autonomous_loop.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Licensed pictograms and Fiji/napari logos show the packaged skill's intended workflow: biological brief, input inspection, pipeline execution, matched-view audit, targeted repair and delivery. (B) Recorded H001 decisions across four executions, with the same region shown raw, first (a01) and final (a04). The elongated body's split is repaired; colours are not shared object identities. The report also records recovery of a pair lost during revision. Catalogue times include review, reporting and cleanup. This example does not establish universal adherence to the current skill.
:::

### Figure 4. Quantitative results and matched image-repair evidence

![Task-specific nuclear, boundary, volume and translocation endpoints alongside an independent DNA/actin merge repair.](figures/slas/submission_analysis_summary.png){width=6in}

::: {custom-style="ImageCaption"}
**(A)** H001 first/final computational-reference F1 (one image). (B) Three BBBC039 authors, all 200 and 175 commonly uninspected fields. (C) BBBC007 boundary agreement: field dots and pooled-pixel lines. (D) H002 matched-centre errors and recovered references. (E) BBBC013 dose means/sample SD, four wells per dose; control Z-prime uses four positive/four negative wells. (F) An independent, uncoached BBBC007 author (H003_POSTPAUSE_88) repairs a local merge in the same C4 region, from candidate01_retry01 to candidate06. The lower object retains bridge support and another regional merge remains unresolved; this is within-run repair, not ground-truth segmentation accuracy. Colours are not shared identities. References differ across endpoints; none is a pooled accuracy score. Evaluation records: Supplementary Data 8.
:::

### Figure 4, continued. Repairs and volumetric localisation

![Matched retinal and volumetric body repairs, with separate frozen three-dimensional localisation evidence.](figures/slas/submission_quantitative_results.png){width=6in}

::: {custom-style="ImageCaption"}
**(G)** Same-input retinal raw/first/final views: fragmented footprints improve while neighbours remain separate. Border and weak-body coverage remain uncertain; this is continuation, not a fresh trial. (H) An independent 3-D author repairs a body partition at Z=36, not the complete volume. (I) A separate frozen analysis: XY labels and post-freeze XZ/YZ outlines (yellow), with in-plane centres (magenta). Fifteen manual centres were recovered; eleven further predictions have no matching annotation of established coverage. Distances are voxels, not micrometres. Colours do not identify objects across attempts. Wider views and remaining errors: Supplementary Figures 3–4 and Data 8.
:::

### Figure 5. Neurite analysis and assisted drug responses

![Public neurite shafts, matched autonomous laboratory-field analysis and measured drug responses after assisted repair.](figures/slas/submission_neurite_results.png){width=6in}

::: {custom-style="ImageCaption"}
**(I)** Same field and scale: raw, initial OpenHCS and published NeuronCyto II [@NeuronCytoII] (CC BY-NC 4.0), not manual ground truth or exact registration. Later repair overextended the target. (II) Matched autonomous P001 field. Frozen arrays/vector paths replace reduced screenshots; display changes leave geometry and measurements unchanged (Supplementary Data 8). (III) Assisted 20-well responses relative to each drug's DMSO mean; dots: two technical wells/dose; whiskers: sample SD. Additional endpoints: Supplementary Figure 5.
:::

### Imported CellProfiler workflows match the compared reference outputs

All 30 workflows passed selected reference-output comparisons in one unified current-source run, with zero reported differences. The selected reference profiles comprised 21 with CSV measurements, three with SQLite measurements and CellProfiler Analyst properties, and six containing only retained images or arrays. The five supplemented workflows contributed five object-label images and three numerical images. All five label images matched exactly after singleton-axis normalization, and all three numerical images passed with zero out-of-tolerance pixels. Supplementary Data 1 identifies every selected output and preserves the unified observations and source identity.

Image comparison executed for seven workflows: six image- or array-only profiles and the completed translocation example, whose overlay was compared alongside its SQLite measurements. Supplementary Data 4 shows how named images, objects and operations are retained in the imported Comet Assay.

The assays include DNA-damage measurement, human and Drosophila cell morphology, tumor morphology, Cell Painting morphology and quality control, protein translocation, wound healing, time-lapse tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening, and *C. elegans* phenotyping. Supplementary Data 1-2 identify the workflows and imported settings.

The advanced segmentation and 3D monolayer imports retain their named structures, measurements and processing sequences in editable Python (Supplementary Data 5).

### Execution speed

The matched single-sample evaluation used [pending]{.benchmark-claim key=case_count} workflows from record [pending]{.benchmark-claim key=record_name}, production revision [pending]{.benchmark-claim key=source_revision}. Its publication status is [pending]{.benchmark-claim key=status}. Declared-output comparisons passed in the warmup and three measured repetitions. Figure 6 shows the distribution of workflow speedups, with every workflow retained as a point. The minimum execution speedup over native CellProfiler was [pending]{.benchmark-claim key=execution_min}-fold and the median was [pending]{.benchmark-claim key=execution_median}-fold.

Compile-plus-run total speedup had a minimum of [pending]{.benchmark-claim key=total_min}-fold and a median of [pending]{.benchmark-claim key=total_median}-fold. This comparison includes OpenHCS compilation and client coordination, separately from execution. Exact per-workflow times and the clock definitions accompany the same record.

Measured multi-worker comparisons, total speedup versus assigned sample count, and individual workflow runtimes are shown in Supplementary Figure 6. Single-core amortization and exact efficiencies are retained in Supplementary Data 3.

### Figure 6. Matched single-sample speedup over native CellProfiler

![Execution and compile-plus-run total speedups, showing means, medians and every matched workflow.](figures/slas/benchmark-publication/measured_benchmark_publication_log.png){width=6in}

::: {custom-style="ImageCaption"}
Execution and compile-plus-run total speedups for [pending]{.benchmark-claim key=case_count} workflows, using one selected source sample, one worker and one numerical thread. Coloured bars show mean speedup, grey points show individual workflows, and black lines show medians on a logarithmic scale. Each workflow's speedup is the ratio of independent engine medians from three repetitions after warmup; the dashed line marks equal runtime. All workflows passed the declared-output comparisons; this is workflow parity, not biological segmentation accuracy. Minimum and median execution speedups are [pending]{.benchmark-claim key=execution_min}-fold and [pending]{.benchmark-claim key=execution_median}-fold; corresponding total speedups are [pending]{.benchmark-claim key=total_min}-fold and [pending]{.benchmark-claim key=total_median}-fold. Record [pending]{.benchmark-claim key=record_name} supplies every panel and manuscript claim. The linear view, individual runtimes and sample-count comparisons appear in Supplementary Figure 6.
:::

## Discussion

OpenHCS makes delegated image analysis inspectable in the terms of the biological experiment. An agent's processing choices remain connected to the source images, masks and measurements, and the scientist can revise the pipeline as the sample or question changes. The trials show agents performing analysis construction and self-directed repair from supplied briefs and acquisition context. They do not establish how easily an untrained user can formulate a brief or judge the result.

A laboratory can import a CellProfiler workflow, adjust source mappings and parameters, add its own Python functions and inspect the masks before processing further samples. Explicit choices permit revision as assays and imaging conditions change.

Imported workflows preserved their selected CellProfiler outputs, and agents recovered useful nuclei, neurite shafts and translocation responses. Image review supported self-directed repairs, but remaining errors included over-segmentation, uncertain boundaries and crossing assignments. Agreement across nuclear fields was uneven; retinal repair showed that improving one region could merge neighbours elsewhere. Task-specific endpoints and distributed inspection remain necessary.

The appropriate endpoint also depends on the experiment. Principal neurite shafts can be recovered without tracing every fine protrusion, whereas assigning length to individual neurons requires resolving crossings. For translocation, the completed 96-well analysis recovered control separation and dose-dependent response among cells with measurable nuclear and cytoplasmic compartments. Treatment-dependent compartment eligibility limits interpretation of the entire cell population. Retinal images lacked exhaustive manual annotations, and their heterogeneous background left some cell outlines uncertain. These distinctions prevent a useful result for one measurement from being treated as evidence for every aspect of segmentation.

Additional models, assays and expert-reviewed images are needed to estimate reliability on new experiments. These trials do not isolate the effect of packaged guidance. When pipelines transfer to new samples, channel choices, parameters and intermediate results remain available for review.

Scientists can therefore delegate pipeline construction and execution while retaining the images, measurements and editable settings needed to judge the result. The same division of work can support an AI-guided laboratory: the agent performs the image-analysis work, while the domain expert remains responsible for the scientific question and interpretation.

## Supplementary Data

The supplementary package indexes retained files and describes their fields and interpretation. Archive DOI: [pending Zenodo publication].

1. **CellProfiler workflow comparison:** unified 30-workflow current-source observations, reference inventory and exact run provenance; historical OpenHCS 0.8.5 release-CI evidence; the five-workflow export definitions and per-artifact audit; and separate historical timing records.
2. **CellProfiler coverage:** module-to-workflow associations, individual setting handling, and archived processing-registration coverage.
3. **Worker and memory measurements:** measured execution and memory by workflow, worker count and repeated-image assignment count, including completion status.
4. **Recorded agent workflow:** evaluated client, model and software versions; input checksums; exact prompt; tool trace and error counts; original outputs; and separately identified later corrections.
5. **Complex CellProfiler workflows:** source-derived step sequences, function-call counts and editable Python for advanced segmentation and 3D monolayer analysis.
6. **Workflow regression tests:** representative configuration, generated-Python and compiler-validation checks, with source and CI-job references.
7. **Prospective agent-authored assays:** frozen pipelines and held-out score receipts for BBBC039, BBBC007 and BBBC013, with quantitative results and operational findings.
8. **Task-only authoring and independent repair:** first/final reference agreement on the same inputs, full-corpus BBBC039 coverage, computational versus biological reference definitions, and retained post-freeze evaluation receipts.

## Code and Data Availability

OpenHCS source code: <https://github.com/OpenHCSDev/OpenHCS>.

OpenHCS documentation: <https://openhcs.readthedocs.io/>.

The supplementary archive contains the figure inputs and generation scripts, frozen analysis pipelines, scoring records and benchmark evidence. Archive DOI: [pending Zenodo publication]. Repository copies are available at <https://github.com/OpenHCSDev/openhcs/tree/main/paper/supplementary> and <https://github.com/OpenHCSDev/openhcs/tree/main/benchmark/results>.

The benchmark uses biological images and pipelines distributed by the CellProfiler project rather than OpenHCS-authored benchmark data. Original sources:

- official CellProfiler example pipelines and images: <https://github.com/CellProfiler/examples> [@CellProfilerExamples]
- official CellProfiler tutorial pipelines and images: <https://github.com/CellProfiler/tutorials> [@CellProfilerTutorials]
- CellProfiler 4 benchmark supplement: <https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics> [@Stirling2021]

The benchmark manifest pins the source collections. The selected matched record, [pending]{.benchmark-claim key=record_name}, retains the measured repetitions, original reports and figure inputs. Earlier unified comparisons and OpenHCS 0.8.5 release-CI evidence remain separately identified in the supplementary archive; they are not combined with the final matched timing record.

Supplementary Table 1 links the source repositories for the eight reusable libraries.

## Acknowledgements

We thank the CellProfiler project, its contributors, and the authors of the underlying biological datasets for making the example, tutorial, and benchmark materials available.

## Author Contributions

[To be confirmed by the authors: assign contributions to the final author list.]

## Funding

[To be confirmed by the authors: list applicable funding bodies, grants and fellowships, or confirm that no specific funding supported this work.]

## Declaration of Competing Interests

[To be confirmed by the authors: disclose relevant financial or personal relationships, or confirm that there are no competing interests to declare.]

## Declaration of generative AI and AI-assisted technologies in the manuscript preparation process

OpenAI Codex was used to assist with manuscript organization, prose revision and reproducible figure-assembly code under the corresponding author's direction. The autonomous analyses evaluated in this study are described separately in Materials and Methods. [Before submission, the authors must confirm their review of the text, citations and figures and their responsibility for the final manuscript.]
