---
bibliography: openhcs_references.json
csl: styles/elsevier-vancouver.csl
reference-section-title: References
link-citations: true
link-bibliography: true
---

# OpenHCS: high-performance autonomous image analysis for the Python ecosystem

**Authors:** Tristan Simas, Jathav Puvirajan, and Alyson Fournier

**Affiliation:** McGill University, Montreal, Quebec, Canada

**Correspondence:** Tristan Simas, <tristan.simas@mail.mcgill.ca>

**Short title:** OpenHCS: autonomous microscopy analysis

**Keywords:** microscopy; image analysis; self-driving laboratory; autonomous analysis; agentic AI; high-content screening

## Abstract

Image analysis blocks biological investigation when extracting measurements requires expertise in both analysis methods and software integration. OpenHCS lets scientists delegate analysis development to AI agents while retaining a method they can inspect, revise and extend. Its unified Python runtime combines processing functions, parallel execution, graphical and Python editing, and result inspection in napari or Fiji. Scientists describe what needs measuring; agents select and configure methods in that shared workflow. Agents built analyses from written task briefs and finalized their pipelines before scoring. Three independent agents reached pooled nuclear detection F1 of 0.906 to 0.910 on 175 BBBC039 fields that none had opened. Three blind agents each recovered both drug-induced outgrowth responses in a laboratory neurite assay. Their well-level measurements correlated with MetaXpress (Pearson r 0.963 to 0.996), with smaller response magnitudes. All 30 imported CellProfiler 4.2.8.1 workflows reproduced exported labels exactly and numerical measurements within absolute and relative tolerances of 1e-6 on Python 3.12 and NumPy 2, including 3D imaging, object tracking and cell profiling. With CellProfiler's setup time spread over eight samples, median one-worker execution per sample was [pending]{.benchmark-claim key=amortized_execution_median}-fold faster. OpenHCS makes delegated analysis development compatible with scientific control of the method, while preserving established workflow outputs and accelerating execution.

## Introduction

Image analysis becomes a bottleneck when answering a biological question first requires assembling and debugging software. A biologist who wants to count cells or measure neurite growth must choose processing methods, install their dependencies, connect their inputs and outputs, and check whether the measurements reflect the images. Finding an appropriate algorithm does not complete that work. In a 2023 analysis of approximately 500 recent image.sc threads, installation appeared in 9.9% of opening posts and somewhere in approximately 19% of threads [@Ouyang2023]. This documents a substantial support burden before biological interpretation even begins.

Combining tools adds a second burden: a segmentation produced in one application must retain its labels, dimensions and sample identity when measured or inspected in another. Published Fiji–CellProfiler workflows use scripts and exchanged images and tables to connect tracking, morphology measurements and visual review [@Dobson2021]. CellProfiler's plugin developers describe dependency conflicts and manual environment setup as obstacles for non-developers, and provide containerized execution as one solution [@Weisbart2024]. These are practical barriers for biologists, not merely software-maintenance concerns.

Fiji/ImageJ, CellProfiler, Icy and BioImageIT provide desktop processing workflows, and napari lets users inspect multidimensional images [@Schneider2012; @Schindelin2012; @Carpenter2006; @McQuin2018; @deChaumont2012; @Prigent2022; @Napari]. Combining processing methods also requires software integration: outputs must reach the next method in a format it accepts. For example, CellProfiler's documentation advises against running the full application as a Python package and points to CellProfiler Library for using its processing functions directly [@CellProfilerPythonPackage].

MCMICRO combines tools for multiplexed tissue imaging by packaging their software environments in containers. Nextflow coordinates the processing stages, passing images and tables between command-line programs as files [@Schapiro2022; @MCMICROImplementation]. This integrates applications at their execution and file boundaries. OpenHCS instead integrates processing functions within a shared Python runtime, with one model for parameters, workflow state, array conversion and results; Docker containers are not its integration mechanism.

AI assistants can also help develop the analysis itself. BioImage.IO Chatbot connects community resources to analysis extensions, and Omega generates and runs Python in napari [@Lei2024; @Royer2024]. Agentic-J combines bioimage knowledge, instructions for using individual plugins and specialized agents to generate, debug and audit Fiji scripts. Scientists can inspect those scripts and connect external tools through the Model Context Protocol (MCP), an interface through which agents call software tools [@Johanns2026]. BIABench compares agent analyses with reference answers and expert assessments; agents did better on routine 2D tasks, and repeated runs were unreliable on more complex data [@Pan2026BIABench].

OpenHCS addresses both method development and software integration (Figure 1). A scientist describes what needs measuring; an agent selects and configures processing methods, runs them and inspects the outputs. The scientist examines the images and measurements, changes settings through graphical controls or Python, and extends or reruns the same analysis. This makes the analysis itself the editable result of delegation, rather than leaving the scientist with disconnected commands and files.

OpenHCS connects these activities through a purpose-built runtime, graphical interface and shared workflow state (Figure 2). Each processing function declares its parameters and documents what it does; those declarations generate graphical controls and agent tool descriptions. Graphical and Python editing operate on the same workflow. Before execution, the compiler prepares the processing sequence and array conversions; workers execute the plan in parallel. ZeroMQ connects execution and viewer services, delivering images and results to napari or Fiji for inspection. Laboratory functions and imported CellProfiler workflows therefore participate in one analysis without user-written conversions between their data formats. Saved images, labels and measurements retain their source samples and processing steps.

We tested whether blind AI agents could build and repair analyses from written task briefs without reference answers, and compared imported CellProfiler workflows with outputs and run times from CellProfiler itself. These experiments test whether agents can develop useful analyses and whether established methods retain their results when run in OpenHCS. The same capabilities can supply image analysis for self-driving laboratories, where measurements inform the next experiment. Systems using SiLA, a standard for laboratory automation, connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]; OpenHCS supplies the image-analysis component.

## Materials and Methods

### Pipeline model

An OpenHCS pipeline is an ordered sequence of functions and settings. Steps use shared defaults unless they declare overrides. Compilation resolves inputs, function calls, array conversions and output destinations into a plan for workers (Supplementary Figure 1). Function signatures supply parameter names, types and defaults for graphical controls and editable Python; docstrings supply searchable descriptions. Backend declarations specify compatible CPU, GPU and deep-learning libraries and support for planes or volumes. ArrayBridge supplies array and tensor conversions across NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto (Supplementary Table 1). The compiler resolves conversion boundaries from functions' declared input and output backends, allowing custom functions from different libraries to participate in one pipeline without manually wiring conversions between steps.

ObjectState manages editable state and its history; graphical forms display that state rather than define a separate analysis. Pycodify renders and reloads the pipeline as Python, so code editing changes the same declared functions and settings. These components make graphical, code and agent access different interfaces to one analysis, not independent implementations of it.

Scientists and agents extend an analysis by registering Python functions with these same declarations, including preprocessing and deep-learning methods. Illumination correction calls BaSiCPy through the OpenHCS-maintained fork, and N2V2 denoising runs in PyTorch with CUDA. These methods join the same editable pipeline without separate graphical forms, agent tools or hand-written array conversions.

Each step's input selection names the channels, planes or stacks it reads and divides images into processing groups. Later steps inherit or replace these choices. Sample, site, channel, plane and time coordinates link results to images through stacking and processing. Microscope handlers interpret acquisition layouts and metadata. Bio-Formats reads image planes from microscopy containers; OME-Zarr supplies arrays, axes, channels and pixel scales; experimental OMERO support supplies managed images. Users can assign channel and image roles explicitly when acquisition metadata are insufficient. Supplementary Table 1 lists the eight reusable libraries behind the runtime.

### Figure 1. Scientists can inspect and edit the agent's analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(I)** Native workspace with ExampleHuman and ExampleFly folders and the nine-step ExampleHuman recipe. Blue boxes mark the plate manager, pipeline editor and execution-server list.
:::

### Execution and viewers

Steps produce images, labels, measurements, object relationships and files. Function contracts specify inputs and outputs, and compilation connects later steps to their sources. Results retain their source coordinates, processing group and producing step when saved or delivered to napari or Fiji. Saving and viewer delivery can be configured independently.

The execution server coordinates requests and workers. Each worker reuses loaded libraries and initialized array backends while processing its assigned samples, then releases its resources when the run finishes. Workers use processes by default, with threads available as a configuration option. Storage routes include local files, in-memory data, Zarr and OMERO.

The streaming service checks viewer readiness and waits for display updates. Viewer sessions remain open for inspection after execution, and agents can query napari layers and regions of interest.

### Agent access through MCP

MCP operations cover function discovery, pipeline editing and validation, execution, progress and result inspection [@MCP]. Each operation declares request and result types, implementation, permitted changes, data access and security requirements. These declarations generate the interface and govern execution.

Registered function descriptions let agents select functions and edit the shared workflow. Registering a custom function adds its signature and docstring to the existing controls and MCP catalogue (Figure 1II). Desktop operations edit the live workflow; headless operations use an isolated execution context. Local clients use standard input/output. Desktop connections are authenticated, workflow revisions are checked, and file access follows permitted roots. Hosted HTTP offers selected read-only operations.

### Figure 1, continued. The laboratory's own Python joins the shared analysis

![Real Python declaration and docstring, generated controls, live editable Python and agent-facing parameter descriptions.](figures/slas/submission_custom_function.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(II)** The Python declaration and docstring generate the function's graphical controls and MCP descriptions. Form and code views show gain 1.2 and offset 0.0.
:::

### CellProfiler import and output comparison

CellProfiler `.cppipe` files supply modules and settings. Setup modules define image sources; processing and export modules become editable OpenHCS steps. Each module declaration specifies images, objects, measurements and relationships and whether it operates per image group or across the plate. The same function is available through GUI, Python and MCP. Named images and objects connect measurements to their inputs. Generated Python was reloaded for the advanced segmentation and 3D monolayer tutorials to check functions and parameters [@CellProfilerTutorials] (Supplementary Data 5).

Numerical measurements and image pixels were compared with absolute and relative tolerances of `1e-6`. Identifiers and categorical values were compared exactly after documented CellProfiler-compatible normalization. Object-label images were compared exactly after singleton-axis normalization. Five workflows lacking exports received terminal image or label exports with their processing settings unchanged. Supplementary Data 1 lists output inventories and comparison definitions; Supplementary Data 2 lists the imported modules and settings. The matched run checked every declared exported file in each workflow, a file-level fraction of 1.00; Supplementary Data 1 gives per-workflow counts.

Continuous integration compares all 30 workflows with committed native CellProfiler references through ZeroMQ on Linux with Python 3.12 and 3.14, and on Windows and macOS with Python 3.14. Supplementary Data 1 describes the additional execution, storage, microscope, installation and desktop tests.

### Figure 2. One editable workflow connects editing, execution and inspection

![Shared editing, execution, workers, viewers and image storage.](figures/slas/shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
Forms, Python and MCP edit one workflow, including imported CellProfiler pipelines. The ZeroMQ execution server compiles the pipeline and coordinates workers. Workers read images, save outputs and stream results to napari or Fiji; progress returns to the editor. Supplementary Figure 1 shows runtime preparation.
:::

### Autonomous trial design

Each trial used a fresh agent, which received a biological task brief, acquisition information and MCP access; later trials also supplied the packaged OpenHCS skill, a written guide to using OpenHCS. Briefs could include channel hints, requested outputs and review instructions; the retinal task, for example, requested RBPMS-positive soma labels, measurements and a count. Supplementary Data 8 summarizes the original briefs. No skill version was recorded for the earlier gpt-5.6-sol trials. For later trials, Supplementary Data 8 records the hash of each delivered skill file: the three BBBC039 agents each received a different skill revision, and the three treatment-assay agents shared one.

The skill instructs agents to inspect channels and representative regions, measure feature sizes, look up function contracts, build and run a pipeline, and compare matched views of the raw image alone, the result alone and both combined. Repairs begin at the earliest failing stage and are checked against positive and regression controls. Figure 3A shows this procedure; recorded attempts show its use in individual trials. Earlier trials used OpenHCS 0.8.5; later trials used 0.8.7.

Agents finalized their pipelines before any comparison with reference data, and no pipeline changed after scoring began. They received no reference labels, accepted settings or score feedback while building their analyses. First-versus-final comparisons use the first completed prediction and the final settings on the same inputs. Self-directed repairs are autonomous; revisions prompted by a scientist are assisted. The earlier gpt-5.6-sol trials withheld evaluation images and treatment metadata until after finalization and changed only input and output folders for evaluation. The later gpt-6.1-sol trials gave agents development images and compared results with task-specific references after the agents finished.

For the laboratory treatment assay, three new gpt-6.1-sol agents independently analysed the same 20 coded wells, each containing nine fields. All received the same biological brief, acquisition information, MCP access and fixed version of the packaged skill using the same OpenHCS 0.8.7 installation. They chose six, four and eight development fields and, after fixing their methods, reviewed 20, eight and twelve further fields. Each analysed all 180 fields, and its final outputs were fixed before the evaluator opened treatment identities, MetaXpress measurements or assisted results. Supplementary Figure 5 reports the individual agents.

For the later BBBC039 agents, image-delivery records identified 25 of the 200 fields as opened by at least one agent. The remaining 175 fields, which none of the three agents opened, form the uninspected subset used for retrospective evaluation. This subset and the earlier held-out partitions are reported separately. Supplementary Data 7–8 provide final pipelines, data partitions, scores, model and software versions, task times and computational usage.

### Endpoints and references

**BBBC039.** The earlier trial used four development and 50 held-out fields. Each predicted nucleus was matched to at most one reference nucleus, and a match required intersection over union (IoU) ≥ 0.5. Scores included object precision, recall and F1, foreground Dice, signed count error, and split/merge diagnostics. Later comparisons used all 200 annotated fields and the 175-field uninspected subset.

**BBBC007.** The earlier trial used four development and 12 held-out DNA/actin fields. The directed boundary fraction measures how closely predicted borders between touching cells follow manual outlines: it is the proportion of predicted boundary pixels between adjacent cells that lie within two pixels of any manual outline. Later agents were compared on the complete 16-field collection.

**BBBC013.** The earlier trial used four development and 92 held-out wells. Its endpoint was the per-well mean of cell-level mean nuclear GFP divided by mean cytoplasmic GFP, using matched nuclear and cytoplasmic object labels. The later agent used each well's median eligible-cell log2 nuclear-to-cytoplasmic GFP ratio. Z′ used sample standard deviations across four positive and four negative control wells for each drug, with wells as replicates.

**H001.** First and final bright-object predictions were matched one-to-one to predeclared computational labels from a notebook-derived image.

**H002.** Predicted 3D centres were matched one-to-one to manual centre annotations within a predeclared 30-voxel radius.

**Retina.** RBPMS-positive soma detection was reviewed in matched raw, label and combined views across several regions.

**Neurites.** Principal shafts in the public field and soma/path recovery in nine laboratory fields were inspected with matched raw and result views. The public comparison used the published NeuronCyto II image and algorithm output [@NeuronCytoII]. Three later independent laboratory analyses were compared with MetaXpress well exports and the retained scientist-assisted analysis. Each endpoint was the unweighted mean of nine field-level values; each drug curve used its own two zero-dose DMSO wells. Overlapping fields were not deduplicated. The comparison tests recovery of treatment effects, not manual tracing accuracy or identical branch definitions. The earlier method-directed demonstration and assisted transfer remain in the supplement.

### Performance measurement

The matched single-sample comparison used one physical CPU core, one worker and one numerical thread. OpenHCS ran with Python 3.12 and native CellProfiler 4.2.8.1 with Python 3.9. That CellProfiler release requires SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]; the comparison tests whether its workflows retain their outputs on OpenHCS's newer scientific Python environment. Each workflow used one selected source well or sample, with unchanged processing settings and the declared comparison outputs. OpenHCS used a warmup followed by three measured repetitions. The native baseline was one complete first-use-inclusive serial CellProfiler batch; its natural internal initialization remained included. Source revisions, workloads, hardware and environments accompany the matched benchmark in Supplementary Data 1 and 3.

**Timing boundaries.** CellProfiler execution time covered its pipeline call, including internal initialization, run/group preparation, processing and post-run work. OpenHCS execution time covered the server job, including output publication and plate exports. External process and server startup, OpenHCS library readiness and warmup, and scientific comparison were excluded. Compile-plus-run time compared the prepared native invocation with OpenHCS client compilation plus execution submission/wait. Each workflow's speedup divided the native first-batch duration by the median of three OpenHCS durations; cohort medians summarize these workflow ratios.

**Batch comparisons.** Batches repeated the same selected source sample. The amortized comparison divided one measured serial eight-sample CellProfiler first batch by eight and the median of three one-worker twelve-sample OpenHCS runs by twelve. The CellProfiler batch used one numerical thread with four permitted CPUs; its single-sample comparison used one CPU. Twelve- and sixteen-sample CellProfiler times were projected from the measured eight-sample batch and warm observations. Supplementary Data 3 gives the full clock definitions, projection law and three-workflow calibration. Process-tree memory was unavailable.

**Worker scaling.** OpenHCS worker counts were compared on the same twelve-sample workload using measured execution and compile-plus-run times throughout.

## Results

### Scientists and agents revise the same analysis

Delegation is useful only if the scientist can take over the resulting method. OpenHCS keeps agent, graphical and Python edits in the same workflow: an MCP request changed a normalization step's high percentile from 99.8 to 99.6, and the graphical form showed 99.6. A field-edit request restored 99.8, and generated Python contained the restored value (Supplementary material, Figure assembly and interface records). Figure 1II shows how a custom function's declaration supplies its generated controls and editable Python, extending that shared workflow without a separate interface implementation.

### Autonomous analysis

Table 1. Main results from the later gpt-6.1-sol trials. Agent counts refer to independent agents within each assay. Agents could inspect development images while building their pipelines; the nuclear fields that none of them opened were identified afterwards. Supplementary Data 7–8 give the individual trial results, the other assays, earlier held-out trials and additional repeats.

| Assay | Agents | Evaluation inputs | Endpoint | Result |
|---|---|---|---|---|
| BBBC039 nuclei | 3 | 175 fields that none of the agents opened | Pooled object F1 | 0.906 to 0.910 |
| BBBC013 translocation | 1 | 96 wells including four development wells | Control Z′, LY294002; Wortmannin | 0.849; 0.726 |
| Laboratory neurite drug assay | 3 | 180 fields in 20 wells per agent | Control-normalized outgrowth responses | Both positive responses recovered by all three; magnitudes varied |

#### Three agents reach similar pooled nuclear accuracy

Independent agents may choose different pipelines for the same task; the practical question is whether they reach comparable accuracy. Three agents segmented nuclei in BBBC039 with pooled object F1 of 0.906 to 0.910 on the 175 fields that none of them opened (Figure 4B). Object F1 combines the fraction of reference nuclei found with the fraction of detections that are correct. Across all 200 fields, including those the agents inspected, F1 was 0.898 to 0.906. Despite choosing different settings, the agents' pooled scores on the uninspected fields differed by at most 0.004.

On the dataset's official 50-image test partition (5,720 nuclei), the agents' per-image mean F1 at IoU 0.5 was 0.898 to 0.903. Caicedo et al. used this dataset to evaluate learned and CellProfiler segmentation methods [@Caicedo2019]. Our agents received no reference labels while building their pipelines.

Most errors were missed nuclei: for each agent, misses outnumbered false detections in 171 to 173 of the 175 uninspected fields, and 117 to 121 fields reached F1 of at least 0.90. The same six fields scored below 0.80 for all three agents; they were mostly less crowded than average (median 59 nuclei, against 126 across all 175 fields), and the lowest scored 0.23 to 0.27 because 57 to 59 of its 69 nuclei were missed.

Between two agents' final pipelines on all 200 fields, per-field F1 mostly differed by less than 0.03 (Supplementary Figure 3). A repair on three inspected fields raised F1 from 0.908 to 0.934 but added split nuclei (Supplementary Data 8). The earlier gpt-5.6-sol trial reached F1 0.746 and foreground Dice 0.935 on 50 held-out fields (Supplementary Data 7).

#### A translocation analysis reaches excellent-assay quality

For a screening assay, an analysis must separate biological controls, not merely produce plausible segmentations. The BBBC013 agent analysed all 96 wells and obtained control Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 4E). Z′ measures how well positive and negative controls separate; both values exceed 0.5, the conventional threshold for an excellent screening assay [@Zhang1999]. The agent chose its own readout: each well's median log2 ratio of nuclear to cytoplasmic GFP across eligible cells. A cytoplasmic compartment was eligible for measurement around 14,631 of 17,320 nuclei (84.5%); eligibility varied with treatment (Supplementary Figure 2). Four wells contributed to each treatment group. The earlier held-out trial obtained Z′ of 0.751 for Wortmannin and 0.554 for LY294002 across 92 wells (Supplementary Data 7).

#### Three blind agents recover drug responses in a laboratory neurite assay

We next tested whether independently authored analyses recovered drug responses in laboratory data without access to treatment identities or commercial measurements. Three agents independently analysed the same coded 20-well neurite outgrowth experiment. All three found increased mean outgrowth per cell and total outgrowth at every tested dose of FC-A and Y27632 (Figure 5III). Across the 20 wells, each agent's mean outgrowth per cell correlated closely with MetaXpress (Pearson r 0.963 to 0.996). The biological responses were recovered, but their measured magnitudes differed: at 40 µM, fold changes in mean outgrowth per cell were 1.32 to 1.65 for FC-A and 1.49 to 1.69 for Y27632, against 1.98 and 2.05 for MetaXpress. Two agents were close to the retained scientist-assisted analysis, which gave 1.77 and 1.76; the third gave weaker responses. Cell-count fold changes were 0.94 to 0.99 for FC-A and 0.92 to 0.94 for Y27632, against 0.95 and 0.91 for MetaXpress.

Branches per cell also increased at every tested dose, and well-level values correlated with MetaXpress (r 0.875 to 0.990). Fold changes at 40 µM were smaller: 1.24 to 1.63 for FC-A and 1.50 to 1.73 for Y27632, against 3.00 and 3.26 for MetaXpress. The agents' control wells started higher, at 2.1 to 5.3 branches per cell, against 1.3 to 1.5 for MetaXpress. For Blind 3, the absolute increases from zero dose to 40 µM were 2.44 and 2.65 branches per cell for FC-A and Y27632, compared with MetaXpress's 2.94 and 2.90. Its higher baselines compressed the fold changes; the cause of the baseline differences was not established. Smaller branching responses also appeared in the assisted analysis and persisted in total branches and branches per primary process (Supplementary Figure 5), so cell-count denominators do not explain the difference. These algorithm-defined measurements capture the biological response but do not establish equivalent anatomical branching.

#### Other assays

Smaller tasks, scored against partial references or by matched image review, are detailed in Supplementary Data 8. On 16 BBBC007 DNA/actin fields, two agents placed 0.743 and 0.740 of their predicted borders between touching cells within two pixels of a manual outline (directed boundary fraction; Figure 4C,F). On single development images, the H001 agent raised F1 against a computational reference from 0.929 to 0.944 through its own repair (Figures 3B and 4A), and the H002 agent recovered all 15 annotated 3D nuclear centres within 30 voxels (Figure 4D,H,I). Eleven predictions had no matching annotation; the partial reference does not establish precision. Agents also detected retinal cell bodies (Figure 4G; Supplementary Figure 4) and traced neurite shafts in a public NeuronCyto II field and in nine laboratory fields (Figure 5I–II). Retinal detection and neurite recovery were assessed by matched image review without exhaustive spatial annotations; unresolved crossings limit per-neuron path assignment. Figure 5I shows the public neurite initial prediction; the final repair extended beyond principal shafts, and the shaft-only target was clarified after the run. Each task involved one or two agents.

### Figure 3. Delegated specialist work leaves an analysis the scientist can inspect

![Skill-directed workflow with Fiji and napari inspection, followed by the recorded H001 decisions and matched raw/repair images.](figures/slas/submission_autonomous_loop.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** The packaged skill's workflow: biological brief, input inspection, pipeline execution, matched-view audit, targeted repair and delivery. **(B)** H001 decisions across four executions and matched raw, first (a01) and final (a04) views. The elongated object's split is corrected. Colours distinguish labels within each view. Times include inspection, repair, reporting and cleanup.
:::

### Figure 4. Quantitative results and matched image-repair evidence

![Task-specific nuclear, boundary, volume and translocation endpoints alongside an independent DNA/actin merge repair.](figures/slas/submission_analysis_summary.png){width=6in}

::: {custom-style="ImageCaption"}
**(A)** H001 computational-reference object F1, first and final, one image.
**(B)** BBBC039 object F1 for three agents on all 200 fields and on the 175 fields that none of them opened.
**(C)** BBBC007 directed boundary agreement with manual outlines; dots are fields and lines are pooled-pixel fractions.
**(D)** H002 voxel errors for the 15 matched manual centres.
**(E)** BBBC013 dose means and sample SD, four wells per dose; control Z′ uses four positive and four negative wells.
**(F)** BBBC007 raw and label views of the same C4 region, before (candidate01_retry01) and after (candidate06) merge repair. Colours distinguish labels within each view.
:::

### Figure 4, continued. Repairs and volumetric localisation

![Matched retinal and volumetric body repairs, with separate finalized three-dimensional localisation evidence.](figures/slas/submission_quantitative_results.png){width=6in}

::: {custom-style="ImageCaption"}
**(G)** Retinal raw, first and final views of fragmented soma footprints and a neighbouring pair.
**(H)** Body-partition repair at Z=36 in a 3D volume.
**(I)** H002 XY labels, XZ/YZ outlines (yellow) and in-plane centres (magenta), with 15 matched manual centres and 11 unmatched predictions. Distances are voxels. Colours distinguish labels within each view.
:::

### Figure 5. Neurite analysis and independently authored drug responses

![Public neurite shafts, matched autonomous laboratory-field analysis and drug responses from three independent blind agents.](figures/slas/submission_neurite_results.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(I)** Raw image, initial OpenHCS analysis and published NeuronCyto II algorithm output [@NeuronCytoII] (CC BY-NC 4.0), displayed at the same field scale; the published output is an algorithm comparison, not manual ground truth. **(II)** Matched raw, soma/path and combined views from the earlier nine-field autonomous P001 analysis, separate from the three treatment-assay authors. **(III)** All three blind authors' 20-well responses and MetaXpress, relative to each drug curve's own DMSO mean. Dots are two technical wells per dose for each author or method; whiskers are sample SD, not uncertainty across authors. Supplementary Figure 5 shows additional endpoints and preserves the assisted comparison.
:::

### Imported CellProfiler workflows reproduce native outputs

Reusing an established analysis on a newer software stack requires preserving its measurements, not merely importing its settings. All 30 imported workflows reproduced native CellProfiler 4.2.8.1 outputs: exported label images matched native pixels and identifiers exactly, and numerical measurements met absolute and relative tolerances of 1e-6. OpenHCS produced these results with Python 3.12 and NumPy 2; native CellProfiler 4.2.8.1 ran with Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0. Its release pins SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]. The tested workflows therefore retained their outputs without retaining CellProfiler's older runtime and dependency versions. The comparison included 21 CSV profiles, three SQLite profiles and six image/array profiles. Five workflows received added exports comprising five label images and three numerical images (Supplementary Data 1).

The workflows covered DNA damage, human and Drosophila morphology, tumor morphology, Cell Painting, protein translocation, wound healing, tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening and *C. elegans* phenotyping. Seven workflows had image comparisons, including the translocation overlay alongside SQLite measurements. Advanced segmentation and 3D monolayer imports were reloaded as editable Python with their named structures, measurements and processing sequences (Supplementary Data 5). Output equivalence thus extended across complete preprocessing, segmentation, measurement and export workflows, including multi-stage 3D analysis.

### Execution speed

Revising an analysis requires rerunning it, and larger experiments repeat that work across many fields. We therefore measured execution with output export included, checking that faster processing preserved the results.

The retained test evidence covers 54 executable processing modules within the thirty-workflow corpus, 29 through module-specific behavior tests and two through shared-path tests (Figure 6A). Shared-path evidence does not establish every module-specific algorithm or setting.

Every one of the 30 workflows was faster than native CellProfiler on one core, for server-job execution and compile-plus-run time (Figure 6B). When CellProfiler's internal initialization was spread over a measured eight-sample serial batch, OpenHCS execution per sample was a median [pending]{.benchmark-claim key=amortized_execution_median}-fold faster, with minimum [pending]{.benchmark-claim key=amortized_execution_min}-fold. This per-sample comparison uses twelve measured OpenHCS samples with one worker, not a matched eight-sample OpenHCS run. Compile-plus-run speedup was a median [pending]{.benchmark-claim key=amortized_total_median}-fold, with minimum [pending]{.benchmark-claim key=amortized_total_min}-fold. The largest execution gain, [pending]{.benchmark-claim key=amortized_execution_max}-fold, came from an illumination-correction workflow whose large median filter took CellProfiler about 950 s per sample at both first and repeated use. Output comparisons passed during warmup and every measured repetition. Supplementary Data 3 gives the single-sample summaries and individual workflow timings.

The measured eight-sample comparison also favoured OpenHCS for every workflow, for both execution and compile-plus-run total time, using two workers against one serial native CellProfiler process. Every workflow remained faster in the twelve- and sixteen-sample comparisons, whose CellProfiler times are projected. These mixed-workload comparisons are shown separately in Supplementary Figure 6; Supplementary Data 3 gives total times and projection calibration.

Figure 6C instead matches the core count and samples per core between engines, comparing measured OpenHCS times with projected CellProfiler times. The projection applies the retained initialization-plus-per-sample model to balanced independent CellProfiler processes; it assumes no contention or coordination overhead. Serial model validation does not establish multicore accuracy, and direct matched multicore CellProfiler measurements remain outstanding (Supplementary Data 3).

On the fixed twelve-sample workload, every workflow benefited from two, three and four workers relative to one worker, for both execution and compile-plus-run time (Supplementary Figure 6; Supplementary Data 3). These ratios use measured OpenHCS times throughout. Repeated samples are copies of the same selected source sample, so the batch results measure computational throughput.

### Figure 6. Module coverage, measured speed and matched-core projections

![Graded module coverage, measured one-worker comparisons and matched-core CellProfiler projections, with all thirty workflows shown as points.](figures/slas/submission_benchmark_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Strongest retained test-evidence tier for each of 85 executable modules; zero-count tiers have no slice. **(B)** Measured one-worker comparisons: one sample each, and per-sample time for eight serial CellProfiler samples versus twelve OpenHCS samples. **(C)** Equal core counts and samples per core, with CellProfiler projected as independent one-thread processes, each retaining its initialization cost. Balanced work, no contention and no coordination overhead are assumed; smaller per-process batches extrapolate outside the serial validation range. **(B, C)** Each colored distribution contains all thirty workflows; black lines mark medians and dashed lines equal runtime. Ratios use OpenHCS medians of three repetitions after warmup. Total time includes OpenHCS compilation; CellProfiler internal initialization is included, external startup and OpenHCS readiness/warmup excluded. Samples are computational replicates. Supplementary Data 3 gives the model, validation limits and individual values.
:::

## Discussion

Agents built executable analyses from written task briefs, recovered both drug-induced outgrowth responses in three independent runs, and reached pooled nuclear F1 above 0.90 on fields none had inspected. They selected and configured processing methods rather than requiring the scientist to specify each step. The contribution is not just automated execution of an existing recipe: it is delegation of method development while keeping the resulting analysis available for scientific inspection, revision and extension.

The nuclear agents shared difficult fields with many missed nuclei, and the neurite analyses differed in response magnitude. These findings make image inspection part of the scientific workflow: a useful autonomous result need not reproduce another algorithm's every decision, but its detections and measurements must remain open to examination. Recovery of the drug responses establishes biological utility; the differing effect sizes remain important when comparing measurements across methods.

The shared workflow makes delegation reversible: scientists inspect the images and measurements, revise settings through graphical controls or Python, and extend the method with their own functions. They do not need to translate an agent's output into a separate application to take control of it. The parameter-edit check demonstrates that agent, form and code operations retain the same settings.

OpenHCS reproduced the tested CellProfiler 4.2.8.1 workflows on Python 3.12 and NumPy 2, preserving exact exported labels and numerical measurements within the stated tolerances. Laboratories can therefore reuse these established methods in the same workflow as custom CPU, GPU and deep-learning functions, rather than keeping the entire analysis tied to CellProfiler's older environment. Supplementary Data 1–2 specify the verified modules, settings and outputs.

OpenHCS was faster in every tested workflow while preserving the compared outputs. Even after CellProfiler initialization was spread across eight samples, median one-worker execution per sample was [pending]{.benchmark-claim key=amortized_execution_median}-fold faster. The advantage persisted when OpenHCS compilation was included, and additional workers increased throughput on a fixed workload. The single-core results establish an execution advantage independent of multicore parallelism; the newer environment is not merely a compatibility benefit.

The architecture removes repeated integration work at the point where it otherwise reaches the user. A processing function's declarations supply its graphical controls and agent description, while declared array backends determine conversions. The biologist encounters one set of controls and inspection tools; the developer does not maintain separate GUI and agent wrappers or conversions at every pipeline boundary. This is a unified analysis system, not a launcher for independently configured applications.

Containerized workflows such as MCMICRO isolate software environments and connect their outputs [@Schapiro2022]; CellProfiler plugins also use containers to accommodate external dependencies [@Weisbart2024]. OpenHCS integrates at a different level: functions share workflow state, compilation, execution and result handling. Its GUI-to-Python editing and ZeroMQ viewer connections preserve that analysis across authoring and inspection. For a biologist, the distinction is the ability to change a method and inspect its consequences in the same system, rather than maintain scripts that transfer results between applications.

The decomposition also extends the software's relevance beyond microscopy. The eight reusable libraries in Supplementary Table 1 separate interface generation, state, code conversion, storage and process communication from biological methods. The axis-based pipeline model describes arrays and processing groups independently of microscope-specific names; non-microscopy remote-sensing and telemetry declarations exercise that separation in the source tests. Extraction of this compiler and runtime into ArrayPipe is underway [@ArrayPipe]. The resulting general-purpose layer is intended for data-science and machine-learning pipelines that need the same combination of heterogeneous array libraries, parallel execution and inspectable intermediate results.

These trials do not isolate the effects of the model, skill or runtime on analysis reliability: model and skill versions changed across the broader trial series, and agent counts varied by assay. The treatment-assay cohort held model, software and skill fixed, whereas the three nuclear agents received different skill revisions. The nuclear uninspected subset was identified retrospectively. The independent agents repeat analysis of the same experimental material; they do not add biological replication.

OpenHCS brings autonomous analysis development, established processing methods and image inspection into one editable workflow. Scientists delegate method development without giving up the ability to inspect, revise and extend the result. For self-driving laboratories, this design offers an image-analysis component whose measurements remain linked to an inspectable method rather than an opaque service.

## Supplementary Data

The supplement contains the comparison methods, reference definitions, trial records and linked source files.

1. **CellProfiler workflow comparison:** unified 30-workflow results, output inventories and five-workflow export definitions.
2. **CellProfiler coverage:** module-to-workflow associations, individual setting handling, and archived processing-registration coverage.
3. **Worker measurements:** execution timings by workflow, worker count and number of repeated samples.
4. **Recorded agent workflow:** earlier method-directed NeuronCyto demonstration, model and software versions, outputs and comparison references.
5. **Complex CellProfiler workflows:** source-derived step sequences, function-call counts and editable Python for advanced segmentation and 3D monolayer analysis.
6. **Workflow regression tests:** representative configuration, generated-Python and compiler-validation checks, with source and CI-job references.
7. **Prospective agent-authored assays:** final pipelines and held-out BBBC039, BBBC007 and BBBC013 scores.
8. **Agent-authored analyses and independent repair:** first/final comparisons, full-corpus nuclear evaluation, original brief summaries and trial measurements.

## Code and Data Availability

OpenHCS source code: <https://github.com/OpenHCSDev/OpenHCS>.

OpenHCS documentation: <https://openhcs.readthedocs.io/>.

Supplementary files contain figure inputs and generation scripts, final pipelines, scores and benchmark measurements. Repository copies are available at <https://github.com/OpenHCSDev/openhcs/tree/main/paper/supplementary> and <https://github.com/OpenHCSDev/openhcs/tree/main/benchmark/results>.

The benchmark uses biological images and pipelines distributed by the CellProfiler project. Original sources:

- official CellProfiler example pipelines and images: <https://github.com/CellProfiler/examples> [@CellProfilerExamples]
- official CellProfiler tutorial pipelines and images: <https://github.com/CellProfiler/tutorials> [@CellProfilerTutorials]
- CellProfiler 4 benchmark supplement: <https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics> [@Stirling2021]

The benchmark manifest specifies the source collections. Benchmark [pending]{.benchmark-claim key=record_name} contains source revision [pending]{.benchmark-claim key=source_revision}, original reports and figure inputs. Original timing reports and historical comparisons are available in the archive.

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

OpenAI Codex was used to assist with manuscript organization, prose revision and reproducible figure-assembly code under the corresponding author's direction. The autonomous analyses evaluated in this study are described separately in Materials and Methods.
