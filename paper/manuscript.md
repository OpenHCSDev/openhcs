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

OpenHCS lets scientists and AI agents build, run and revise the same microscopy image analysis. Graphical controls, editable Python and the Model Context Protocol (MCP), through which AI agents operate software, all edit one workflow. Each function's declaration and documentation generate its controls and its description for agents. A compiled parallel runtime passes arrays between NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto steps. All 30 imported CellProfiler workflows, including 3D, tracking and Cell Painting analyses, reproduced native outputs on a current scientific Python stack: labels agreed exactly and numerical measurements agreed within 1e-6. Every workflow ran faster on one core. With CellProfiler's startup spread over eight samples, execution was at least [pending]{.benchmark-claim key=amortized_execution_min}-fold faster, with a median of [pending]{.benchmark-claim key=amortized_execution_median}-fold; including per-job compilation, it was at least [pending]{.benchmark-claim key=amortized_total_min}-fold faster. For single samples, the median execution speedup was [pending]{.benchmark-claim key=execution_median}-fold. Every workflow also ran faster with two, three and four parallel workers. AI agents built analyses from written task briefs and finalized each pipeline before scoring. Three independent agents segmented nuclei with object F1 of 0.906 to 0.910 on 175 BBBC039 fields that none of them had opened, agreeing within 0.004. A translocation analysis of 96 wells, four inspected during development, gave control Z′ of 0.849 and 0.726, in the excellent-assay range. In a laboratory neurite drug assay, three blind agents each recovered both drug-induced increases in outgrowth. Their well-level outgrowth correlated with MetaXpress (Pearson r 0.963 to 0.996), although their response sizes were smaller. Scientists can inspect the images, masks and measurements behind any result in napari or Fiji and revise the workflow that produced them, in direct use or in self-driving laboratories.

## Introduction

Many investigators know which cells, neurites or subcellular signals matter to an experiment but not how to turn their images into reliable measurements. Image analysis requires specialist choices about channels, preprocessing, segmentation and quality control. A pipeline can run without errors and still miss dim structures or split one cell in two. To delegate this work, a scientist needs an analysis that runs efficiently, can be edited, and keeps each measurement linked to the images behind it.

Fiji/ImageJ, CellProfiler, Icy and BioImageIT provide desktop processing workflows, and napari supports multidimensional inspection [@Schneider2012; @Schindelin2012; @Carpenter2006; @McQuin2018; @deChaumont2012; @Prigent2022; @Napari]. CellProfiler's documentation advises against running the full application as a Python package and points to CellProfiler Library for using its processing functions directly [@CellProfilerPythonPackage]. The CellProfiler 4.2.8.1 release pins SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies], so established workflows stay tied to an older scientific Python stack.

MCMICRO combines interchangeable modules for multiplexed tissue imaging using containerized tools and workflow engines [@Schapiro2022]. Its Nextflow implementation connects tools through command-line interfaces and intermediate image and table files. Its configuration states each tool's command, input options and channel numbering, and workflow code identifies the output files and where to save them [@MCMICROImplementation]. Combining tools therefore means coordinating these interfaces, file formats and execution state.

OpenHCS gives graphical users, Python programmers and AI agents one workflow to write, run and inspect (Figure 1). The workflow records the function calls, their settings and the images each step reads. A function's parameter declarations and documentation generate its graphical controls and its description for agents. Laboratory functions and imported CellProfiler workflows use the same interfaces, and imported workflows run as editable OpenHCS pipelines on current Python, NumPy and SciPy releases. The runtime compiles function calls, data flow, array conversions and output destinations into a parallel execution plan (Figure 2). ArrayBridge converts arrays and tensors when successive steps use different libraries. Saved and displayed images, labels and measurements stay linked to their source samples and to the step that made them. Scientists can therefore inspect and revise analyses they built themselves or delegated to an agent.

BioImage.IO Chatbot connects community resources to analysis extensions, and Omega generates and runs Python in napari [@Lei2024; @Royer2024]. Agentic-J combines curated bioimage knowledge, plugin-specific skills and specialized agents to generate, debug and audit Fiji scripts; scientists can inspect the scripts, interact with Fiji and connect external tools through MCP [@Johanns2026]. OpenHCS instead gives agents the workflow that scientists edit and a runtime that checks and executes it. BIABench scores agent analyses against references and expert rubrics; agents did better on routine 2D tasks, and repeated runs were unreliable on more complex data [@Pan2026BIABench].

We compared imported CellProfiler workflows with native outputs and run times, and tested whether blind AI agents could build and repair analyses from written task briefs without reference answers. Self-driving laboratories need unattended image analysis that turns microscopy into measurements for the next experiment. SiLA-based systems connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]; OpenHCS supplies the analysis step, while the scientist chooses the biological question.

## Materials and Methods

### Pipeline model

An OpenHCS pipeline is an ordered sequence of functions and settings. Steps use shared defaults unless they declare overrides. Compilation resolves inputs, function calls, array conversions and output destinations into a plan for workers (Supplementary Figure 1). Function signatures supply parameter names, types and defaults for graphical controls and editable Python; docstrings supply searchable descriptions. Backend declarations specify compatible CPU, GPU and deep-learning libraries and support for planes or volumes. ArrayBridge supplies array and tensor conversions across NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto (Supplementary Table 1). The compiler resolves conversion boundaries from functions' declared input and output backends, allowing custom functions from different libraries to participate in one pipeline without manually wiring conversions between steps.

Each step's input selection names the channels, planes or stacks it reads and divides images into processing groups. Later steps inherit or replace these choices. Sample, site, channel, plane and time coordinates link results to images through stacking and processing. Microscope handlers interpret acquisition layouts and metadata. Bio-Formats reads image planes from microscopy containers; OME-Zarr supplies arrays, axes, channels and pixel scales; experimental OMERO support supplies managed images. Users can assign channel and image roles explicitly when acquisition metadata are insufficient. Eight reusable libraries supply discovery, settings, generated interfaces, editable Python, array conversion, storage and process coordination (Supplementary Table 1). OpenHCS combines these mechanisms into a microscopy runtime; laboratory functions use the same declarations and execution paths as imported processing functions.

### Figure 1. Scientists can inspect and edit the agent's analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(I)** Native workspace with ExampleHuman and ExampleFly folders and the nine-step ExampleHuman recipe. Blue boxes mark the plate manager, pipeline editor and execution-server list.
:::

### Execution and viewers

Steps produce images, labels, measurements, object relationships and files. Function contracts specify inputs and outputs, and compilation connects later steps to their sources. Each result carries its source coordinates, its processing group and the step that produced it. Saving and viewer delivery can be configured independently.

The execution server coordinates requests and workers. Each worker reuses loaded libraries and initialized array backends while processing its assigned samples, then releases its resources when the run finishes. Worker count controls concurrency; workers use processes by default, with threads available as a configuration option. Storage routes include local files, in-memory data, Zarr and OMERO.

napari and Fiji receive selected outputs with their source coordinates and the step that produced them. The streaming service checks viewer readiness and waits for display updates. Sessions remain open for inspection after execution, and agents can query napari layers and regions of interest.

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

Continuous integration tests Linux, Windows and macOS. Python 3.11 and 3.13 each run the generated CellProfiler workflow corpus through multiprocessing and the ZeroMQ server on all three operating systems. Python 3.12 tests every combination of disk or Zarr storage and ImageXpress or OperaPhenix inputs on those systems. A separate Python 3.14 Linux job checks the installed core runtime without the optional Centrosome comparison dependency. The full 30-workflow numerical comparison runs through ZeroMQ against committed native CellProfiler references on Linux with Python 3.12 and on Linux, Windows and macOS with Python 3.14. A required CI check enforces the complete parity matrix for relevant pull requests. Additional jobs exercise package installation, the GUI and installed desktop candidates through MCP, including Intel and Apple Silicon macOS, and native Windows and macOS installers. The versioned CI workflow defines these test scopes (Supplementary Data 1).

### Figure 2. One editable workflow connects editing, execution and inspection

![Shared editing, execution, workers, viewers and image storage.](figures/slas/shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
Forms, Python and MCP edit one workflow, including imported CellProfiler pipelines. The ZeroMQ execution server compiles the pipeline and coordinates workers. Workers read images, save outputs and stream results to napari or Fiji; progress returns to the editor. Supplementary Figure 1 shows runtime preparation.
:::

### Autonomous trial design

Each trial used a fresh agent, which received a biological task brief, acquisition information and MCP access; later trials also supplied the packaged OpenHCS skill, a written guide to using OpenHCS. Briefs could include channel hints, requested outputs and review instructions; the retinal task, for example, requested RBPMS-positive soma labels, measurements and a count. Supplementary Data 8 summarizes the original briefs. No skill version was recorded for the earlier gpt-5.6-sol trials. For later trials, Supplementary Data 8 records the hash of each delivered skill file: the three BBBC039 agents each received a different skill revision, and the three treatment-assay agents shared one.

The skill instructs agents to inspect channels and representative regions, measure feature sizes, look up function contracts, build and run a pipeline, and compare matched views of the raw image alone, the result alone and both combined. Repairs begin at the earliest failing stage and are checked against positive and regression controls. Figure 3A shows this procedure; recorded attempts show its use in individual trials. Earlier trials used OpenHCS 0.8.5; later trials used 0.8.7.

Agents finalized their pipelines before any comparison with reference data, and no pipeline changed after scoring began. They received no reference labels, accepted settings or score feedback while building their analyses. First-versus-final comparisons use the first completed prediction and the final settings on the same inputs. Self-directed repairs are autonomous; revisions prompted by a scientist are assisted. The earlier gpt-5.6-sol trials withheld evaluation images and treatment metadata until after finalization and changed only input and output folders for evaluation. The later gpt-6.1-sol trials gave agents development images and compared results with task-specific references after the agents finished.

For the laboratory treatment assay, three new gpt-6.1-sol agents independently analysed the same 20 coded wells, each containing nine fields. All received the same biological brief, acquisition information, MCP access and fixed version of the packaged skill under one qualified OpenHCS 0.8.7 installation. They chose six, four and eight development fields and, after fixing their methods, reviewed 20, eight and twelve further fields. Each analysed all 180 fields, and its final outputs were fixed before the evaluator opened treatment identities, MetaXpress measurements or assisted results. Supplementary Figure 5 reports all three agents, not a selected best run.

For the later BBBC039 agents, the original image-delivery records showed that at least one agent opened 25 of the 200 fields. The remaining 175 fields, which none of the three agents opened, form the uninspected subset used for retrospective evaluation. This subset and the earlier held-out partitions are reported separately. Supplementary Data 7–8 provide final pipelines, data partitions, scores, model and software versions, task times and computational usage.

### Endpoints and references

**BBBC039.** The earlier trial used four development and 50 held-out fields. Each predicted nucleus was matched to at most one reference nucleus, and a match required intersection over union (IoU) ≥ 0.5. Scores included object precision, recall and F1, foreground Dice, signed count error, and split/merge diagnostics. Later comparisons used all 200 annotated fields and the 175-field uninspected subset.

**BBBC007.** The earlier trial used four development and 12 held-out DNA/actin fields. The directed boundary fraction measures how closely predicted borders between touching cells follow manual outlines: it is the proportion of predicted boundary pixels between adjacent cells that lie within two pixels of any manual outline. Later agents were compared on the complete 16-field collection.

**BBBC013.** The earlier trial used four development and 92 held-out wells. Its endpoint was the per-well mean of cell-level mean nuclear GFP divided by mean cytoplasmic GFP, using matched nuclear and cytoplasmic object labels. The later agent used each well's median eligible-cell log2 nuclear-to-cytoplasmic GFP ratio. Z′ used sample standard deviations across four positive and four negative control wells for each drug, with wells as replicates.

**H001.** First and final bright-object predictions were matched one-to-one to predeclared computational labels from a notebook-derived image.

**H002.** Predicted 3D centres were matched one-to-one to manual centre annotations within a predeclared 30-voxel radius.

**Retina.** RBPMS-positive soma detection was reviewed in matched raw, label and combined views across several regions. [TODO: annotated soma-centre reference, from four to six hand-marked crops.]

**Neurites.** Principal shafts in the public field and soma/path recovery in nine laboratory fields were inspected with matched raw and result views. The public comparison used the published NeuronCyto II image and algorithm output [@NeuronCytoII]. Three later independent laboratory analyses were compared with MetaXpress well exports and the retained scientist-assisted analysis. Each endpoint was the unweighted mean of nine field-level values; each drug curve used its own two zero-dose DMSO wells. Overlapping fields were not deduplicated. The comparison tests recovery of treatment effects, not manual tracing accuracy or identical branch definitions. [TODO: spatial reference, from crossing ownership labels in two to three fields.] The earlier method-directed demonstration and assisted transfer remain in the supplement.

### Performance measurement

The matched single-sample comparison used one physical CPU core, one worker and one numerical thread. OpenHCS ran with Python 3.12 and native CellProfiler 4.2.8.1 with Python 3.9. Each workflow used one selected source well or sample, with unchanged processing settings and the declared comparison outputs. OpenHCS used a warmup followed by three measured repetitions. The native baseline was one complete first-use-inclusive serial CellProfiler batch; its natural internal initialization remained included. Source revisions, workloads, hardware and environments accompany the matched benchmark in Supplementary Data 1 and 3.

CellProfiler execution time covered the pipeline call, including run/group preparation, processing and post-run work. OpenHCS execution time covered the complete server job, including output publication and plate exports. External process and server startup, OpenHCS library readiness and warmup, and scientific comparison were excluded. Native initialization inside the pipeline call remained included. Batches repeated the same selected sample (repeated samples, labelled assignments in Figure 6). Larger batches spread CellProfiler’s internal initialization and OpenHCS compilation over more samples. The amortized one-process comparison divided one measured serial eight-sample CellProfiler first batch by eight, and the median of three measured one-worker twelve-sample OpenHCS runs by twelve. This spreads CellProfiler initialization over eight samples and OpenHCS preparation over twelve. The eight-sample CellProfiler batch used one process and one numerical thread with four permitted CPUs; the single-sample batch used one CPU. Worker scaling was therefore calculated by comparing OpenHCS worker counts on the same twelve-sample workload. Total time compared the prepared native invocation with the sum of OpenHCS client compilation and execution submission/wait. Nested server and worker durations were counted once. Each workflow's speedup was its complete native first-batch duration divided by the median of three OpenHCS durations; the cohort median was the median of those ratios. Native CellProfiler times for twelve and sixteen samples were projected from the measured eight-sample first batch and warm observations, not measured; OpenHCS scaling on the fixed twelve-sample workload was measured directly. Supplementary Data 3 gives the projection law and its limited three-workflow calibration. Process-tree memory was unavailable.

## Results

### Scientists and agents revise the same analysis

Graphical authoring, editable Python and agent operations preserve one editable workflow (Figure 1). A custom function's declaration and docstring supply its graphical controls and MCP parameter descriptions (Figure 1II). Imported CellProfiler steps use these same interfaces, so established analyses and laboratory-specific functions can be edited and executed together. Scientists can construct an analysis directly, open an agent-authored pipeline, inspect linked images and measurements in napari or Fiji, and revise the settings before rerunning it.

In a code-to-control check, an MCP request changed the normalization step's high percentile from 99.8 to 99.6 and the form showed 99.6. A field-edit request restored 99.8, and generated Python contained the restored value (Supplementary material, Figure assembly and interface records). Figure 2 shows how the editor, execution server and viewers share the workflow and its outputs.

### Autonomous analysis

Table 1 summarizes the three assays with the strongest evidence.

Table 1. Main results from the later gpt-6.1-sol trials. Agent counts refer to independent agents within each assay. Agents could inspect development images while building their pipelines; the nuclear fields that none of them opened were identified afterwards. Supplementary Data 7–8 give the individual trial results, the other assays, earlier held-out trials and additional repeats.

| Assay | Agents | Evaluation inputs | Endpoint | Result |
|---|---|---|---|---|
| BBBC039 nuclei | 3 | 175 fields that none of the agents opened | Pooled object F1 | 0.906 to 0.910 |
| BBBC013 translocation | 1 | 96 wells including four development wells | Control Z′, LY294002; Wortmannin | 0.849; 0.726 |
| Laboratory neurite drug assay | 3 | 180 fields in 20 wells per agent | Control-normalized outgrowth responses | Both positive responses recovered by all three; magnitudes varied |

#### Three agents segment nuclei with the same accuracy

Three independent agents segmented nuclei in BBBC039 with pooled object F1 of 0.906 to 0.910 on the 175 fields that none of them opened (Figure 4B). Object F1 combines the fraction of reference nuclei found with the fraction of detections that are correct. Across all 200 fields, including those the agents inspected, F1 was 0.898 to 0.906. The agents chose different settings, yet their pooled scores on the uninspected fields differed by at most 0.004.

On the dataset's official 50-image test partition (5,720 nuclei), the agents' per-image mean F1 at IoU 0.5 was 0.898 to 0.903. On the same images, Caicedo et al. reported average F1 of 0.898 for a trained U-Net and 0.790 and 0.811 for basic and advanced CellProfiler pipelines tuned by experts [@Caicedo2019]. Their scores average over IoU thresholds from 0.5 upward, but changed little up to IoU 0.8. The agents received no reference labels while building their pipelines.

Most errors were missed nuclei: for each agent, misses outnumbered false detections in 171 to 173 of the 175 uninspected fields, and 117 to 121 fields reached F1 of at least 0.90. The same six fields scored below 0.80 for all three agents; they were mostly less crowded than average (median 59 nuclei, against 126 across all 175 fields), and the lowest scored 0.23 to 0.27 because 57 to 59 of its 69 nuclei were missed.

Between two agents' final pipelines on all 200 fields, per-field F1 mostly differed by less than 0.03 (Supplementary Figure 3). A repair on three inspected fields raised F1 from 0.908 to 0.934 but added split nuclei (Supplementary Data 8). The earlier gpt-5.6-sol trial reached F1 0.746 and foreground Dice 0.935 on 50 held-out fields (Supplementary Data 7).

#### A translocation analysis reaches excellent-assay quality

The BBBC013 agent analysed all 96 wells and obtained control Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 4E). Z′ measures how well positive and negative controls separate; both values exceed 0.5, the conventional threshold for an excellent screening assay [@Zhang1999]. The agent chose its own readout: each well's median log2 ratio of nuclear to cytoplasmic GFP across eligible cells. A cytoplasmic compartment was eligible for measurement around 14,631 of 17,320 nuclei (84.5%). Four wells contributed to each treatment group. The earlier held-out trial obtained Z′ of 0.751 for Wortmannin and 0.554 for LY294002 across 92 wells (Supplementary Data 7).

#### Three blind agents recover drug responses in a laboratory neurite assay

Three agents independently analysed the same coded 20-well neurite outgrowth experiment, blind to treatment. All three found increased mean outgrowth per cell and total outgrowth at every tested dose of FC-A and Y27632 (Figure 5III). Across the 20 wells, each agent's mean outgrowth per cell correlated closely with MetaXpress (Pearson r 0.963 to 0.996). Effect sizes varied and were smaller than MetaXpress's: at 40 µM, fold changes in mean outgrowth per cell were 1.32 to 1.65 for FC-A and 1.49 to 1.69 for Y27632, against 1.98 and 2.05 for MetaXpress. Two agents were close to the retained scientist-assisted analysis, which gave 1.77 and 1.76; the third gave weaker responses. Cell-count fold changes were 0.94 to 0.99 for FC-A and 0.92 to 0.94 for Y27632, against 0.95 and 0.91 for MetaXpress.

Branches per cell also increased at every tested dose, and well-level values correlated with MetaXpress (r 0.875 to 0.990). Fold changes at 40 µM were smaller: 1.24 to 1.63 for FC-A and 1.50 to 1.73 for Y27632, against 3.00 and 3.26 for MetaXpress. The agents' control wells started higher, at 2.1 to 5.3 branches per cell, against 1.3 to 1.5 for MetaXpress. The absolute increases from zero dose to 40 µM were similar (3.1 and 2.9 branches per cell for MetaXpress; 2.5 and 2.7 for the most correlated agent), so the higher baseline compressed the fold changes. The OpenHCS neurite function applies no minimum branch length, which may admit short side processes in control wells. Smaller branching responses also appeared in the assisted analysis and persisted in total branches and branches per primary process (Supplementary Figure 5), so cell-count denominators do not explain the difference. These algorithm-defined measurements capture the biological response but do not establish equivalent anatomical branching.

#### Other assays

Smaller tasks, scored against partial references or by matched image review, are detailed in Supplementary Data 8. On 16 BBBC007 DNA/actin fields, two agents placed 0.743 and 0.740 of their predicted borders between touching cells within two pixels of a manual outline (directed boundary fraction; Figure 4C,F). On single development images, the H001 agent raised F1 against a computational reference from 0.929 to 0.944 through its own repair (Figures 3B and 4A), and the H002 agent recovered all 15 annotated 3D nuclear centres within 30 voxels (Figure 4D,H,I); eleven predictions had no matching annotation. [TODO: precision, from classification of the eleven unmatched predictions.] Agents also detected retinal cell bodies (Figure 4G; Supplementary Figure 4). [TODO: manual-reference result, from annotated soma centres.] Others traced neurite shafts in a public NeuronCyto II field and in nine laboratory fields (Figure 5I–II). [TODO: spatial ownership comparison, from crossing annotations.] Each of these tasks involved one or two agents, and most lack exhaustive references.

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

All 30 imported workflows passed the declared output comparisons: labels matched exactly and numerical measurements agreed at 1e-6 tolerance. Exact label agreement means every segmented object kept the same pixels and identifier as in native CellProfiler, a stricter criterion than overlap scores. OpenHCS produced these outputs with Python 3.12 and NumPy 2, whereas native CellProfiler ran with Python 3.9 and its pinned SciPy and scikit-image releases. Continuous integration repeats the full numerical comparison on Linux, Windows and macOS and blocks relevant changes that break it. The comparison included 21 CSV profiles, three SQLite profiles and six image/array profiles. Five workflows received added exports comprising five label images and three numerical images (Supplementary Data 1).

The workflows covered DNA damage, human and Drosophila morphology, tumor morphology, Cell Painting, protein translocation, wound healing, tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening and *C. elegans* phenotyping. Seven workflows had image comparisons, including the translocation overlay alongside SQLite measurements. Advanced segmentation and 3D monolayer imports could be reloaded as editable Python with their named structures, measurements and processing sequences (Supplementary Data 5). The output agreement spans preprocessing, segmentation, measurements and terminal exports in complete workflows, including multi-stage 3D analysis.

### Execution speed

Every one of the 30 workflows was faster than native CellProfiler on one core, for execution and for compile-plus-run total time. When CellProfiler's internal initialization was spread over a measured eight-sample serial batch, OpenHCS execution per sample was a median [pending]{.benchmark-claim key=amortized_execution_median}-fold faster, with minimum [pending]{.benchmark-claim key=amortized_execution_min}-fold; compile-plus-run total speedup was a median [pending]{.benchmark-claim key=amortized_total_median}-fold, with minimum [pending]{.benchmark-claim key=amortized_total_min}-fold. The largest gain, [pending]{.benchmark-claim key=amortized_execution_max}-fold, came from an illumination-correction workflow whose large median filter took CellProfiler about 950 s per sample at both first and repeated use, so it reflects computation rather than startup. For single samples, execution was a median [pending]{.benchmark-claim key=execution_median}-fold faster than native CellProfiler, with minimum [pending]{.benchmark-claim key=execution_min}-fold (Figure 6). Compile-plus-run total speedup was a median [pending]{.benchmark-claim key=total_median}-fold, with minimum [pending]{.benchmark-claim key=total_min}-fold. Each point compares one complete native first-use-inclusive batch with the median of three OpenHCS repetitions after warmup. Output comparisons passed during warmup and every measured repetition.

The execution measurements include worker coordination, output publication and plate exports. The speedups therefore apply to the complete server job, including those runtime responsibilities. Compile-plus-run measurements also include per-job compilation.

The measured eight-sample comparison also favoured OpenHCS for every workflow, for both execution and compile-plus-run total time, using two workers against one serial native CellProfiler process. Every workflow remained faster in the twelve- and sixteen-sample comparisons, whose CellProfiler times are projected. Figure 6 shows execution speedups across worker configurations and graded module-test coverage; Supplementary Data 3 gives total times and projection calibration.

On the fixed twelve-sample workload, every workflow benefited from two, three and four workers relative to one worker, for both execution and compile-plus-run time (Supplementary Figure 6). These scaling ratios use measured OpenHCS times and do not depend on CellProfiler projections. The one-worker comparisons at one and twelve samples report time per sample and preparation amortization for both systems. Repeated samples are copies of the same selected source sample, so the batch results measure computational throughput.

### Figure 6. Execution speed and module-test coverage

![Execution speedups across worker configurations for thirty workflows.](figures/slas/submission_benchmark_schedule.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Execution speedups with 1, 2, 3 and 4 workers processing 1, 8, 12 and 16 repeated samples (assignments). Each configuration contains all thirty workflows; bars show means and black lines medians. Each ratio uses a complete CellProfiler first-use-inclusive batch divided by the median of three OpenHCS runs after warmup. CellProfiler 1- and 8-sample batches were measured; 12 and 16 were projected from the measured 8-sample batch and the warm per-sample rate. The dashed line marks equal runtime. Repeated samples are computational replicates of each selected sample.
:::

### Figure 6, continued

![Graded test evidence for current executable processing modules.](figures/slas/submission_benchmark_coverage.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(B)** Evidence tiers for the current executable processing-module catalog: exercised in the thirty-workflow corpus, module-specific behavior tests, shared-path behavior tests, declaration/import checks only, or no evidence. A module receives its strongest supported tier. Shared-path evidence covers the named common behavior, not every module-specific setting or algorithm. Setup modules and non-executable declarations are excluded. Supplementary Data 3 provides the per-module evidence and timing tables.
:::

## Discussion

OpenHCS turns function declarations into an analysis that scientists and agents can edit, run and inspect. A function's declared input and output libraries tell the compiler where arrays must be converted, so NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto functions can share one pipeline. Custom laboratory functions and imported CellProfiler steps use the same workflow and runtime. Scientists can add a function without building its graphical controls, its MCP description or conversion code between libraries. Measurements, saved files and displayed results stay linked to their source samples and processing steps.

The output comparison shows that established analyses can move to a current scientific Python stack without changing their results. The benchmarked CellProfiler 4.2.8.1 release pins SciPy to 1.9.0 and scikit-image to 0.18.3 [@CellProfiler4281Dependencies]. OpenHCS reproduced the compared outputs with Python 3.12, NumPy 2 and newer SciPy (Supplementary Data 1), and continuous integration extends this check to Python 3.14 on Linux, Windows and macOS. Laboratories with existing `.cppipe` workflows can therefore run them as editable Python pipelines alongside current deep-learning and GPU libraries. The reusable comparison suite checks measurement values, images and exports, not only that a workflow finishes. Its evidence covers the tested workflows and outputs; upgrading dependencies inside CellProfiler would need its own validation.

OpenHCS reproduced the compared native outputs of all 30 workflows while running faster on one core, for both execution and compile-plus-run time. With CellProfiler initialization spread over eight samples, the smallest compile-plus-run speedup was [pending]{.benchmark-claim key=amortized_total_min}-fold, so per-job compilation did not erase the execution advantage in any tested workflow. The measured job includes loading, worker coordination, saving and plate exports, so the gains apply to complete analyses.

The mechanisms behind this workflow are packaged as eight reusable libraries for discovery, settings, generated interfaces, editable Python, array conversion, storage and process coordination (Supplementary Table 1); other Python tools can adopt them without OpenHCS. A shared workflow reduces the separate rules needed to connect tools. MCMICRO's Nextflow extension template asks developers to declare matching filename patterns for process outputs and saved files and to connect each new stage to the main workflow [@MCMICROImplementation]. OpenHCS instead derives parameter interfaces from function declarations, and its compiler and runtime handle data flow and saving. Imported CellProfiler workflows and custom functions use the same mechanisms.

Agentic-J grounds analysis in curated domain knowledge and coordinates generated scripts through a supervisor that tracks state and through specialized agents [@Johanns2026]. In OpenHCS, agents and scientists edit the pipeline that the compiler and runtime execute. The settings that determine the processing remain visible when scientists inspect the results, so scientists can revise an agent's analysis through the usual controls or Python.

BIABench compares final outputs with ground truth and uses a vision-language model to score analysis practice against expert rubrics; it found repeated agent runs unreliable on more complex data [@Pan2026BIABench]. Here, agents finalized their pipelines before any scoring, yet three independent agents reached the same nuclear accuracy within 0.004 F1, and three others recovered the same positive neurite drug responses. On the official BBBC039 test images, their scores were similar to a published trained U-Net and higher than expert-tuned CellProfiler pipelines, although the published scores average over several overlap thresholds. A workflow with declared function contracts and a runtime that checks them may contribute to this consistency, although these trials do not isolate its effect. The scientist can inspect and revise the pipeline behind any result.

The trials have several limits. Models and skill revisions changed together across trials, and the number of agents varied by assay, so their separate contributions to reliability cannot be isolated. The three laboratory treatment-assay agents used the same model, qualified software and fixed skill. Agents inspected some development images while building their pipelines, and the 175-field nuclear subset was selected retrospectively. Nuclear accuracy varied across fields, and the inspected repair traded missed nuclei for additional splits. Retinal counts and neurite recovery lack exhaustive spatial references; unresolved crossings limit per-neuron length and branch assignment. The public neurite final repair went beyond its principal-shaft target, which was clarified after the run. H002 annotations cover only some centres, so precision awaits classification of unmatched predictions. DNA/actin outlines support only the directed boundary measure. Eligible-cell translocation responses may differ from the full cell population, because compartment eligibility varies with treatment. Overlapping laboratory neurite fields were analysed independently. Independent analysis agents do not add biological replication. Ease of use by scientists without image-analysis training remains untested. [TODO: independent frozen-skill evaluation on an unused nuclear dataset, from the new trial.]

An imaging-based self-driving laboratory needs analysis that runs efficiently, that agents can build and repair, and that scientists can still inspect and revise. OpenHCS supplies this infrastructure. Independent agents reached the same nuclear accuracy on fields none of them had opened; one agent's translocation analysis gave an excellent plate-level assay; and three blind agents recovered both positive drug responses in a laboratory neurite assay. Scientists can use the platform directly or delegate a task to an agent, and each measurement keeps the source images and settings needed for review before it informs the next experiment.

## Supplementary Data

The supplement describes the comparisons, reference definitions and trial evidence. Archive DOI: [TODO: Zenodo archive DOI, publication].

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

The supplementary archive contains figure inputs and generation scripts, final pipelines, scores and benchmark measurements. Repository copies are available at <https://github.com/OpenHCSDev/openhcs/tree/main/paper/supplementary> and <https://github.com/OpenHCSDev/openhcs/tree/main/benchmark/results>.

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

OpenAI Codex was used to assist with manuscript organization, prose revision and reproducible figure-assembly code under the corresponding author's direction. The autonomous analyses evaluated in this study are described separately in Materials and Methods. [Before submission, the authors must confirm their review of the text, citations and figures and their responsibility for the final manuscript.]
