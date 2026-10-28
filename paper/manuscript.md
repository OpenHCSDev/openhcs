---
bibliography: openhcs_references.json
csl: styles/elsevier-vancouver.csl
reference-section-title: References
link-citations: true
link-bibliography: true
---

# OpenHCS: an extensible platform for agent-driven bioimage analysis

**Authors:** Tristan Simas, Jathav Puvirajan, and Alyson Fournier

**Affiliation:** McGill University, Montreal, Quebec, Canada

**Correspondence:** Tristan Simas, <tristan.simas@mail.mcgill.ca>

**Short title:** OpenHCS: agent-driven bioimage analysis

**Keywords:** microscopy; image analysis; self-driving laboratory; autonomous analysis; agentic AI; high-content screening

## Abstract

Bioimage analysis is essential for biological research, but setting up specialized tools and getting them to work together can impede discovery for researchers without the required technical expertise. OpenHCS connects the bioimaging ecosystem's existing software tools and platforms through a native Python layer, with multiprocessing and GPU support for standard machine-learning libraries. Scientists can round-trip analysis edits between graphical controls and Python, and inspect results in Fiji or napari. Laboratories can load compatible Python functions within the running application without a separate plugin package and reuse existing CellProfiler pipelines. Measurements remain linked to their source images and samples. From a single written biological task prompt, independent AI agents used the same tools to build, run, inspect and correct analyses autonomously, recovering drug responses, detecting nuclei and distinguishing positive and negative assay controls. All 30 tested CellProfiler pipelines retained their outputs and ran faster with both applications using one processor core; parallel OpenHCS execution further reduced times on the same twelve-sample workload. OpenHCS extends laboratory automation to building and running analyses that scientists inspect, change and reuse.

## Introduction

Drug screening and studies of cell and molecular biology need open-source tools that automate measurements from microscopy images. First described 20 years ago, CellProfiler was developed with academic and industry support to organize image processing and measurement into reusable pipelines [@Carpenter2006; @McQuin2018]. Its pipeline-based approach became widely used; assembling an analysis still means choosing and tuning steps for a particular assay. Different disease models and biological questions require measurements ranging from cell number and morphology to subcellular protein location and signal dynamics. Each assay therefore needs its own processing sequence and often substantial troubleshooting.

To inspect, process and organize their images, researchers use ImageJ/Fiji and napari [@Schneider2012; @Schindelin2012; @NapariPlugins], OMERO for managing images and their information [@Allan2012], and Icy for viewing, plugins and graphical workflows [@deChaumont2012].

Specialized algorithms for image correction and detecting biological structures are available as standalone software or libraries and through plugins for these platforms. Flat-field correction compensates for uneven illumination, and denoising helps distinguish structures from noise. [BaSiCPy](https://github.com/peng-lab/BaSiCPy) corrects background and illumination, N2V2 denoises and Cellpose finds cells [@Stringer2021Cellpose; @Hock2022N2V2]. Unsuitable functions or settings can turn imaging artifacts into apparent biological differences. Cellpose plugins for Fiji and napari and N2V2 for napari illustrate these host-specific routes [@FijiCellpose; @CellposeNapari; @NapariN2V]. Keeping these integrations usable can require updates when the underlying algorithms or host interfaces change.

Installing compatible software versions is only the first step; the selected tools must also be connected into a repeatable end-to-end analysis. Steps must exchange images and results while preserving channels, dimensions, pixel sizes and sample identities. Connecting scripts need maintenance when tools, parameters, formats or versions change. This work creates a barrier for researchers without programming training. In the image.sc support forum [@Rueden2019Forum], installation appeared in approximately 19% of roughly 500 recent threads [@Ouyang2023].

Existing Python bridges for some of these tools reduce integration work. PyImageJ connects ImageJ to Python, napari-imagej makes ImageJ tools available in napari, and magicgui generates controls from Python functions [@Rueden2022PyImageJ; @NapariImageJ; @NapariMagicgui; @NapariWidgetWorkshop]. Combining these tools into a complete analysis can still require code to connect images, detections, measurements and settings while preserving sample identities. Python access does not resolve incompatible dependencies. The [software-resource inventory](supplementary/software_resources.md) compares extension routes and learning resources.

Specialized tools can require incompatible library versions. For example, the [napari-n2v installation guide](https://github.com/juglab/napari-n2v/blob/0e9fee355d5f51c8ec0f0a6a3b9e4c71fe35237e/docs/installation.md#L15) states that “`n2v` is not compatible with TensorFlow 2.16 and upwards”; its [maintenance notice](https://github.com/juglab/napari-n2v/blob/0e9fee355d5f51c8ec0f0a6a3b9e4c71fe35237e/README.md#L11) says the plugin is “no longer maintained”. The documented [RunCellpose recipe for Cellpose-SAM on Apple Silicon](https://plugins.cellprofiler.org/runcellpose.html#cellpose-sam-cellpose-4) uses `python=3.9` with `cellpose==4.0.6`; Python 3.9 [reached end of life on 31 October 2025](https://peps.python.org/pep-0596/#lifespan). These examples illustrate version-specific environments that can remain necessary or documented while other analysis libraries advance. Docker packages tools and their libraries in isolated containers so conflicting versions can coexist. Integration approaches include Fiji–CellProfiler image and table exchange [@Dobson2021], BioImageIT's packaged processing and data management [@Prigent2022], CellProfiler's Python and Docker plugins [@Weisbart2024], and MCMICRO's coordination of tissue-imaging tools through containers and files [@Schapiro2022; @MCMICROImplementation]. Different dependency versions can increase container-image storage; file-based workflows add reads and writes between steps. Containers manage dependency conflicts, but packaging alone does not coordinate settings, execution and inspection. Scientists must still choose settings and check measurements.

Research effort has gone into platforms where AI assistants aim to reduce this technical burden by helping researchers develop and run analyses from written requests. [Supp. Table 3](supplementary/README.md#supplementary-table-3.-ai-assistance-and-evaluation-resources) summarizes community-linked assistance, generated Python and specialist tool use, including the Model Context Protocol (MCP), which lets agents invoke software operations. BIABench separately evaluates agent-produced analyses against reference answers and expert assessments: performance was stronger on routine 2D tasks, while repeated runs were unreliable on more complex data [@Pan2026BIABench].

OpenHCS provides a native Python integration layer for connecting existing bioimage-analysis tools and platforms within one editable analysis. Graphical settings can be opened as editable Python, and applying code changes updates that same analysis and its controls; pipelines can be shared as reusable presets (Figure 1A). From within the running application, laboratories can add compatible Python functions without writing a host-specific plugin package; these functions receive the same controls and agent access (Figure 1B). Multiprocessing runs samples in parallel, while native GPU support lets functions use libraries such as PyTorch and TensorFlow. Results remain linked to source images and samples (Figure 2); OpenHCS uses PyImageJ for Fiji viewing and also supports napari. From a biological task brief, agents use MCP to build, run, inspect and repair these same pipelines autonomously.

We evaluated how scientists build, inspect, change, share and extend analyses through graphical and Python interfaces and work with AI agents. Independent agents developed analyses of neurite growth, nuclei and protein redistribution; we compared final measurements with references after development. We also compared images, measurements and completion times for 30 imported CellProfiler workflows, using matched single-core resources and testing additional OpenHCS workers.

## Materials and Methods

Microscopy analysis must coordinate wells, sites, channels, Z planes and timepoints while accommodating different microscope formats, processing functions, storage systems, viewers and parallel processes. Rather than implement each combination separately, we built eight domain-agnostic libraries for editing, settings, data handling and communication, and composed them into OpenHCS (Figures 1–2; Supp. Table 1).

### Building and editing pipelines

A pipeline is an ordered sequence of configurable processing steps. Each step contains one or more compatible Python functions, their settings and input selections from source images or earlier results. Scientists can add functions from existing libraries or their own Python code from within OpenHCS. At each step, scientists choose which images to collect into a stack using acquisition coordinates such as site, Z plane, channel or timepoint. For example, overlapping sites from the same well, channel, Z plane and timepoint can be collected for stitching using their tile positions, while collecting Z planes produces a volume. Separate processing groups can apply different functions, for example to different channels. Sample and image coordinates are retained during grouping or stacking; later steps inherit or replace these choices (Supp. Figure 1).

Different microscope layouts can make selecting the correct experimental images and acquisition information a manual task. Preconfigured microscope handlers provide a common interface for recognized acquisition layouts, using file-discovery rules and metadata to identify each well, site, channel, Z plane and timepoint. Outside those layouts, OpenHCS can read supported microscopy containers through Bio-Formats. For ordinary image folders still requiring manual configuration, source bindings let users select readable files, extract image coordinates and name pipeline inputs. These selection, metadata and input-naming tasks are familiar from [CellProfiler's Images, Metadata and NamesAndTypes modules](https://cellprofiler-manual.s3.amazonaws.com/CellProfiler-4.2.8/help/projects_configure_images.html). OME-Zarr stores microscopy data in blocks, allowing selected image regions to be retrieved without downloading the entire dataset [@Moore2021]; OpenHCS reads its images, dimensions, channels and pixel sizes. Experimental OMERO support provides access to images in a shared image-management server. Users can assign channel and image roles explicitly when acquisition metadata are insufficient.

To avoid writing and maintaining a separate plugin package when adding laboratory-specific functions, we accept compatible Python function code from within the running application. A function's parameter names, types, defaults and documentation generate graphical controls and agent-facing descriptions (Figure 1B). Each function defines its inputs and outputs; registering these definitions integrates the function with pipeline execution, graphical editing and agent access. Graphical settings can be rendered as editable Python, and applying Python edits updates the same analysis and its controls. Shared defaults, step-specific settings and edit history remain with the analysis, which can be saved as a reusable preset (Figure 1A–B). Compatible processing and storage classes are discovered through shared interfaces, avoiding separate implementation lists.

An array stores an image's pixel values, but its representation depends on the processing library. To avoid manual conversions when connecting compatible functions, we built ArrayBridge to convert array formats and transfer data between central processing unit (CPU) and graphics processing unit (GPU) memory. Functions specify their array library and whether they accept image planes or volumes.

Processing functions need their inputs connected correctly: a measurement function, for example, needs the intended image and detected objects. We built a compiler that connects defined inputs and outputs, checks function requirements and plans data-format conversions and worker assignments before processing begins (Figure 2; Supp. Figure 1). Preparing these connections detects incompatible configurations early and reduces repeated planning during processing.

### Figure 1. Scientists can inspect and edit the agent's analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** OpenHCS brings input selection, analysis editing and execution status into one workspace, shown here with the ExampleHuman and ExampleFly image folders and a nine-step ExampleHuman analysis. The Plate Manager at left lists input collections and their analyses. The Pipeline Editor at right lists object-detection, measurement and export steps in execution order, with their settings available for editing. The lower-left server panel reports execution-server and desktop-connection status. Blue outlines identify these three regions; annotations indicate their roles. Scientists can prepare and follow the analysis from this window.
:::

### Execution and viewers

To let scientists check that measurements come from the intended cells or structures, we kept results linked to their source images and processing steps (Figure 2). Steps produce processed images, object-label images, numerical measurements, object relationships and exported files for inspection or further analysis. Label images assign an identifier to each detected cell, nucleus or other structure so later steps can measure individual objects. Object relationships associate related detections, such as a nucleus with its surrounding cell. Results retain their source coordinates, processing group and producing step when saved or delivered to napari or Fiji. Scientists can inspect the detections behind a measurement.

To use the same analysis across storage systems without rewriting each processing step, we built PolyStore to read and write local files, data held in memory, Zarr and OMERO. New storage destinations implement PolyStore's shared reading or writing interfaces rather than adding a separate storage path to every processing step.

To let scientists edit analyses and inspect images while processing continues, we built ZMQRuntime to coordinate ZeroMQ messages, process startup, shutdown and progress (Figure 2). Applications add operations, including viewer controls, through its client and server interfaces. To reduce repeated setup, workers reuse loaded libraries and CPU/GPU resources across assigned samples, then release them after the run. Execution uses processes by default, with optional threads.

Saving and live inspection can be configured independently: image results can be saved to a folder and sent directly to Fiji or napari as processing proceeds (Figure 2). Scientists can inspect results without finding and loading each output file manually. Viewer sessions remain open after execution for continued inspection, and agents can query napari layers and regions of interest. During processing, the streaming service checks viewer readiness and waits for display updates.

### Figure 1, continued. The laboratory's own Python joins the shared analysis

![Real Python definition and docstring, generated controls, live editable Python and agent-facing parameter descriptions.](figures/slas/submission_custom_function.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(B)** A laboratory-specific Python function is available through graphical controls, editable code and the agent interface. The function definition specifies its parameters; the docstring describes their meaning. OpenHCS uses this information to generate the parameter controls and descriptions available to an agent. The graphical form and Python views both show gain 1.2 and offset 0.0 for the same function. Scientists can therefore change a parameter through either view while agents work with that analysis, rather than maintaining separate graphical and scripted interfaces.
:::

### Agent access through MCP

Scientists need to inspect and continue an agent's analysis without reconstructing a separate workflow. We expose function discovery, pipeline editing and validation, execution and result inspection through MCP [@MCP]. Each operation's definition specifies its input and result types, implementation, permitted changes, data access and security requirements; these definitions generate the interface and govern execution. Agents can edit an analysis open in the desktop application or run one without opening a window.

To protect analyses from unintended access and conflicting edits, desktop connections require authentication and revision checks prevent an agent from overwriting intervening edits. MCP file operations check permitted directories. Processing functions run as Python code with the worker's permissions; these path checks are not an operating-system sandbox. Local clients communicate through standard input/output. The hosted HTTP interface offers selected read-only operations.

### CellProfiler import and output comparison

Established CellProfiler pipelines contain processing choices that laboratories need to preserve when changing software. We built an importer to make these pipelines editable in OpenHCS, then checked their images and measurements against native CellProfiler outputs before comparing execution times (Figure 6).

The importer reads `.cppipe` settings and converts processing and export modules into the same configurable steps used by other OpenHCS pipelines; setup modules are translated into the same source bindings used by other OpenHCS pipelines. Module definitions specify images, objects, measurements, relationships and image-group or plate-wide operation. The resulting pipeline uses OpenHCS compilation and execution and remains editable through graphical controls, Python and MCP. Named images and objects connect measurements to inputs. We reloaded generated Python for the advanced-segmentation and 3D-monolayer tutorials to check functions and parameters [@CellProfilerTutorials] (Supp. Data 5).

We checked that imported workflows retained their outputs by comparing numerical measurements and image pixels with absolute and relative tolerances of `1e-6`. Identifiers and categorical values were compared exactly after the documented formatting adjustments needed to match CellProfiler. Object-label images were compared exactly after standardizing dimensions of length one. Five workflows lacking exports received a final image or label export step without changing their processing settings. Every expected exported file was checked in each workflow. Supp. Data 1–2 provide output counts, comparison rules, imported modules and settings, and details of the additional software checks.

### Software reliability checks

To catch software changes that alter analysis results, we built automated checks around complete analysis tasks. The automated test workflow, known as continuous integration, is configured to run the 30 imported CellProfiler pipelines and compare their outputs with saved native results on Linux, Windows and macOS, each with Python 3.12 and 3.14. Other checks exercise storage, microscope inputs, live viewers and saving and reloading analysis settings (Supp. Table 2).

### Figure 2. One editable workflow connects editing, execution and inspection

![Shared editing, execution, workers, viewers and image storage.](figures/slas/shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
Graphical forms, Python and agents using MCP edit the same analysis, including imported CellProfiler pipelines. The editor sends compilation and execution requests to the execution server, which prepares the data connections and assigns processing to workers using ZMQRuntime's communication infrastructure. Worker processes load source images, execute the analysis on CPU or GPU resources and save images, object labels and measurements. Image and region-of-interest results can also be sent to napari or Fiji for inspection. Blue arrows show requests, compiled work and status updates between the editor, server and workers; green arrows connect workers with viewers and stored data. Progress returns to the editor while the analysis runs. Separating these processes allows image inspection and editing to remain available alongside processing. Supp. Figure 1 describes how image groups, function preparation and worker assignments are assembled.
:::

### Laboratory neurite assay

To test whether independent analyses recovered drug responses, we used images of primary cortical neurons from embryonic day 18 rats, imaged two days after plating. Fusicoccin-A (FC-A) and Y27632 were each tested at 0, 5, 10, 20 and 40 µM, with two technical wells per dose and dimethyl sulfoxide (DMSO) vehicle controls. Nine paired nuclear/neuronal fields were acquired per well. Culture media, stains and acquisition settings are given in Supp. methods: neurite morphometry.

### Autonomous analysis design

To test whether agents could turn biological requests into useful measurements, we asked fresh agents to develop and inspect analyses of cells, nuclei, neurites and protein redistribution. We compared their final results with references after analysis development had finished. Separate runs let us compare independently developed analyses of the same task.

The nuclear, cell-boundary and protein-translocation datasets came from the Broad Bioimage Benchmark Collection (BBBC). We distinguish independently developed analyses by numbering them within each biological task: nuclear detection analyses 1–4 use BBBC039, cell-boundary analyses 1–3 use BBBC007, and protein translocation analyses 1–2 use BBBC013. Numbers identify independent analyses, not successive repairs or quality rankings.

Each fresh agent received a task brief, acquisition information and MCP access. Nuclear detection 1, cell-boundary 1 and protein translocation 1 used gpt-5.6-sol; no OpenHCS instruction-guide version was recorded for those analyses. The gpt-6.1-sol agents also received the packaged OpenHCS skill, a written guide to using OpenHCS. Briefs could include channel hints, requested outputs and review instructions; the retinal task, for example, requested labels, measurements and counts of somata stained for RNA-binding protein with multiple splicing (RBPMS). Nuclear detection analyses 2–4 each used a different guide revision, while the three drug-response analyses used the same revision.

The skill asks agents to inspect images, read function documentation and compare results with matched raw images and overlays (Figure 3A). It directs repairs to the earliest faulty step and requires rechecking previously successful examples. Trial records document how agents followed it. Earlier trials used OpenHCS 0.8.5; later trials used 0.8.7.

### Figure 3. Delegated specialist work leaves an analysis the scientist can inspect

![Skill-directed workflow with Fiji and napari inspection, followed by the recorded H001 decisions and matched raw/repair images.](figures/slas/submission_autonomous_loop.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Analysis procedure described by the agent guide. The biological brief specifies the question, requested measurements and acquisition information. Image inspection establishes channels, feature scales and representative regions before the agent selects processing functions and runs the pipeline. Results are compared with raw images from the same region; errors lead to revised settings and further inspection before delivery. The scientist receives the analysis settings, images and measurements and can continue editing the analysis. **(B)** Four recorded versions of bright-object detection analysis 1 (H001) on one development image. Correcting an initially split object temporarily lost a neighbouring pair, which was recovered in the final version. The matched raw, first-result and final-result crops show the same region. Colours distinguish detections within each view rather than matching object identities across versions. Elapsed times start when the agent was asked to read its brief: approximately 14 min to the first completed execution and 45 min for the whole task, including inspection, corrections, reporting and cleanup.
:::

To prevent reference answers from guiding analysis development, agents finalized their pipelines before any comparison with reference data, and no pipeline changed after scoring began. They received no reference labels, accepted settings or score feedback while building their analyses. First-versus-final comparisons use the first completed prediction and the final settings on the same inputs. Self-directed repairs are autonomous; revisions prompted by a scientist are assisted. The earlier gpt-5.6-sol trials withheld evaluation images and treatment metadata until after finalization and changed only input and output folders for evaluation. The later gpt-6.1-sol trials gave agents development images and compared results with task-specific references after the agents finished.

Three fresh gpt-6.1-sol agents independently analysed the same 20 coded neurite-assay wells, with nine fields each, using the same brief, acquisition information, MCP access, guide revision and OpenHCS 0.8.7 installation. Each analysed all 180 fields and finalized its outputs before the evaluator opened treatment identities, MetaXpress measurements or assisted results. Development and subsequent review fields are listed in the cohort record (Supp. Data 8; Supp. Figure 5).

To evaluate nuclear detection on images none of the agents had opened, we identified those fields retrospectively from the image-delivery records. For nuclear detection analyses 2–4, at least one agent had opened 25 of the 200 fields, leaving 175 in the uninspected subset. This subset is reported separately from the images withheld in advance for nuclear detection analysis 1. Supp. Data 7–8 provide the original task briefs, guide versions, final pipelines, data partitions, scores, model and software versions, task times and computational usage.

### Endpoints and references

**Nuclear detection (BBBC039).** Analysis 1 used four development and 50 held-out fields; analyses 2–4 were evaluated on all 200 annotated fields and on the 175 retrospectively uninspected fields defined above. One-to-one matches required intersection over union (IoU) ≥ 0.5: the overlapping area had to be at least half the total area covered by the two outlines together. F1 balances finding reference nuclei against avoiding false detections, with 1 best. Pooled F1 combines object counts across fields; mean per-image F1 weights fields equally.

**Cell boundaries (BBBC007).** Analysis 1 used four development and 12 held-out DNA/actin fields; analyses 2–3 used all 16 fields. Boundary support is the fraction of predicted border pixels between touching cells that lie within two pixels of a manual outline; it does not measure recovery of every manual border.

**Protein translocation (BBBC013).** Analysis 1 used four development and 92 held-out wells, averaging cell-level ratios of mean nuclear to mean cytoplasmic green fluorescent protein (GFP) intensity within wells. Analysis 2 used median log2 ratios across cells with measurable cytoplasm, evaluating all 96 wells including four development wells. Z′ (Z-prime) measures control separation relative to well variation (1 ideal; above 0.5 excellent). Each drug had four positive and four negative control wells.

**Other image analyses.** Bright-object detection 1 (H001) matched first and final detections one-to-one to computational reference labels from a notebook-derived image. 3D nuclear localisation (H002) matched centres one-to-one to partial manual annotations within a predeclared 30-voxel radius. A voxel is a three-dimensional image pixel; lower centre-to-centre distances indicate more accurate localisation. Retinal RBPMS-positive somata were reviewed in matched raw, label and combined views across several regions.

**Neurites.** Public principal shafts and soma/path recovery in nine laboratory fields were inspected in matched views; the public comparison used the published NeuronCyto II image and algorithm output [@NeuronCytoII]. The three independent laboratory analyses were compared with MetaXpress well exports and the retained scientist-assisted analysis. OpenHCS endpoints were unweighted means of nine field-level values; each drug curve used its own two zero-dose DMSO wells. Overlapping fields were not deduplicated. This tests treatment-effect recovery, not manual tracing accuracy or identical branch definitions. The earlier method-directed demonstration and assisted transfer remain separate supplementary examples.

Fold changes divide measurements by their DMSO control mean. Pearson's correlation coefficient, r, describes whether measurements rise and fall together across wells; it does not establish identical values or effect sizes. Full scoring definitions are given in Supp. methods: analysis scoring; Supp. Data 7–8 retain the individual evaluations.

### Performance measurement

To compare execution without giving either application extra CPU resources, we used one physical CPU core, one worker and one numerical thread for each single-sample run, with one selected source well or sample per workflow, unchanged settings and defined comparison outputs. OpenHCS used Python 3.12; native CellProfiler 4.2.8.1 used Python 3.9, requiring SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]. OpenHCS used warmup followed by three measured repetitions; the native baseline was a complete first-use-inclusive serial batch.

**Timing intervals.** Processing included CellProfiler's internal initialization, image-group preparation, processing and final output steps, and OpenHCS's server work through saving and plate-level exports. Setup plus processing added CellProfiler pipeline preparation and invocation, or OpenHCS compilation, submission and waiting. Application and server startup, OpenHCS library loading, warmup and output-agreement checks were excluded. Speedup was CellProfiler's first-batch time divided by the median OpenHCS time; we summarize speedups across workflows using their minimum, arithmetic mean, median and maximum.

**Batching and workers.** Repeated copies of the same source sample measured batch-processing costs, not biological variation. Per-sample times divided the measured eight-sample CellProfiler batch by eight and the median of three measured one-worker, twelve-sample OpenHCS times by twelve. The CellProfiler batch used one numerical thread with four permitted CPUs, versus one CPU in the single-sample comparison. Twelve- and sixteen-sample CellProfiler times were estimated from measured eight-sample and post-initialization batches, with calibration on three workflows. Parallel CellProfiler projections assume evenly divided work, initialization per process and no concurrent slowdown; matching multicore runs were not measured. OpenHCS worker scaling was measured on the same twelve-sample workload for both timing intervals. Combined process memory was not measured. Supp. methods: execution-time estimates and Supp. Data 3 retain formulas, calibration and the full benchmark protocol.

## Results

Independent agents delivered analyses that scientists could inspect, change and reuse. The analyses recovered assay responses and detected biological structures, while image review identified repairs and remaining errors. All 30 tested CellProfiler pipelines retained their outputs on the newer software stack and ran faster in the matched single-core comparison.

### Scientists can inspect, revise and extend the analysis behind a measurement

Scientists could continue an agent's analysis through graphical controls or Python without recreating its settings. An agent's upper normalization-percentile change from 99.8 to 99.6 appeared in the form; restoring 99.8 updated the generated Python (Supp. Data 5). Registering a custom function also exposed its settings through both graphical and agent interfaces (Figure 1B).

### Agent-developed analyses produce useful assay measurements

Agents autonomously developed analyses that recovered neurite drug responses, detected nuclei and separated translocation controls without reference answers during development (Table 1).

Table: Table 1. Main results from the three neurite drug-response analyses, nuclear detection analyses 2–4 and protein translocation analysis 2, all using gpt-6.1-sol. Agent counts refer to independent agents within each assay. Agents could inspect development images while building their pipelines; the nuclear fields that none of them opened were identified afterwards. Supp. Data 7–8 give individual results, including nuclear detection 1, cell-boundary 1 and protein translocation 1 on held-out images.

| Assay | Agents | Evaluation inputs | Endpoint | Result |
|---|---|---|---|---|
| Laboratory neurite drug assay | 3 | 180 fields in 20 wells per agent | Control-normalized outgrowth responses | Both positive responses recovered by all three; magnitudes varied |
| Nuclear detection 2–4 (BBBC039) | 3 | 175 fields that none of the agents opened | Pooled detection F1 | 0.906 to 0.910 |
| Protein translocation 2 (BBBC013) | 1 | 96 wells including four development wells | Control separation, Z′: LY294002; Wortmannin | 0.849; 0.726 |

#### Three blind agents recover drug responses in a laboratory neurite assay

All three analyses found increased mean outgrowth per cell and total outgrowth at every nonzero dose of FC-A and Y27632 (Figure 4A–B). Across the 20 wells, each agent's mean outgrowth per cell correlated closely with MetaXpress (Pearson r 0.963 to 0.996). Effect sizes nevertheless differed by method: at 40 µM, fold changes in mean outgrowth per cell were 1.32 to 1.65 for FC-A and 1.49 to 1.69 for Y27632, against 1.98 and 2.05 for MetaXpress. Two agents were close to the scientist-assisted analysis, which gave 1.77 and 1.76; the third estimated smaller treatment effects. Cell-count fold changes were 0.94 to 0.99 for FC-A and 0.92 to 0.94 for Y27632, against 0.95 and 0.91 for MetaXpress.

Branches per cell increased at every nonzero dose and correlated with MetaXpress across wells (r 0.875 to 0.990), although fold responses were smaller. In analysis 3, higher control values compressed fold changes despite absolute increases closer to MetaXpress; the cause of the baseline difference was not established. Smaller branching responses also appeared in the assisted analysis and persisted in total branches and branches per primary process, so cell-count denominators alone do not explain the difference (Supp. Figure 5). These algorithm-defined measurements recover the treatment response but do not establish equivalent anatomical branching.

### Figure 4. Three independent agents recover both neurite outgrowth responses

![Drug responses from three independent blind agents, followed by separate public and laboratory neurite tracing demonstrations.](figures/slas/submission_neurite_results.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A–B)** Mean neurite outgrowth per cell after treatment with fusicoccin-A (FC-A) or Y27632. Three independent blind agents and MetaXpress analysed the same 180 fields from 20 wells; analyses 1–3 identify independent agent runs, not biological replicates. OpenHCS well values are unweighted means of nine fields. Each drug curve is normalized to the mean of its two zero-dose DMSO wells; 1 denotes no change from vehicle. Dots are two technical wells per dose for each method; whiskers show sample standard deviation (SD) among those wells, excluding uncertainty in the control mean. All three analyses recover increased outgrowth for both drugs, with smaller response magnitudes than MetaXpress. **(C–E)** Neurite tracing in a public image, comparing the raw field, initial OpenHCS analysis and published NeuronCyto II algorithm output [@NeuronCytoII] (CC BY-NC 4.0) at the same field scale. The published output, including its red circles and arrow, is an algorithm comparison, not manual ground truth. **(F–H)** A laboratory field shown as a raw image, detected cell bodies and neurites, and an overlay on the raw image. This separate nine-field autonomous analysis is not one of the three drug-response analyses in A–B. Scale bars in C, D and F–H are in image pixels. Supp. Figure 5 shows additional measurements and the scientist-assisted comparison.
:::

#### Three agents reach similar pooled nuclear accuracy

Independent agents may choose different pipelines for the same task; the practical question is whether they reach comparable accuracy. Nuclear detection analyses 2–4 reached pooled F1 of 0.906 to 0.910 on the 175 BBBC039 fields that none of their agents opened (Figure 5B). Across all 200 fields, including those the agents inspected, F1 was 0.898 to 0.906.

On the dataset's official 50-image test partition (5,720 nuclei), the agents' per-image mean F1 at IoU 0.5 was 0.898 to 0.903. Caicedo et al. used this dataset to evaluate learned and CellProfiler segmentation methods [@Caicedo2019]. Our agents received no reference labels while building their pipelines.

Most fields scored highly, but all three analyses shared difficult images. For each agent, 117 to 121 of the 175 uninspected fields reached F1 of at least 0.90. Most errors were missed nuclei, and all three agents scored below 0.80 on the same six fields. Similar pooled accuracy therefore did not remove the need to inspect individual images. Supp. Figure 3 and Data 8 give per-field agreement, error counts and a three-field repair that improved recovery but increased splitting. The earlier nuclear detection analysis 1 reached F1 0.746 and Dice area overlap 0.935 on 50 prospectively held-out fields (Supp. Data 7).

#### An agent-developed translocation analysis separates assay controls

For a screening assay, an analysis must separate biological controls, not merely produce plausible segmentations. Protein translocation analysis 2 analysed all 96 BBBC013 wells and obtained Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 5E). Z′ measures control separation relative to variation between wells; higher values mean clearer separation. Both exceed 0.5, the conventional threshold for an excellent screening assay [@Zhang1999]. The agent chose its own readout: each well's median log2 ratio of nuclear to cytoplasmic GFP across eligible cells. Cytoplasm could be measured around 14,631 of 17,320 nuclei (84.5%); this fraction varied with treatment (Supp. Figure 2). Four wells contributed to each treatment group. Protein translocation analysis 1 obtained Z′ of 0.554 for LY294002 and 0.751 for Wortmannin on 92 held-out wells (Supp. Data 7). The two analyses used different well summaries and evaluation sets, so these scores are not a controlled before-and-after comparison.

### Image review identifies repairs and remaining errors

Agents used image inspection to locate and correct split and merged detections. Bright-object detection analysis 1 (H001) increased F1 against computational reference labels from 0.929 to 0.944 on one development image (Figures 3B and 5A). On 16 BBBC007 DNA/actin fields, cell-boundary analyses 2 and 3 placed 0.743 and 0.740 of their predicted borders between touching cells within two pixels of a manual outline (Figure 5C). Figure 5F shows a local correction of merged nuclear detections; Figure 5G shows improved retinal cell-body outlines while neighbouring cells remain separate.

Three-dimensional images require checking object positions across image planes. Nuclear localisation analysis 1 (H002) recovered all 15 manually annotated centres within 30 voxels (Figure 5D,I). Eleven predictions had no matching annotation; because the reference covers only some centres, those predictions do not establish a false-detection rate. A separate agent corrected a continuous body divided between multiple detections in a 3D image (Figure 5H).

For datasets without exhaustive spatial annotations, we compared analysis results with the same raw-image regions. These examples include retinal cell bodies (Supp. Figure 4), a public NeuronCyto II field and nine laboratory neurite fields (Figure 4C–H). The comparisons show recovered structures and remaining errors; unresolved neurite crossings limit per-neuron path assignment. Figure 4C–E shows the public field's initial prediction. The final revision extended beyond principal shafts, and the shaft-only target was clarified after the run. These demonstrations involved one or two agents per task; Supp. Data 8 gives their analyses and reference definitions.

### Figure 5. Analysis accuracy and visible corrections

![Task-specific nuclear, boundary, volume and translocation endpoints alongside an independent nuclear-separation repair.](figures/slas/submission_analysis_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
Independent analyses were checked against reference labels and assay controls; matched images show a local nuclear repair. **(A)** Bright-object detection analysis 1 (H001), first and final detections on one development image. F1 balances precision and recall against computational reference labels (1 is perfect).
**(B)** Nuclear detection analyses 2–4 on 200 annotated BBBC039 fields and the 175 none of their agents opened, identified retrospectively. Pooled F1 combines object counts across fields; matches require intersection over union ≥ 0.5.
**(C)** Cell-boundary analyses 2–3, 16 BBBC007 fields each. Dots give the per-field fraction of predicted borders between touching cells within two pixels of manual outlines; horizontal lines pool border pixels. This does not measure recovery of every manual border.
**(D)** Mean centre-to-centre distance for matched 3D nuclei in H002. Labels give matches among 15 manual centres; the dashed line is the predeclared 30-voxel matching limit. Partial annotations prevent a false-detection estimate.
**(E)** Protein translocation analysis 2, 96 BBBC013 wells including four development wells. Dots are well medians of cell-level log2 nuclear/cytoplasmic green fluorescent protein (GFP) ratios; marks and whiskers show mean ± sample SD of four wells per dose. Drug panels share vertical limits. Z′ compares controls (four positive and four negative wells); values above 0.5 indicate excellent separation.
**(F)** Matched BBBC007 DNA-stained region: raw image, first nuclear detections and final separation of a merge. Colours distinguish nuclei within each view, not identities across views. Scale bar, 10 pixels.
:::

### Figure 5, continued. Correcting cell detection in two and three dimensions

![Matched retinal and volumetric body repairs, with separate finalized three-dimensional localisation evidence.](figures/slas/submission_quantitative_results.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(G)** Matched retinal regions showing raw RNA-binding protein with multiple splicing (RBPMS) signal, which marks the cell bodies, and first and final detections over the raw image. The final analysis reduces fragmented outlines while preserving a neighbouring pair of cells. Scale bar, 20 µm.
**(H)** A continuous body initially divided between multiple detections in a 3D image. The same XY region at Z = 36 is shown as raw signal, first labels, final labels and final labels over raw signal. This local repair is from a separate analysis, not a before-and-after comparison of H002 localisation accuracy.
**(I)** Finalized 3D nuclear localisation analysis 1 (H002), shown in XY, XZ and YZ. Label colours distinguish detected nuclei; yellow outlines and magenta in-plane centres locate detections in the orthogonal views. All 15 manually annotated centres have a prediction within the predeclared 30-voxel radius. Eleven predictions have no matching annotation; the partial reference does not establish whether these are false detections. Distances and scale bars in H–I are in voxel-index units, not calibrated physical lengths. Image panels are matched within each comparison; colours do not track object identities across versions.
:::

### Established CellProfiler workflows retain their outputs {#established-cellprofiler-workflows-retain-their-measurements}

Reusing an established analysis on a newer software stack requires preserving its outputs, not merely importing its settings. All 30 imported workflows reproduced native CellProfiler 4.2.8.1 outputs: exported label images matched native pixels and identifiers exactly, and numerical measurements met absolute and relative tolerances of 1e-6. OpenHCS produced these results with Python 3.12 and NumPy 2; native CellProfiler 4.2.8.1 ran with Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0. The tested workflows therefore retained their outputs without retaining CellProfiler's older runtime and dependency versions. The comparison included 21 workflows with comma-separated values (CSV) tables, three with SQLite databases and six with image or array outputs only. Five workflows received added exports comprising five label images and three numerical images (Supp. Data 1).

The workflows covered DNA damage, human and Drosophila morphology, tumor morphology, Cell Painting, protein translocation, wound healing, tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening and *C. elegans* phenotyping. Seven workflows had image comparisons, including the translocation overlay alongside SQLite measurements. Advanced segmentation and 3D monolayer imports were reloaded as editable Python with their named structures, measurements and processing sequences (Supp. Data 5). Output equivalence thus extended across complete preprocessing, segmentation, measurement and export workflows, including multi-stage 3D analysis.

To show what was checked beyond the 30 complete workflows, Figure 6A separates three levels of module evidence. Of 85 processing modules, 54 were tested in complete workflows and another 29 individually. For the remaining two, tests covered shared components rather than each module's own algorithm.

### Faster execution supports iteration and larger experiments

Revising an analysis requires rerunning it, and larger experiments repeat that work across many fields. We therefore measured execution with output export included, checking that faster processing preserved the results.

Every one of the 30 workflows was faster than CellProfiler on one core, both for processing alone and with pipeline setup included (Figure 6B). When CellProfiler's internal initialization was spread over a measured eight-sample serial batch, the median per-sample processing speedup across workflows was [pending]{.benchmark-claim key=amortized_execution_median}-fold, with a minimum of [pending]{.benchmark-claim key=amortized_execution_min}-fold. This comparison divides each application's time by the number of samples: eight for CellProfiler and twelve for OpenHCS, using one worker. Including pipeline setup, speedup was a median [pending]{.benchmark-claim key=amortized_total_median}-fold, with minimum [pending]{.benchmark-claim key=amortized_total_min}-fold. The largest processing gain, [pending]{.benchmark-claim key=amortized_execution_max}-fold, came from an illumination-correction workflow whose large median filter took CellProfiler about 950 s per sample at both first and repeated use. Outputs matched during warmup and every measured repetition. Supp. Data 3 provides individual workflow timings, batch summaries, CellProfiler estimates and calibration checks.

The measured eight-sample comparison also favoured OpenHCS for every workflow, both for processing alone and with pipeline setup included, using two workers against one serial CellProfiler process. Every workflow remained faster in the twelve- and sixteen-sample comparisons, which use estimated CellProfiler times. These comparisons use different worker counts.

To compare parallel execution with equal CPU resources, Figure 6C matches core counts and samples per core. OpenHCS times were measured; CellProfiler times were estimated from measured initialization costs and per-sample processing times, assuming evenly divided work across independent processes, each with its own initialization cost, and no concurrent slowdown. The timing formula was checked against serial batches; matching multicore CellProfiler runs have not been measured.

On the same twelve-sample workload, every workflow ran faster with two, three and four workers than with one, both for processing alone and with setup included (Supp. Figure 6). All these OpenHCS times were measured. Batches repeat copies of the same image sample to measure processing speed, not biological variation.

### Figure 6. CellProfiler compatibility and execution speed

![Graded module coverage, measured one-worker comparisons and matched-core CellProfiler projections, with all thirty workflows shown as points.](figures/slas/submission_benchmark_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
Imported CellProfiler workflows were checked for output agreement before their execution times were compared. **(A)** Strongest test per module; zero-count categories have no slice. Shared-code tests do not test each module's own algorithm. **(B)** Measured one-worker comparisons: one sample each, then per-sample time for batches of eight (CellProfiler) or twelve (OpenHCS). **(C)** Matching cores and samples: measured OpenHCS versus estimated CellProfiler. Estimates assume independent single-threaded processes, each with initialization, evenly divided work and no parallel slowdown. Some per-process batch sizes fall below the validated range (Supp. Data 3). **(B, C)** Speedup is CellProfiler time divided by OpenHCS time; values above 1 mean faster OpenHCS execution. Each dot is one of 30 workflows; translucent bars are arithmetic means and black lines medians. Each distribution is labelled with its minimum, arithmetic mean, median and maximum speedup. Logarithmic axes; red dashed line is equal speed, guides are 2×, 4× and 10×. OpenHCS times are medians of three runs after warmup. Setup includes compilation; both CellProfiler timing measures include initialization. External startup, OpenHCS library loading and warmup are excluded. Repeated samples measure processing, not biological variation.
:::

## Discussion

OpenHCS connects existing analysis software through a native Python layer so that laboratories can delegate technical analysis work while retaining control of the resulting measurements. Changes move between graphical controls and editable Python in the same delivered pipeline, so scientists can inspect, revise and extend it while agents continue working on that analysis.

Agreement on a treatment response did not imply identical measurements. All three neurite analyses recovered both drug responses but estimated smaller effects than MetaXpress (Figure 4A–B). Similarly, close pooled nuclear scores concealed shared difficult fields with missed nuclei (Figure 5B). Linking measurements to visible detections lets scientists identify where refinement is needed and keep measurement definitions explicit when comparing effect sizes.

Preserving the outputs of established workflows lets laboratories extend analyses without discarding their existing processing choices. The 30 CellProfiler workflows retained their outputs on OpenHCS's newer Python environment (Figure 6). Scientists can extend these pipelines with compatible CPU, GPU and deep-learning functions from existing libraries or laboratory code as biological questions change.

Faster reruns reduce the cost of inspecting a result, changing the pipeline and checking it again across an experiment. With one worker and CellProfiler initialization spread across eight samples, OpenHCS retained a median [pending]{.benchmark-claim key=amortized_execution_median}-fold per-sample speedup (Figure 6B). The advantage persisted with pipeline setup included, and additional OpenHCS workers shortened execution further. Thus the measured speed advantage supports iteration by scientists and agents without depending on extra CPU cores.

Separating general computing tasks from microscope-specific definitions also makes the components reusable outside microscopy. We built the eight libraries in Supp. Table 1 for graphical controls, edit history, Python editing, storage and interprocess communication. Pipelines organize data by dimensions and processing groups without requiring microscope-specific fields; source tests include remote-sensing and telemetry examples. Work is underway to release preparation and execution separately as ArrayPipe [@ArrayPipe], so other data-science and machine-learning applications could combine array libraries, run processing steps in parallel and inspect intermediate results.

The trials evaluate complete agent-developed analyses, combining the model, written guide and OpenHCS runtime. The treatment-assay cohort held these components fixed; the broader trial series varied model and guide versions as recorded in Methods. This design supports comparison of the delivered analyses, while controlled component studies would be needed to attribute reliability to any one part. The nuclear uninspected subset was identified retrospectively, and independent agents analysed the same experimental material rather than adding biological replicates.

OpenHCS addresses analysis development and execution within laboratory automation. Systems using SiLA, a standard for laboratory automation, connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]. In either a conventional or automated laboratory, the aim is to delegate technical analysis work while keeping scientists able to judge, change and extend it.

## Supp. Data {#supplementary-data}

Supp. figures provide additional assay results and image comparisons. Supp. Data 1–3 contain CellProfiler output comparisons, module coverage and timing measurements; Data 4–6 contain NeuronCyto references, editable workflows and software checks; Data 7–8 contain agent instructions, final pipelines, evaluation partitions and individual analysis results.

## Code and Data Availability

OpenHCS source code: <https://github.com/OpenHCSDev/OpenHCS>.

OpenHCS documentation: <https://openhcs.readthedocs.io/>.

Supp. files contain figure inputs and generation scripts, final pipelines, scores and benchmark measurements. Repository copies are available at <https://github.com/OpenHCSDev/openhcs/tree/main/paper/supplementary> and <https://github.com/OpenHCSDev/openhcs/tree/main/benchmark/results>.

The benchmark uses biological images and pipelines distributed by the CellProfiler project. Original sources:

- official CellProfiler example pipelines and images: <https://github.com/CellProfiler/examples> [@CellProfilerExamples]
- official CellProfiler tutorial pipelines and images: <https://github.com/CellProfiler/tutorials> [@CellProfilerTutorials]
- CellProfiler 4 benchmark supplement: <https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics> [@Stirling2021]

The [benchmark protocol](../benchmark/results/matched_worker_sweep_20261008_latestproduction/README.md) specifies the workloads, software versions, hardware and timing reports.

Supp. Table 1 links the source repositories for the eight reusable libraries.

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
