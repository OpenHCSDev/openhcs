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

Getting measurements from microscopy images often means knowing which specialized tools to use, then installing, setting up and connecting them. OpenHCS brings image-processing tools together through a native Python layer. Scientists can inspect detections and change analyses through a graphical interface or Python. Laboratories can add their own image-processing steps and reuse existing CellProfiler pipelines. Measurements remain linked to their source images and samples. AI agents access the same analysis tools to build and run analyses, inspect results and correct errors. Starting from written prompts, independent agents recovered drug responses, detected nuclei and distinguished positive and negative assay controls. All 30 tested CellProfiler pipelines retained their measurements and ran faster with both applications using one processor core. OpenHCS extends laboratory automation to building and running analyses that scientists inspect, change and reuse.

## Introduction

Fluorescence microscopy can reveal changes in cell number, neurite growth and the location of proteins. Measuring these features may require several tools: one to reduce image noise or background, another to find cells or other structures and another to measure their shapes or signals. The choice of tools depends on the biological question and the images.

Established tools provide the foundations for this work. ImageJ/Fiji and napari support image inspection and processing [@Schneider2012; @Schindelin2012; @NapariPlugins]; CellProfiler organizes repeatable analysis workflows [@Carpenter2006; @McQuin2018]; OMERO manages images and their associated information [@Allan2012]; and Icy combines viewing, plugins and graphical workflows [@deChaumont2012]. Cellpose finds cells and N2V2 reduces image noise, with both available through Fiji and napari plugins [@Stringer2021Cellpose; @Hock2022N2V2; @FijiCellpose; @CellposeNapari; @NapariN2V].

Scientists can also connect tools and add their own code through Python. PyImageJ connects ImageJ to Python, napari-imagej makes ImageJ tools available in napari, and magicgui turns Python functions into controls beside images [@Rueden2022PyImageJ; @NapariImageJ; @NapariMagicgui; @NapariWidgetWorkshop]. The [software-resource inventory](supplementary/software_resources.md) compares extension routes and learning resources. Python access alone does not connect the images, detections and measurements or make differing software-version requirements compatible. Someone must preserve channel names, image dimensions, pixel sizes and sample identities, connect steps and configure their settings. Adding a new way to find cells or measure their signals may also require changes to graphical controls and scripts.

Docker containers package tools with the software versions they need, reducing conflicts between installations. Existing integration systems connect tools in several ways: Fiji–CellProfiler workflows exchange images and tables through scripts [@Dobson2021]; BioImageIT packages processing environments alongside image-data management [@Prigent2022]; CellProfiler plugins support Python integration and Docker execution [@Weisbart2024]; and MCMICRO coordinates tissue-imaging tools through containers and files [@Schapiro2022; @MCMICROImplementation]. For each experiment, someone must still choose settings and check the resulting measurements.

Community support documents the practical work of installing and using image-analysis software. The 2019 image.sc paper reported approximately 10,000 users and more than 15,000 posts per year, including general discussion and requests for help [@Rueden2019Forum]. A 2023 study of approximately 500 recent threads found installation mentioned in 9.9% of opening posts and somewhere in approximately 19% of threads [@Ouyang2023]. These observations place software setup among the practical barriers to biological analysis.

AI assistants build and check image analyses from written requests. BioImage.IO Chatbot connects community resources to analysis extensions, and Omega generates and runs Python and creates napari controls from natural-language requests [@Lei2024; @Royer2024]. Agentic-J uses bioimage knowledge, plugin instructions and specialized agents to develop and audit Fiji scripts. It also connects external tools through the Model Context Protocol (MCP), which lets agents call software operations [@Johanns2026]. BIABench compares agent analyses with reference answers and expert assessments; agents performed better on routine 2D tasks, while repeated runs were unreliable on more complex data [@Pan2026BIABench].

OpenHCS brings tools from the bioimage-analysis ecosystem together through a native Python layer. Connected image-processing steps form a pipeline (Figure 2), using different Python libraries, a laboratory's own code and imported CellProfiler pipelines. Scientists can inspect detections and change the same analysis through a graphical interface or Python (Figure 1A). OpenHCS uses PyImageJ to show results in Fiji and generates controls for each image-processing step. Laboratories can add their own steps with the same controls and agent access, without programming separate interfaces (Figure 1B). OpenHCS processes samples in parallel and keeps measurements linked to their source images and samples. AI agents access the same analysis tools through MCP. Given a description of what to measure, such as how a drug changes neurite growth, an agent builds and runs the analysis, inspects detections against images and corrects errors.

We evaluated OpenHCS through shared editing, biological analyses and imported CellProfiler workflows. We recorded changes to the same pipeline settings through graphical controls, Python and agents. Independent agents developed analyses of neurite growth, nuclei and protein redistribution. We compared their results with references after the agents had finished their analyses. We also compared the outputs and execution times of 30 imported CellProfiler workflows. Across biological assays, agents built and ran analyses that laboratories can inspect, change and reuse.

## Materials and Methods

### Pipeline model

Processing methods need compatible inputs before they can be combined: a measurement step must receive the correct image and detected objects, and functions from different libraries may use different array formats. OpenHCS prepares these connections before execution. This compilation step determines which data and array formats each function requires and connects its outputs to subsequent steps (Supplementary Figure 1). Functions run in their declared order, using shared defaults or settings chosen for an individual step.

A function's Python signature supplies its parameter names, types and defaults; its docstring describes what it does. OpenHCS uses these definitions to generate graphical controls, editable Python and agent access, avoiding separate interfaces for a laboratory's custom methods. Each function also declares its processing library and whether it accepts image planes or volumes. Libraries can run on the central processing unit (CPU), a graphics processing unit (GPU), or both. ArrayBridge converts arrays between NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto, allowing their functions to run together without hand-written conversion steps (Supplementary Table 1).

Scientists can move between graphical controls, Python and agent editing while working on the same functions and settings. ObjectState stores those settings and their edit history; Pycodify converts the pipeline to editable Python and reads changes back into the same analysis.

Scientists and agents extend an analysis by registering Python functions with these same declarations, including preprocessing and deep-learning methods. Illumination correction uses a version of BaSiCPy maintained by OpenHCS, and N2V2 denoising runs in PyTorch with CUDA, NVIDIA's GPU-computing platform.

Measurements must remain associated with the correct sample, field and channel as images are grouped or combined into stacks. Input selections specify which channels, planes or stacks each step reads and how images are grouped for processing. Later steps inherit or replace these choices. Sample, site, channel, plane and time coordinates stay attached to the results. Microscope handlers identify the acquisition files for each well, site, channel and plane. Bio-Formats reads microscopy file formats produced by different instruments. OME-Zarr stores microscopy data in blocks, allowing selected image regions to be retrieved without downloading the entire dataset [@Moore2021]; OpenHCS reads its images, dimensions, channels and pixel sizes. Experimental OMERO support provides access to images in a shared image-management server. Users can assign channel and image roles explicitly when acquisition metadata are insufficient. Supplementary Table 1 lists the eight reusable libraries behind the runtime.

### Figure 1. Scientists can inspect and edit the agent's analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** OpenHCS brings input selection, analysis editing and execution status into one workspace, shown here with the ExampleHuman and ExampleFly image folders and a nine-step ExampleHuman analysis. The Plate Manager at left lists input collections and their analyses. The Pipeline Editor at right lists object-detection, measurement and export steps in execution order, with their settings available for editing. The lower-left server panel reports execution-server and desktop-connection status. Blue outlines identify these three regions; annotations indicate their roles. Scientists can prepare and follow the analysis from this window.
:::

### Execution and viewers

Measurements and detected objects need to remain traceable to their images and processing steps. Steps produce processed images, object-label images, numerical measurements, object relationships and exported files. Label images assign an identifier to each detected cell, nucleus or other structure so later steps can measure individual objects. Object relationships associate related detections, such as a nucleus with its surrounding cell. Each function declares its inputs and outputs, and compilation connects later steps to those sources. Results retain their source coordinates, processing group and producing step when saved or delivered to napari or Fiji. Saving and viewer delivery can be configured independently.

The execution server uses ZeroMQ, a messaging library, to coordinate requests and workers. Each worker reuses its loaded libraries and CPU or GPU execution resources while processing its assigned samples, then releases its resources when the run finishes. Workers use processes by default, with threads available as a configuration option. Storage routes include local files, in-memory data, Zarr and OMERO.

The streaming service checks viewer readiness and waits for display updates. Viewer sessions remain open for inspection after execution, and agents can query napari layers and regions of interest.

### Figure 1, continued. The laboratory's own Python joins the shared analysis

![Real Python declaration and docstring, generated controls, live editable Python and agent-facing parameter descriptions.](figures/slas/submission_custom_function.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(B)** A laboratory-specific Python function is available through graphical controls, editable code and the agent interface. The function declaration defines its parameters; the docstring describes their meaning. OpenHCS uses this information to generate the parameter controls and descriptions available to an agent. The graphical form and Python views both show gain 1.2 and offset 0.0 for the same function. Scientists can therefore change a parameter through either view while agents work with that analysis, rather than maintaining separate graphical and scripted methods.
:::

### Agent access through MCP

Agents discover functions, edit and validate pipelines, execute analyses and inspect progress and results through MCP [@MCP]. Each operation declares request and result types, implementation, permitted changes, data access and security requirements. These declarations generate the interface and govern execution.

Function descriptions let agents select methods and edit the analysis. Registering a custom function makes its parameters and documentation available in the graphical controls and MCP tool list (Figure 1B). Agents can edit an analysis open in the desktop application or run a separate analysis without opening a window. Local clients communicate through standard input/output. Desktop connections require authentication; revision checks prevent an agent from overwriting intervening edits, and MCP file operations check permitted directories. Processing functions run as Python code with the worker's permissions; these path checks are not an operating-system sandbox. The hosted HTTP interface offers selected read-only operations.

### CellProfiler import and output comparison

The importer turns established CellProfiler workflows into editable OpenHCS analyses by reading their `.cppipe` modules and settings. Setup modules define image sources; processing and export modules become OpenHCS steps. Each module declaration specifies images, objects, measurements and relationships and whether it operates per image group or across the plate. The same function is available through GUI, Python and MCP. Named images and objects connect measurements to their inputs. Generated Python was reloaded for the advanced segmentation and 3D monolayer tutorials to check functions and parameters [@CellProfilerTutorials] (Supplementary Data 5).

We checked that imported workflows retained their outputs by comparing numerical measurements and image pixels with absolute and relative tolerances of `1e-6`. Identifiers and categorical values were compared exactly after the documented formatting adjustments needed to match CellProfiler. Object-label images were compared exactly after standardizing dimensions of length one. Five workflows lacking exports received a final image or label export step without changing their processing settings. Supplementary Data 1 lists the outputs and comparison rules; Supplementary Data 2 lists the imported modules and settings. Every expected exported file was checked in each workflow; Supplementary Data 1 gives per-workflow counts.

Continuous integration compares all 30 workflows with committed native CellProfiler references through ZeroMQ on Linux with Python 3.12 and 3.14, and on Windows and macOS with Python 3.14. Supplementary Data 1 describes the additional execution, storage, microscope, installation and desktop tests.

### Figure 2. One editable workflow connects editing, execution and inspection

![Shared editing, execution, workers, viewers and image storage.](figures/slas/shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
Graphical forms, Python and agents using MCP edit the same analysis, including imported CellProfiler pipelines. The editor sends compilation and execution requests to the ZeroMQ server, which prepares the data connections and assigns processing to workers. Worker processes load source images, execute the analysis on CPU or GPU resources and save images, object labels and measurements. Image and region-of-interest results can also be sent to napari or Fiji for inspection. Blue arrows show requests, compiled work and status updates between the editor, server and workers; green arrows connect workers with viewers and stored data. Progress returns to the editor while the analysis runs. Separating these processes allows image inspection and editing to remain available alongside processing. Supplementary Figure 1 describes how image groups, function preparation and worker assignments are assembled.
:::

### Laboratory neurite assay

Primary cortical neurons from embryonic day 18 (E18) rats were imaged two days after plating. Fusicoccin-A (FC-A) or Y27632 was added when the initial Dulbecco's modified Eagle medium containing fetal bovine serum was replaced with supplemented Neurobasal medium. Each compound was tested at 0, 5, 10, 20 and 40 µM, with two technical wells per dose; zero-dose wells contained dimethyl sulfoxide (DMSO) vehicle. Paired nuclear-stain and neuronal-signal images were acquired at nine fields per well, with a pixel size of 1.3556 µm. The nuclear stain was 4′,6-diamidino-2-phenylindole (DAPI). Each channel was recorded as a 1024-by-1024-pixel image at one Z position and one timepoint; neuronal signal was recorded in the FITC channel.

### Autonomous analysis design

The nuclear, cell-boundary and protein-translocation datasets came from the Broad Bioimage Benchmark Collection (BBBC). We distinguish independently developed methods by numbering analyses within each biological task: nuclear detection analyses 1–4 use BBBC039, cell-boundary analyses 1–3 use BBBC007, and protein translocation analyses 1–2 use BBBC013. Numbers identify independently developed methods, not successive repairs or quality rankings. Supplementary Data 8 links these names to the original run records.

Each analysis used a fresh agent, which received a biological task brief, acquisition information and MCP access. Nuclear detection 1, cell-boundary 1 and protein translocation 1 used gpt-5.6-sol; no OpenHCS instruction-guide version was recorded for those analyses. The gpt-6.1-sol agents also received the packaged OpenHCS skill, a written guide to using OpenHCS. Briefs could include channel hints, requested outputs and review instructions; the retinal task, for example, requested labels, measurements and counts of somata stained for RNA-binding protein with multiple splicing (RBPMS). Supplementary Data 8 summarizes the original briefs and records the instruction versions: nuclear detection analyses 2–4 each used a different revision, while the three drug-response analyses used the same revision.

The skill instructs agents to inspect channels and representative regions, measure feature sizes, read function documentation, build and run a pipeline, and compare the same region as a raw image, an analysis result and an overlay of both. Agents correct the earliest step causing an error, then check that the change fixes the problem without breaking previously successful examples. Figure 3A shows this procedure; individual trial records show how agents followed it. Earlier trials used OpenHCS 0.8.5; later trials used 0.8.7.

### Figure 3. Delegated specialist work leaves an analysis the scientist can inspect

![Skill-directed workflow with Fiji and napari inspection, followed by the recorded H001 decisions and matched raw/repair images.](figures/slas/submission_autonomous_loop.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Analysis procedure described by the agent guide. The biological brief specifies the question, requested measurements and acquisition information. Image inspection establishes channels, feature scales and representative regions before the agent selects methods and runs the pipeline. Results are compared with raw images from the same region; errors lead to revised settings and further inspection before delivery. The scientist receives the analysis settings, images and measurements and can continue editing the method. **(B)** Four recorded versions of bright-object detection analysis 1 (H001) on one development image. Correcting an initially split object temporarily lost a neighbouring pair, which was recovered in the final version. The matched raw, first-result and final-result crops show the same region. Colours distinguish detections within each view rather than matching object identities across versions. Elapsed times start when the agent was asked to read its brief: approximately 14 min to the first completed execution and 45 min for the whole task, including inspection, corrections, reporting and cleanup.
:::

Agents finalized their pipelines before any comparison with reference data, and no pipeline changed after scoring began. They received no reference labels, accepted settings or score feedback while building their analyses. First-versus-final comparisons use the first completed prediction and the final settings on the same inputs. Self-directed repairs are autonomous; revisions prompted by a scientist are assisted. The earlier gpt-5.6-sol trials withheld evaluation images and treatment metadata until after finalization and changed only input and output folders for evaluation. The later gpt-6.1-sol trials gave agents development images and compared results with task-specific references after the agents finished.

For the laboratory treatment assay, three new gpt-6.1-sol agents independently analysed the same 20 coded wells, each containing nine fields. All received the same biological brief, acquisition information, MCP access and fixed version of the packaged skill using the same OpenHCS 0.8.7 installation. They chose six, four and eight development fields and, after fixing their methods, reviewed 20, eight and twelve further fields. Each analysed all 180 fields, and its final outputs were fixed before the evaluator opened treatment identities, MetaXpress measurements or assisted results. Supplementary Figure 5 reports the individual agents.

For nuclear detection analyses 2–4, image-delivery records identified 25 of the 200 fields as opened by at least one agent. The remaining 175 fields, which none of the three agents opened, form the uninspected subset used for retrospective evaluation. This retrospectively identified subset is reported separately from the images withheld in nuclear detection analysis 1. Supplementary Data 7–8 provide final pipelines, data partitions, scores, model and software versions, task times and computational usage.

### Endpoints and references

**Nuclear detection (BBBC039).** Nuclear detection analysis 1 used four development fields and 50 held-out fields, meaning images withheld until the method was finalized. Analyses 2–4 were evaluated on all 200 annotated fields and separately on the 175 fields none of their agents had inspected. Each detected nucleus could match at most one reference nucleus. A match required intersection over union (IoU) ≥ 0.5: the overlapping area had to be at least half the total area covered by the two outlines together.

Precision was the fraction of detections matched to reference nuclei; recall was the fraction of reference nuclei detected. F1 was their harmonic mean, ranging from 0 to 1. Pooled F1 combined object counts across fields before scoring; mean per-image F1 gave each field equal weight. Dice measured overlap of detected and reference areas, from 0 to 1; splitting and merging were evaluated separately. Signed count error was the detected count minus the reference count. Split and merge checks identified reference nuclei detected as several objects, or several nuclei detected as one.

**Cell boundaries (BBBC007).** Cell-boundary analysis 1 used four development and 12 held-out DNA/actin fields. Analyses 2–3 were evaluated on all 16 fields. The directed boundary fraction is the proportion of predicted border pixels between touching cells that lie within two pixels of a manual outline. Higher values mean that more of the predicted borders follow the manual outlines; this does not measure whether every manual border was found.

**Protein translocation (BBBC013).** Protein translocation analysis 1 used four development and 92 held-out wells. It measured mean green fluorescent protein (GFP) intensity in each cell's nucleus divided by mean GFP intensity in its cytoplasm, then averaged those ratios within each well. Protein translocation analysis 2 used each well's median log2 nuclear-to-cytoplasmic GFP ratio across cells with measurable cytoplasm. On this log2 scale, 0 means equal nuclear and cytoplasmic intensity, and 1 means twice the intensity in the nucleus. Analysis 2 was evaluated on all 96 wells, including four development wells.

Control separation was quantified by Z′ (Z-prime): 1 minus three times the sum of the positive and negative control groups' sample standard deviations, divided by the absolute difference between their means. Each drug had four positive and four negative control wells. Z′ of 1 indicates ideal separation with no within-group variation; values above 0.5 indicate an excellent screening assay. Standard deviation (SD) describes variation among wells.

**Bright-object detection (H001).** First and final detections were matched one-to-one to computational reference labels from a notebook-derived image.

**3D nuclear localisation (H002).** Predicted centres were matched one-to-one to manually marked centres within a predeclared 30-voxel radius. A voxel is a three-dimensional image pixel; lower centre-to-centre distances indicate more accurate localisation.

**Retina.** RBPMS-positive soma detection was reviewed in matched raw, label and combined views across several regions.

**Neurites.** Principal shafts in the public field and soma/path recovery in nine laboratory fields were inspected with matched raw and result views. The public comparison used the published NeuronCyto II image and algorithm output [@NeuronCytoII]. Three later independent laboratory analyses were compared with MetaXpress well exports and the retained scientist-assisted analysis. Each endpoint was the unweighted mean of nine field-level values; each drug curve used its own two zero-dose DMSO wells. Overlapping fields were not deduplicated. The comparison tests recovery of treatment effects, not manual tracing accuracy or identical branch definitions. The earlier method-directed demonstration and assisted transfer remain in the supplement.

For drug responses, fold change is the measurement divided by its DMSO control mean: 1 means no change, 2 means double and 0.5 means half. Pearson's correlation coefficient, r, describes whether two methods' measurements rise and fall together across wells. It ranges from −1 to 1; values near 1 indicate a strong positive linear relationship, but do not mean that the methods give identical values or effect sizes.

### Performance measurement

To compare execution with equal parallel resources, the matched single-sample benchmark used one physical CPU core, one worker and one numerical thread. OpenHCS ran with Python 3.12 and native CellProfiler 4.2.8.1 with Python 3.9. That CellProfiler release requires SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]; the comparison tests whether its workflows retain their outputs on OpenHCS's newer scientific Python environment. Each workflow used one selected source well or sample, with unchanged processing settings and the declared comparison outputs. OpenHCS used a warmup followed by three measured repetitions. The native baseline was one complete first-use-inclusive serial CellProfiler batch; its natural internal initialization remained included. Source revisions, workloads, hardware and environments accompany the matched benchmark in Supplementary Data 1 and 3.

**Timing intervals.** CellProfiler processing time included its internal initialization, preparation of image groups, processing and final output steps. OpenHCS processing time included the server's work through saving results and plate-level exports. Neither measurement included starting the applications or server; loading OpenHCS libraries, warmup and checking output agreement were also excluded. We additionally measured setup plus processing: preparing and calling the CellProfiler pipeline, or compiling the OpenHCS pipeline, submitting it and waiting for completion. Speedup was CellProfiler's first-batch time divided by the median of three OpenHCS times. We report the median speedup across workflows.

**Batch comparisons.** Batches repeated the same selected source sample. To compare time per sample, we divided CellProfiler's measured eight-sample batch time by eight and the median of three single-worker, twelve-sample OpenHCS times by twelve. This spreads the initial setup cost over the batch. The CellProfiler batch used one numerical thread with four permitted CPUs; its single-sample comparison used one CPU. We estimated twelve- and sixteen-sample CellProfiler times from the measured eight-sample batch and repeated runs after initialization. Supplementary Data 3 gives the timing definitions, estimation formula and checks against measurements for three workflows. Combined memory use across the application and its workers was not measured.

**Parallel processing.** OpenHCS worker counts were compared on the same twelve-sample workload using measured processing and setup-plus-processing times throughout.

## Results

### Scientists can inspect, revise and extend the analysis behind a measurement

Graphical controls, Python and agents changed the same analysis settings. An agent changed the upper percentile used for image normalization from 99.8 to 99.6, and the graphical form showed 99.6. Changing the setting back to 99.8 also updated the generated Python (Supplementary Data 5). Registering a custom Python function made its settings available through the graphical controls and agent interface (Figure 1B). Scientists could therefore continue editing the agent's analysis or extend it with their own functions.

### Agent-developed methods produce useful assay measurements

Agents developed analyses that recovered neurite drug responses, detected nuclei and separated translocation controls without reference answers during method development (Table 1).

Table: Table 1. Main results from the three neurite drug-response analyses, nuclear detection analyses 2–4 and protein translocation analysis 2, all using gpt-6.1-sol. Agent counts refer to independent agents within each assay. Agents could inspect development images while building their pipelines; the nuclear fields that none of them opened were identified afterwards. Supplementary Data 7–8 give individual results, including nuclear detection 1, cell-boundary 1 and protein translocation 1 on held-out images.

| Assay | Agents | Evaluation inputs | Endpoint | Result |
|---|---|---|---|---|
| Laboratory neurite drug assay | 3 | 180 fields in 20 wells per agent | Control-normalized outgrowth responses | Both positive responses recovered by all three; magnitudes varied |
| Nuclear detection 2–4 (BBBC039) | 3 | 175 fields that none of the agents opened | Pooled detection F1 | 0.906 to 0.910 |
| Protein translocation 2 (BBBC013) | 1 | 96 wells including four development wells | Control separation, Z′: LY294002; Wortmannin | 0.849; 0.726 |

#### Three blind agents recover drug responses in a laboratory neurite assay

We tested whether independently authored analyses recovered drug responses in laboratory data without access to treatment identities or commercial measurements. Three agents independently analysed the same coded 20-well neurite outgrowth experiment. All three found increased mean outgrowth per cell and total outgrowth at every tested dose of FC-A and Y27632 (Figure 4A–B). Across the 20 wells, each agent's mean outgrowth per cell correlated closely with MetaXpress (Pearson r 0.963 to 0.996). All three analyses recovered the biological responses, with method-dependent effect sizes: at 40 µM, fold changes in mean outgrowth per cell were 1.32 to 1.65 for FC-A and 1.49 to 1.69 for Y27632, against 1.98 and 2.05 for MetaXpress. Two agents were close to the scientist-assisted analysis, which gave 1.77 and 1.76; the third estimated smaller treatment effects. Cell-count fold changes were 0.94 to 0.99 for FC-A and 0.92 to 0.94 for Y27632, against 0.95 and 0.91 for MetaXpress.

Branches per cell increased at every tested dose and correlated with MetaXpress across wells (r 0.875 to 0.990), although fold responses were smaller. In analysis 3, higher control values compressed fold changes despite absolute increases closer to MetaXpress; the cause of the baseline difference was not established. Smaller branching responses also appeared in the assisted analysis and persisted in total branches and branches per primary process, so cell-count denominators alone do not explain the difference (Supplementary Figure 5). These algorithm-defined measurements recover the treatment response but do not establish equivalent anatomical branching.

### Figure 4. Three independent agents recover both neurite outgrowth responses

![Drug responses from three independent blind agents, followed by separate public and laboratory neurite tracing demonstrations.](figures/slas/submission_neurite_results.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A–B)** Mean neurite outgrowth per cell after treatment with fusicoccin-A (FC-A) or Y27632. Three independent blind agents and MetaXpress analysed the same 180 fields from 20 wells; analyses 1–3 identify independent methods, not biological replicates. Well values are unweighted means of nine fields. Each drug curve is normalized to the mean of its two zero-dose DMSO wells; 1 denotes no change from vehicle. Dots are two technical wells per dose for each method; whiskers show sample SD among those wells, excluding uncertainty in the control mean. All three analyses recover increased outgrowth for both drugs, with smaller response magnitudes than MetaXpress. **(C–E)** Neurite tracing in a public image, comparing the raw field, initial OpenHCS analysis and published NeuronCyto II algorithm output [@NeuronCytoII] (CC BY-NC 4.0) at the same field scale. The published output, including its red circles and arrow, is an algorithm comparison, not manual ground truth. **(F–H)** A laboratory field shown as a raw image, detected cell bodies and neurites, and an overlay on the raw image. This separate nine-field autonomous analysis is not one of the three drug-response analyses in A–B. Scale bars in C, D and F–H are in image pixels. Supplementary Figure 5 shows additional measurements and the scientist-assisted comparison.
:::

#### Three agents reach similar pooled nuclear accuracy

Independent agents may choose different pipelines for the same task; the practical question is whether they reach comparable accuracy. Nuclear detection analyses 2–4 reached pooled F1 of 0.906 to 0.910 on the 175 BBBC039 fields that none of their agents opened (Figure 5B). F1 balances finding reference nuclei against avoiding false detections, with 1 indicating a perfect match. Across all 200 fields, including those the agents inspected, F1 was 0.898 to 0.906.

On the dataset's official 50-image test partition (5,720 nuclei), the agents' per-image mean F1 at IoU 0.5 was 0.898 to 0.903. Caicedo et al. used this dataset to evaluate learned and CellProfiler segmentation methods [@Caicedo2019]. Our agents received no reference labels while building their pipelines.

For each agent, 117 to 121 of the 175 uninspected fields reached F1 of at least 0.90. Most errors were missed nuclei, and all three agents scored below 0.80 on the same six fields. Similar pooled accuracy therefore did not remove the need to inspect individual images. Supplementary Figure 3 and Data 8 give per-field agreement, error counts and a three-field repair that improved recovery but increased splitting. The earlier nuclear detection analysis 1 reached F1 0.746 and Dice area overlap 0.935 on 50 prospectively held-out fields (Supplementary Data 7).

#### An agent-developed translocation analysis separates assay controls

For a screening assay, an analysis must separate biological controls, not merely produce plausible segmentations. Protein translocation analysis 2 analysed all 96 BBBC013 wells and obtained Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 5E). Z′ measures control separation relative to variation between wells; higher values mean clearer separation. Both exceed 0.5, the conventional threshold for an excellent screening assay [@Zhang1999]. The agent chose its own readout: each well's median log2 ratio of nuclear to cytoplasmic GFP across eligible cells. Cytoplasm could be measured around 14,631 of 17,320 nuclei (84.5%); this fraction varied with treatment (Supplementary Figure 2). Four wells contributed to each treatment group. Protein translocation analysis 1 obtained Z′ of 0.554 for LY294002 and 0.751 for Wortmannin on 92 held-out wells (Supplementary Data 7). The two analyses used different well summaries and evaluation sets, so these scores are not a controlled before-and-after comparison.

### Image review identifies repairs and remaining errors

Agents used image inspection to locate and correct split and merged detections. Bright-object detection analysis 1 (H001) increased F1 against computational reference labels from 0.929 to 0.944 on one development image (Figures 3B and 5A). On 16 BBBC007 DNA/actin fields, cell-boundary analyses 2 and 3 placed 0.743 and 0.740 of their predicted borders between touching cells within two pixels of a manual outline (Figure 5C). Figure 5F shows a local correction of merged nuclear detections; Figure 5G shows improved retinal cell-body outlines while neighbouring cells remain separate.

Three-dimensional images require checking object positions across image planes. Nuclear localisation analysis 1 (H002) recovered all 15 manually annotated centres within 30 voxels (Figure 5D,I). Eleven predictions had no matching annotation; because the reference covers only some centres, those predictions do not establish a false-detection rate. A separate agent corrected a continuous body divided between multiple detections in a 3D image (Figure 5H).

For datasets without exhaustive spatial annotations, we compared analysis results with the same raw-image regions. These examples include retinal cell bodies (Supplementary Figure 4), a public NeuronCyto II field and nine laboratory neurite fields (Figure 4C–H). The comparisons show recovered structures and remaining errors; unresolved neurite crossings limit per-neuron path assignment. Figure 4C–E shows the public field's initial prediction. The final revision extended beyond principal shafts, and the shaft-only target was clarified after the run. These demonstrations involved one or two agents per task; Supplementary Data 8 gives their methods and reference definitions.

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

### Established CellProfiler workflows retain their measurements

Reusing an established analysis on a newer software stack requires preserving its measurements, not merely importing its settings. All 30 imported workflows reproduced native CellProfiler 4.2.8.1 outputs: exported label images matched native pixels and identifiers exactly, and numerical measurements met absolute and relative tolerances of 1e-6. OpenHCS produced these results with Python 3.12 and NumPy 2; native CellProfiler 4.2.8.1 ran with Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0. The tested workflows therefore retained their outputs without retaining CellProfiler's older runtime and dependency versions. The comparison included 21 workflows with comma-separated values (CSV) tables, three with SQLite databases and six with image or array outputs only. Five workflows received added exports comprising five label images and three numerical images (Supplementary Data 1).

The workflows covered DNA damage, human and Drosophila morphology, tumor morphology, Cell Painting, protein translocation, wound healing, tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening and *C. elegans* phenotyping. Seven workflows had image comparisons, including the translocation overlay alongside SQLite measurements. Advanced segmentation and 3D monolayer imports were reloaded as editable Python with their named structures, measurements and processing sequences (Supplementary Data 5). Output equivalence thus extended across complete preprocessing, segmentation, measurement and export workflows, including multi-stage 3D analysis.

Of 85 processing modules, 54 were tested in the 30 complete workflows, and another 29 had tests of their individual behavior (Figure 6A). For the remaining two, tests covered shared components rather than each module's own algorithm. These levels distinguish testing a complete analysis, testing an individual module and testing only the supporting code it uses.

### Faster execution supports iteration and larger experiments

Revising an analysis requires rerunning it, and larger experiments repeat that work across many fields. We therefore measured execution with output export included, checking that faster processing preserved the results.

Every one of the 30 workflows was faster than CellProfiler on one core, both for processing alone and with pipeline setup included (Figure 6B). When CellProfiler's internal initialization was spread over a measured eight-sample serial batch, the median per-sample processing speedup across workflows was [pending]{.benchmark-claim key=amortized_execution_median}-fold, with a minimum of [pending]{.benchmark-claim key=amortized_execution_min}-fold. This comparison divides each application's time by the number of samples: eight for CellProfiler and twelve for OpenHCS, using one worker. Including pipeline setup, speedup was a median [pending]{.benchmark-claim key=amortized_total_median}-fold, with minimum [pending]{.benchmark-claim key=amortized_total_min}-fold. The largest processing gain, [pending]{.benchmark-claim key=amortized_execution_max}-fold, came from an illumination-correction workflow whose large median filter took CellProfiler about 950 s per sample at both first and repeated use. Outputs matched during warmup and every measured repetition. Supplementary Data 3 gives the single-sample summaries and individual workflow timings.

The measured eight-sample comparison also favoured OpenHCS for every workflow, both for processing alone and with pipeline setup included, using two workers against one serial CellProfiler process. Every workflow remained faster in the twelve- and sixteen-sample comparisons, which use estimated CellProfiler times. These comparisons use different worker counts; Supplementary Data 3 gives total times and checks of the estimates.

Figure 6C compares both applications with the same number of cores and samples per core. OpenHCS times were measured; CellProfiler times were estimated from its measured initialization cost and processing time per sample. The estimate divides samples evenly among independent CellProfiler processes, each paying its own initialization cost, and assumes that running them together adds no delay. The timing formula was checked against serial batches; the matching multicore CellProfiler runs have not yet been measured (Supplementary Data 3).

On the same twelve-sample workload, every workflow ran faster with two, three and four workers than with one, both for processing alone and with setup included (Supplementary Figure 6; Supplementary Data 3). All these OpenHCS times were measured. Batches repeat copies of the same image sample to measure processing speed, not biological variation.

### Figure 6. CellProfiler compatibility and execution speed

![Graded module coverage, measured one-worker comparisons and matched-core CellProfiler projections, with all thirty workflows shown as points.](figures/slas/submission_benchmark_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
Imported CellProfiler workflows were checked for output agreement before their execution times were compared. **(A)** Strongest test per module; zero-count categories have no slice. Shared-code tests do not test each module's own algorithm. **(B)** Measured one-worker comparisons: one sample each, then per-sample time for batches of eight (CellProfiler) or twelve (OpenHCS). **(C)** Matching cores and samples: measured OpenHCS versus estimated CellProfiler. Estimates assume independent single-threaded processes, each with initialization, evenly divided work and no parallel slowdown. Some per-process batch sizes fall below the validated range (Supplementary Data 3). **(B, C)** Speedup is CellProfiler time divided by OpenHCS time; values above 1 mean faster OpenHCS execution. Each dot is one of 30 workflows; translucent bars are arithmetic means and black lines medians. Numbers below each distribution give its median. Logarithmic axes; red dashed line is equal speed, guides are 2×, 4× and 10×. OpenHCS times are medians of three runs after warmup. Setup includes compilation; both CellProfiler timing measures include initialization. External startup, OpenHCS library loading and warmup are excluded. Repeated samples measure processing, not biological variation.
:::

## Discussion

OpenHCS automates analysis development and execution while leaving laboratories with methods they can inspect, change and reuse. A scientist can change an agent-developed method through graphical controls or Python and rerun it; a laboratory function gains parameter controls and agent access from its definition. Agents debug and refine methods within this same system. Their repairs become part of the delivered analysis, available for correction, extension and reuse as the experiment changes.

The neurite analyses agreed with MetaXpress on the direction of both drug responses while giving smaller effect sizes. This supports using the delivered methods to detect these responses, with measurement definitions kept explicit when comparing their magnitudes. Nuclear detection showed a similar distinction between aggregate agreement and individual images: pooled scores were close, but the agents shared difficult fields with missed nuclei. Image inspection lets scientists connect each measurement to the detections that produced it and decide where further refinement is needed.

All 30 CellProfiler 4.2.8.1 workflows retained their measurements on OpenHCS with Python 3.12 and NumPy 2: exported labels matched exactly, and numerical measurements met the stated tolerances. Laboratories can reuse these workflows alongside custom CPU, GPU and deep-learning functions without keeping the entire analysis tied to CellProfiler's older environment. This preserves established analyses while allowing scientists to incorporate new methods from the wider Python ecosystem through custom functions. The analysis can therefore grow as biological questions and available methods evolve, rather than remain limited to the methods supplied with OpenHCS. Supplementary Data 1–2 specify the verified modules, settings and outputs.

Shorter runs make it more practical to inspect a result, revise the method and check it again across an experiment. Even after CellProfiler initialization was spread across eight samples, OpenHCS achieved a median [pending]{.benchmark-claim key=amortized_execution_median}-fold per-sample speedup across workflows with one worker. The advantage persisted with OpenHCS pipeline setup included, and additional workers processed the same workload faster. Thus the measured speed advantage does not depend on assigning OpenHCS more cores. It reduces the processing cost of rerunning an analysis, whether the next revision comes from a scientist or an agent.

The software's reusable components also make it useful beyond microscopy. The eight libraries in Supplementary Table 1 handle graphical controls, edit history, Python editing, storage and communication between processes without depending on biological methods. Pipelines organize data by dimensions and processing groups rather than requiring microscope-specific fields; source tests include remote-sensing and telemetry examples. Work is underway to release the pipeline preparation and execution code separately as ArrayPipe [@ArrayPipe]. This would let other data-science and machine-learning applications combine array libraries, run processing steps in parallel and inspect intermediate results.

The trials evaluate complete agent-developed analyses, combining the model, written guide and OpenHCS runtime. The treatment-assay cohort held these components fixed; the broader trial series varied model and guide versions as recorded in Methods. This design supports comparison of the delivered analyses, while controlled component studies would be needed to attribute reliability to any one part. The nuclear uninspected subset was identified retrospectively, and independent agents analysed the same experimental material rather than adding biological replicates.

OpenHCS automates image analysis within laboratory workflows, producing measurements that remain linked to inspectable methods. Systems using SiLA, a standard for laboratory automation, connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]. In either a conventional or automated laboratory, the aim is the same: delegate the technical work of developing an analysis while keeping the scientist able to judge, change and extend it.

## Supplementary Data

Supplementary figures provide additional assay results and image comparisons. Supplementary Data 1–3 contain CellProfiler output comparisons, module coverage and timing measurements; Data 4–6 contain NeuronCyto references, editable workflows and software checks; Data 7–8 contain agent instructions, final pipelines, evaluation partitions and individual analysis results.

## Code and Data Availability

OpenHCS source code: <https://github.com/OpenHCSDev/OpenHCS>.

OpenHCS documentation: <https://openhcs.readthedocs.io/>.

Supplementary files contain figure inputs and generation scripts, final pipelines, scores and benchmark measurements. Repository copies are available at <https://github.com/OpenHCSDev/openhcs/tree/main/paper/supplementary> and <https://github.com/OpenHCSDev/openhcs/tree/main/benchmark/results>.

The benchmark uses biological images and pipelines distributed by the CellProfiler project. Original sources:

- official CellProfiler example pipelines and images: <https://github.com/CellProfiler/examples> [@CellProfilerExamples]
- official CellProfiler tutorial pipelines and images: <https://github.com/CellProfiler/tutorials> [@CellProfilerTutorials]
- CellProfiler 4 benchmark supplement: <https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics> [@Stirling2021]

The [benchmark protocol](../benchmark/results/matched_worker_sweep_20261008_latestproduction/README.md) specifies the workloads, software versions, hardware and timing reports.

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
