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

Extracting a trustworthy measurement from microscopy images often requires assembling software as well as choosing an analysis method. OpenHCS connects task specification, method development, image inspection and execution in one editable workflow. Scientists can delegate development to AI agents, review detections against images and revise settings through graphical controls or Python. Technical users can add Python functions without building separate graphical or agent interfaces, combine processing libraries through automatic data conversions and reuse established CellProfiler workflows. Outputs retain their image and sample relationships. We evaluated this workflow through recorded interface edits, independently developed analyses and output-matched execution comparisons. Three blind agents recovered both drug-induced neurite outgrowth responses, with well-level measurements correlated with MetaXpress (Pearson r 0.963 to 0.996) but smaller response magnitudes. Three independent agents reached pooled nuclear detection F1 of 0.906 to 0.910 on 175 BBBC039 fields none had opened; F1 balances missed and false detections, with 1 best. All 30 imported CellProfiler 4.2.8.1 workflows preserved exported labels exactly and numerical measurements within absolute and relative tolerances of 1e-6. With CellProfiler's internal initialization spread over eight samples, median processing time per sample with one worker was [pending]{.benchmark-claim key=amortized_execution_median}-fold faster. OpenHCS provides an extensible foundation for agent-driven image analysis in which scientists can inspect and change methods while retaining established workflows.

## Introduction

Image analysis becomes a bottleneck when answering a biological question first requires assembling and debugging software. A biologist who wants to count cells or measure neurite growth must load the images and their associated information correctly, choose processing methods, install their dependencies and connect the tools. They must then check whether the measurements reflect the images. Finding an appropriate algorithm does not complete that work.

OpenHCS lets scientists delegate method development and debugging while keeping the resulting analysis available for inspection, revision and reuse (Figure 1A). Agents select processing methods, configure them, run them and examine outputs. Scientists review detections against images and edit settings through graphical controls or Python. A laboratory can add its own Python functions, whose definitions generate graphical controls and agent access (Figure 1B).

Established tools provide the foundations for this work. ImageJ/Fiji and napari support image inspection and processing [@Schneider2012; @Schindelin2012; @NapariPlugins]; CellProfiler organizes repeatable analysis workflows [@Carpenter2006; @McQuin2018]; OMERO manages images and their associated information [@Allan2012]; and Icy combines viewing, plugins and graphical workflows [@deChaumont2012]. Python bridges and generated controls let scientists extend these systems: PyImageJ connects ImageJ to Python, napari-imagej exposes ImageJ tools in napari, and magicgui turns Python functions into controls beside images [@Rueden2022PyImageJ; @NapariImageJ; @NapariMagicgui; @NapariWidgetWorkshop]. OpenHCS uses PyImageJ for its Fiji viewer and generates controls from processing-function definitions. Supplementary Table 2 compares extension routes and learning resources.

Connecting methods also requires preserving channel names, dimensions, pixel sizes and sample identities. Fiji–CellProfiler workflows exchange images and tables through scripts [@Dobson2021]; BioImageIT packages processing environments alongside image-data management [@Prigent2022]; CellProfiler plugins support Python integration and Docker execution [@Weisbart2024]; and MCMICRO connects tissue-imaging tools through containers and files [@Schapiro2022; @MCMICROImplementation]. Deep-learning methods, including Cellpose segmentation and N2V2 denoising, add further choices through Fiji and napari plugins [@Stringer2021Cellpose; @Hock2022N2V2; @FijiCellpose; @CellposeNapari; @NapariN2V]. These tools make methods available; choosing settings, connecting steps and checking the resulting measurements remain experiment-specific work.

AI assistants can take on this method-development work. BioImage.IO Chatbot connects community resources to analysis extensions, and Omega generates and runs Python and creates napari controls from natural-language requests [@Lei2024; @Royer2024]. Agentic-J uses bioimage knowledge, plugin instructions and specialized agents to develop and audit Fiji scripts. It also connects external tools through the Model Context Protocol (MCP), which lets agents call software operations [@Johanns2026]. BIABench compares agent analyses with reference answers and expert assessments; agents performed better on routine 2D tasks, while repeated runs were unreliable on more complex data [@Pan2026BIABench].

OpenHCS brings method authoring, execution and image inspection into the same system. Graphical controls, Python and agents edit one analysis (Figure 2). The system converts data between processing libraries, runs steps in parallel and keeps outputs linked to their samples and processing steps. Custom functions and imported CellProfiler workflows run together without Docker containers connecting the processing tools.

We evaluated whether scientists could delegate method development while retaining an analysis they could inspect and change, and whether the same system could support custom and established methods. Recorded edits demonstrate how graphical controls, Python and agents share pipeline settings. Independently developed neurite, nuclear-detection and translocation analyses test whether delegated methods produce useful measurements. Comparisons across 30 imported CellProfiler workflows test output preservation and execution time. These evaluations address different parts of the same task: obtaining a measurement, checking what it means and retaining a method that the laboratory can reuse or extend. Together, they test a shared foundation for agent-driven analysis, new Python methods and established workflows.

## Materials and Methods

### Pipeline model

OpenHCS combines processing functions into a pipeline and arranges their data connections before execution. Compilation determines which data each function receives, which conversions it needs and where its outputs go (Supplementary Figure 1). Steps run in their declared order and use shared defaults unless the user changes them for an individual step. Python function signatures supply parameter names, types and defaults for graphical controls and editable code; docstrings supply searchable descriptions. Each function specifies the CPU, GPU or deep-learning library it uses and whether it accepts image planes or volumes. ArrayBridge converts arrays and tensors across NumPy, CuPy, PyTorch, TensorFlow, JAX and pyclesperanto (Supplementary Table 1). OpenHCS uses these function definitions to arrange conversions automatically, so custom functions from different libraries can run in the same pipeline without user-written conversion steps.

Scientists can move between graphical controls, Python and agent editing while working on the same functions and settings. ObjectState stores those settings and their edit history; Pycodify converts the pipeline to editable Python and reads changes back into the same analysis.

Scientists and agents extend an analysis by registering Python functions with these same declarations, including preprocessing and deep-learning methods. Illumination correction calls BaSiCPy through the OpenHCS-maintained fork, and N2V2 denoising runs in PyTorch with CUDA. These methods join the same editable pipeline without separate graphical forms, agent tools or hand-written array conversions.

Input selections specify which channels, planes or stacks each step reads and how images are divided into processing groups. Later steps inherit or replace these choices. Sample, site, channel, plane and time coordinates link results to images through stacking and processing. Microscope handlers interpret acquisition layouts and metadata. Bio-Formats reads image planes from microscopy containers; OME-Zarr supplies arrays, axes, channels and pixel scales; experimental OMERO support supplies managed images. Users can assign channel and image roles explicitly when acquisition metadata are insufficient. Supplementary Table 1 lists the eight reusable libraries behind the runtime.

### Figure 1. Scientists can inspect and edit the agent's analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** OpenHCS window with ExampleHuman and ExampleFly folders and the nine-step ExampleHuman analysis. Blue boxes show where to select a plate, edit analysis steps and settings, and check execution status.
:::

### Execution and viewers

Measurements and detected objects need to remain traceable to their images and processing steps. Function contracts specify the images, labels, measurements, object relationships and files each step produces; compilation connects later steps to those sources. Results retain their source coordinates, processing group and producing step when saved or delivered to napari or Fiji. Saving and viewer delivery can be configured independently.

The execution server uses ZeroMQ, a messaging library, to coordinate requests and workers. Each worker reuses loaded libraries and initialized array backends while processing its assigned samples, then releases its resources when the run finishes. Workers use processes by default, with threads available as a configuration option. Storage routes include local files, in-memory data, Zarr and OMERO.

The streaming service checks viewer readiness and waits for display updates. Viewer sessions remain open for inspection after execution, and agents can query napari layers and regions of interest.

### Figure 1, continued. The laboratory's own Python joins the shared analysis

![Real Python declaration and docstring, generated controls, live editable Python and agent-facing parameter descriptions.](figures/slas/submission_custom_function.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(B)** Scientists can extend an analysis with laboratory-specific Python functions without building a separate interface. The function's definition and documentation supply graphical controls and agent-tool descriptions. Form and code views show gain 1.2 and offset 0.0.
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
Forms, Python and MCP edit one workflow, including imported CellProfiler pipelines. The ZeroMQ execution server compiles the pipeline and coordinates workers. Workers read images, save outputs and stream results to napari or Fiji; progress returns to the editor. Supplementary Figure 1 shows runtime preparation.
:::

### Autonomous analysis design

We distinguish independently developed methods by numbering analyses within each biological task: nuclear detection analyses 1–4 use BBBC039, cell-boundary analyses 1–3 use BBBC007, and protein translocation analyses 1–2 use BBBC013. Numbers identify independently developed methods, not successive repairs or quality rankings. Supplementary Data 8 links these names to the original run records.

Each analysis used a fresh agent, which received a biological task brief, acquisition information and MCP access. Nuclear detection 1, cell-boundary 1 and protein translocation 1 used gpt-5.6-sol; no OpenHCS instruction-guide version was recorded for those analyses. The gpt-6.1-sol analyses also supplied the packaged OpenHCS skill, a written guide to using OpenHCS. Briefs could include channel hints, requested outputs and review instructions; the retinal task, for example, requested RBPMS-positive soma labels, measurements and a count. Supplementary Data 8 summarizes the original briefs and records the instruction versions: nuclear detection analyses 2–4 each used a different revision, while the three drug-response analyses used the same revision.

The skill instructs agents to inspect channels and representative regions, measure feature sizes, read function documentation, build and run a pipeline, and compare the same region as a raw image, an analysis result and an overlay of both. Agents correct the earliest step causing an error, then check that the change fixes the problem without breaking previously successful examples. Figure 3A shows this procedure; individual trial records show how agents followed it. Earlier trials used OpenHCS 0.8.5; later trials used 0.8.7.

### Figure 3. Delegated specialist work leaves an analysis the scientist can inspect

![Skill-directed workflow with Fiji and napari inspection, followed by the recorded H001 decisions and matched raw/repair images.](figures/slas/submission_autonomous_loop.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Instructions supplied to the agent: read the biological task, inspect images, run the analysis, compare results with raw images, correct errors and deliver the analysis. **(B)** Bright-object detection analysis 1 (H001) across four runs, with the same region shown before analysis and with the first and final results. The elongated object is initially split into separate detections; the final analysis detects it as one object. Colours distinguish detected objects within each view. Times include inspection, repair, reporting and cleanup.
:::

Agents finalized their pipelines before any comparison with reference data, and no pipeline changed after scoring began. They received no reference labels, accepted settings or score feedback while building their analyses. First-versus-final comparisons use the first completed prediction and the final settings on the same inputs. Self-directed repairs are autonomous; revisions prompted by a scientist are assisted. The earlier gpt-5.6-sol trials withheld evaluation images and treatment metadata until after finalization and changed only input and output folders for evaluation. The later gpt-6.1-sol trials gave agents development images and compared results with task-specific references after the agents finished.

For the laboratory treatment assay, three new gpt-6.1-sol agents independently analysed the same 20 coded wells, each containing nine fields. Each field contained paired 1024-by-1024-pixel images of DAPI nuclear stain and FITC neuronal signal, at one Z position and one timepoint. The recorded XY spacing was 1.3556 µm per pixel. All received the same biological brief, acquisition information, MCP access and fixed version of the packaged skill using the same OpenHCS 0.8.7 installation. They chose six, four and eight development fields and, after fixing their methods, reviewed 20, eight and twelve further fields. Each analysed all 180 fields, and its final outputs were fixed before the evaluator opened treatment identities, MetaXpress measurements or assisted results. Supplementary Figure 5 reports the individual agents.

For nuclear detection analyses 2–4, image-delivery records identified 25 of the 200 fields as opened by at least one agent. The remaining 175 fields, which none of the three agents opened, form the uninspected subset used for retrospective evaluation. This retrospectively identified subset is reported separately from the images withheld in nuclear detection analysis 1. Supplementary Data 7–8 provide final pipelines, data partitions, scores, model and software versions, task times and computational usage.

### Endpoints and references

**Nuclear detection (BBBC039).** Nuclear detection analysis 1 used four development fields and 50 held-out fields, meaning images withheld until the method was finalized. Analyses 2–4 were evaluated on all 200 annotated fields and separately on the 175 fields none of their agents had inspected. Each detected nucleus could match at most one reference nucleus. A match required intersection over union (IoU) ≥ 0.5: the overlapping area had to be at least half the total area covered by the two outlines together.

**How to read detection scores.** Precision is the fraction of detections that match real objects; recall is the fraction of reference objects found. F1 combines these two fractions using their harmonic mean, so both must be high for a high score. F1 ranges from 0 to 1, with 1 indicating no missed or false detections under the matching rule; an F1 of 0.90 is not simply “90% of cells counted correctly.” Pooled F1 combines object counts across fields before calculating the score, whereas mean per-image F1 gives each image equal weight. Dice measures overlap of the detected and reference areas, from 0 (no overlap) to 1 (identical areas); a high Dice score can still accompany incorrect splitting or merging of cells. Signed count error is the detected count minus the reference count: positive values indicate overcounting and negative values undercounting. Split and merge checks identify one real object detected as several, or several detected as one.

**Cell boundaries (BBBC007).** Cell-boundary analysis 1 used four development and 12 held-out DNA/actin fields. Analyses 2–3 were evaluated on all 16 fields. The directed boundary fraction is the proportion of predicted border pixels between touching cells that lie within two pixels of a manual outline. Higher values mean that more of the predicted borders follow the manual outlines; this does not measure whether every manual border was found.

**Protein translocation (BBBC013).** Protein translocation analysis 1 used four development and 92 held-out wells. It measured mean GFP intensity in each cell's nucleus divided by mean GFP intensity in its cytoplasm, then averaged those ratios within each well. Protein translocation analysis 2 used each well's median log2 nuclear-to-cytoplasmic GFP ratio across cells with measurable cytoplasm. On this log2 scale, 0 means equal nuclear and cytoplasmic intensity, and 1 means twice the intensity in the nucleus. Analysis 2 was evaluated on all 96 wells, including four development wells.

Z′ (Z-prime) measures how clearly an assay separates positive and negative controls, accounting for variation between wells. Higher is better: 1 is ideal separation with no within-group variation, values above 0.5 conventionally indicate an excellent screening assay, and zero or negative values indicate poor separation relative to the variation. It is not a percentage of correctly analysed cells. We calculated Z′ as 1 minus three times the sum of the two control groups' sample standard deviations, divided by the absolute difference between their means. Each drug used four positive and four negative control wells. Standard deviation (SD) describes variation among wells, not uncertainty across independent agents.

**Bright-object detection (H001).** First and final detections were matched one-to-one to computational reference labels from a notebook-derived image.

**3D nuclear localisation (H002).** Predicted centres were matched one-to-one to manually marked centres within a predeclared 30-voxel radius. A voxel is a three-dimensional image pixel; lower centre-to-centre distances indicate more accurate localisation.

**Retina.** RBPMS-positive soma detection was reviewed in matched raw, label and combined views across several regions.

**Neurites.** Principal shafts in the public field and soma/path recovery in nine laboratory fields were inspected with matched raw and result views. The public comparison used the published NeuronCyto II image and algorithm output [@NeuronCytoII]. Three later independent laboratory analyses were compared with MetaXpress well exports and the retained scientist-assisted analysis. Each endpoint was the unweighted mean of nine field-level values; each drug curve used its own two zero-dose DMSO wells. Overlapping fields were not deduplicated. The comparison tests recovery of treatment effects, not manual tracing accuracy or identical branch definitions. The earlier method-directed demonstration and assisted transfer remain in the supplement.

For drug responses, fold change is the measurement divided by its DMSO control mean: 1 means no change, 2 means double and 0.5 means half. Pearson's correlation coefficient, r, describes whether two methods' measurements rise and fall together across wells. It ranges from −1 to 1; values near 1 indicate a strong positive linear relationship, but do not mean that the methods give identical values or effect sizes.

### Performance measurement

To compare execution with equal parallel resources, the matched single-sample benchmark used one physical CPU core, one worker and one numerical thread. OpenHCS ran with Python 3.12 and native CellProfiler 4.2.8.1 with Python 3.9. That CellProfiler release requires SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]; the comparison tests whether its workflows retain their outputs on OpenHCS's newer scientific Python environment. Each workflow used one selected source well or sample, with unchanged processing settings and the declared comparison outputs. OpenHCS used a warmup followed by three measured repetitions. The native baseline was one complete first-use-inclusive serial CellProfiler batch; its natural internal initialization remained included. Source revisions, workloads, hardware and environments accompany the matched benchmark in Supplementary Data 1 and 3.

**What was timed.** CellProfiler processing time included its internal initialization, preparation of image groups, processing and final output steps. OpenHCS processing time included the server's work through saving results and plate-level exports. Neither measurement included starting the applications or server; loading OpenHCS libraries, warmup and checking output agreement were also excluded. We additionally measured setup plus processing: preparing and calling the CellProfiler pipeline, or compiling the OpenHCS pipeline, submitting it and waiting for completion. Speedup was CellProfiler's first-batch time divided by the median of three OpenHCS times. We report the median speedup across workflows.

**Batch comparisons.** Batches repeated the same selected source sample. To compare time per sample, we divided CellProfiler's measured eight-sample batch time by eight and the median of three single-worker, twelve-sample OpenHCS times by twelve. This spreads the initial setup cost over the batch. The CellProfiler batch used one numerical thread with four permitted CPUs; its single-sample comparison used one CPU. We estimated twelve- and sixteen-sample CellProfiler times from the measured eight-sample batch and repeated runs after initialization. Supplementary Data 3 gives the timing definitions, estimation formula and checks against measurements for three workflows. Combined memory use across the application and its workers was not measured.

**Parallel processing.** OpenHCS worker counts were compared on the same twelve-sample workload using measured processing and setup-plus-processing times throughout.

## Results

### Scientists can inspect, revise and extend the analysis behind a measurement

Delegating method development leaves a scientist with an analysis to check and reuse, not only a table of numbers. Scientists can adjust image normalization in the graphical interface and continue editing the same settings in Python. In the recorded demonstration, an agent changed the upper percentile used for normalization from 99.8 to 99.6, and the graphical form showed 99.6. Changing the setting back to 99.8 also updated the generated Python. These edits changed the same pipeline settings through each interface (Supplementary material, Figure assembly and interface records). Figure 1B shows how adding a custom Python function also makes its settings available in the graphical controls and to agents, without writing a separate interface.

### Agent-developed methods produce useful assay measurements

An editable workflow is useful only if its measurements address the experiment. We therefore tested whether agent-developed analyses recovered laboratory drug responses, detected annotated nuclei and separated assay controls without access to reference answers during method development (Table 1).

Table 1. Main results from the three neurite drug-response analyses, nuclear detection analyses 2–4 and protein translocation analysis 2, all using gpt-6.1-sol. Agent counts refer to independent agents within each assay. Agents could inspect development images while building their pipelines; the nuclear fields that none of them opened were identified afterwards. Supplementary Data 7–8 give individual results, including nuclear detection 1, cell-boundary 1 and protein translocation 1 on held-out images.

| Assay | Agents | Evaluation inputs | Endpoint | Result |
|---|---|---|---|---|
| Laboratory neurite drug assay | 3 | 180 fields in 20 wells per agent | Control-normalized outgrowth responses | Both positive responses recovered by all three; magnitudes varied |
| Nuclear detection 2–4 (BBBC039) | 3 | 175 fields that none of the agents opened | Pooled detection F1 | 0.906 to 0.910 |
| Protein translocation 2 (BBBC013) | 1 | 96 wells including four development wells | Control separation, Z′: LY294002; Wortmannin | 0.849; 0.726 |

#### Three blind agents recover drug responses in a laboratory neurite assay

We tested whether independently authored analyses recovered drug responses in laboratory data without access to treatment identities or commercial measurements. Three agents independently analysed the same coded 20-well neurite outgrowth experiment. All three found increased mean outgrowth per cell and total outgrowth at every tested dose of FC-A and Y27632 (Figure 4A–B). Across the 20 wells, each agent's mean outgrowth per cell correlated closely with MetaXpress (Pearson r 0.963 to 0.996). The biological responses were recovered, but their measured magnitudes differed: at 40 µM, fold changes in mean outgrowth per cell were 1.32 to 1.65 for FC-A and 1.49 to 1.69 for Y27632, against 1.98 and 2.05 for MetaXpress. Two agents were close to the scientist-assisted analysis, which gave 1.77 and 1.76; the third gave weaker responses. Cell-count fold changes were 0.94 to 0.99 for FC-A and 0.92 to 0.94 for Y27632, against 0.95 and 0.91 for MetaXpress.

Branches per cell also increased at every tested dose, and well-level values correlated with MetaXpress (r 0.875 to 0.990). Fold changes at 40 µM were smaller: 1.24 to 1.63 for FC-A and 1.50 to 1.73 for Y27632, against 3.00 and 3.26 for MetaXpress. The agents' control wells started higher, at 2.1 to 5.3 branches per cell, against 1.3 to 1.5 for MetaXpress. For drug-response analysis 3, the absolute increases from zero dose to 40 µM were 2.44 and 2.65 branches per cell for FC-A and Y27632, compared with MetaXpress's 2.94 and 2.90. Its higher baselines compressed the fold changes; the cause of the baseline differences was not established. Smaller branching responses also appeared in the assisted analysis and persisted in total branches and branches per primary process (Supplementary Figure 5), so cell-count denominators do not explain the difference. These algorithm-defined measurements capture the biological response but do not establish equivalent anatomical branching.

#### Three agents reach similar pooled nuclear accuracy

Independent agents may choose different pipelines for the same task; the practical question is whether they reach comparable accuracy. Nuclear detection analyses 2–4 reached pooled F1 of 0.906 to 0.910 on the 175 BBBC039 fields that none of their agents opened (Figure 5B). F1 balances finding reference nuclei against avoiding false detections, with 1 indicating a perfect match. Across all 200 fields, including those the agents inspected, F1 was 0.898 to 0.906. Despite choosing different settings, the agents' pooled scores on the uninspected fields differed by at most 0.004.

On the dataset's official 50-image test partition (5,720 nuclei), the agents' per-image mean F1 at IoU 0.5 was 0.898 to 0.903. Caicedo et al. used this dataset to evaluate learned and CellProfiler segmentation methods [@Caicedo2019]. Our agents received no reference labels while building their pipelines.

For each agent, 117 to 121 of the 175 uninspected fields reached F1 of at least 0.90. Missed nuclei made up most errors, and the same six fields scored below 0.80 for all three agents. Supplementary Data 8 provides the per-field scores and error counts. Between analyses 2 and 3 on all 200 fields, per-field F1 mostly differed by less than 0.03 (Supplementary Figure 3). The earlier nuclear detection analysis 1 reached F1 0.746 and Dice area overlap 0.935 on 50 prospectively held-out fields (Supplementary Data 7).

#### An agent-developed translocation analysis separates assay controls

For a screening assay, an analysis must separate biological controls, not merely produce plausible segmentations. Protein translocation analysis 2 analysed all 96 BBBC013 wells and obtained Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 5E). Z′ measures control separation relative to variation between wells; higher values mean clearer separation. Both exceed 0.5, the conventional threshold for an excellent screening assay [@Zhang1999]. The agent chose its own readout: each well's median log2 ratio of nuclear to cytoplasmic GFP across eligible cells. Cytoplasm could be measured around 14,631 of 17,320 nuclei (84.5%); this fraction varied with treatment (Supplementary Figure 2). Four wells contributed to each treatment group. Protein translocation analysis 1 obtained Z′ of 0.554 for LY294002 and 0.751 for Wortmannin on 92 held-out wells (Supplementary Data 7). The two analyses used different well summaries and evaluation sets, so these scores are not a controlled before-and-after comparison.

### Image review identifies repairs and remaining errors

A numerical score does not show where an analysis makes mistakes. Agents inspected the images and corrected split and merged detections. Bright-object detection analysis 1 (H001) increased F1 against computational reference labels from 0.929 to 0.944 on one development image (Figures 3B and 5A). On 16 BBBC007 DNA/actin fields, cell-boundary analyses 2 and 3 placed 0.743 and 0.740 of their predicted borders between touching cells within two pixels of a manual outline (Figure 5C). Figure 5F shows a local correction of merged cell detections; Figure 5G shows improved retinal cell-body outlines while neighbouring cells remain separate.

Three-dimensional images require checking object positions across image planes. Nuclear localisation analysis 1 (H002) recovered all 15 manually annotated centres within 30 voxels (Figure 5D,I). Eleven predictions had no matching annotation; because the reference covers only some centres, those predictions do not establish a false-detection rate. A separate agent corrected a cell body split into two detections in a 3D image (Figure 5H).

For datasets without exhaustive spatial annotations, we compared analysis results with the same raw-image regions. These examples include retinal cell bodies (Supplementary Figure 4), a public NeuronCyto II field and nine laboratory neurite fields (Figure 4C–H). The comparisons show recovered structures and remaining errors; unresolved neurite crossings limit per-neuron path assignment. Figure 4C–E shows the public field's initial prediction. The final revision extended beyond principal shafts, and the shaft-only target was clarified after the run. These demonstrations involved one or two agents per task; Supplementary Data 8 gives their methods and reference definitions.

### Figure 4. Three independent agents recover both neurite outgrowth responses

![Drug responses from three independent blind agents, followed by separate public and laboratory neurite tracing demonstrations.](figures/slas/submission_neurite_results.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A–B)** Drug responses from three independent blind agents and MetaXpress across 20 wells, relative to each drug curve's own DMSO mean. Analyses 1–3 identify the three agent-developed methods. Dots are two technical wells per dose for each analysis or method; whiskers show sample SD among those wells. All three analyses recover increased outgrowth for both drugs, with smaller response magnitudes than MetaXpress. **(C–E)** Raw public image, initial OpenHCS analysis and published NeuronCyto II algorithm output [@NeuronCytoII] (CC BY-NC 4.0), displayed at the same field scale. The published output is an algorithm comparison, not manual ground truth. **(F–H)** A laboratory field shown as a raw image, detected cell bodies and neurites, and an overlay on the raw image. This separate nine-field autonomous analysis is not one of the three drug-response analyses in A–B. Supplementary Figure 5 shows additional measurements and the scientist-assisted comparison.
:::

### Figure 5. Analysis accuracy and visible corrections

![Task-specific nuclear, boundary, volume and translocation endpoints alongside an independent DNA/actin merge repair.](figures/slas/submission_analysis_summary.png){width=6in}

::: {custom-style="ImageCaption"}
**(A)** Bright-object analysis 1, before and after repair on one image; computational-reference F1 (1 is best).
**(B)** Nuclear analyses 2–4: all 200 fields and the 175 none of the agents opened.
**(C)** Cell-boundary analyses 2–3: predicted borders within two pixels of manual outlines. Dots are fields; lines pool border pixels.
**(D)** Mean error among matched 3D centres; labels count matches out of 15 annotations. Dashed line: predeclared 30-voxel (3D pixel) matching limit. Annotations are incomplete.
**(E)** Translocation analysis 2: means ± SD of four well medians per dose, with shared vertical limits. Each well's median cell-level log2(nuclear/cytoplasmic GFP) increases with relative nuclear GFP. Z′ measures control separation (four wells/type; >0.5 is excellent). The 96 wells include four development wells.
**(F)** Same BBBC007 region, raw and before/after correcting merged cells. Colours identify cells within each view.
:::

### Figure 5, continued. Correcting cell detection in two and three dimensions

![Matched retinal and volumetric body repairs, with separate finalized three-dimensional localisation evidence.](figures/slas/submission_quantitative_results.png){width=6in}

::: {custom-style="ImageCaption"}
**(G)** Retinal raw image, first analysis and final analysis, showing fragmented cell-body detections and a neighbouring pair of cells.
**(H)** Correction of a cell body split into two detections at Z=36 in a 3D image.
**(I)** 3D nuclear localisation analysis 1 (H002): XY labels, XZ/YZ outlines (yellow) and in-plane centres (magenta), with 15 matched manual centres and 11 unmatched predictions. Distances are voxels. Colours distinguish labels within each view.
:::

### Established CellProfiler workflows retain their measurements

Reusing an established analysis on a newer software stack requires preserving its measurements, not merely importing its settings. All 30 imported workflows reproduced native CellProfiler 4.2.8.1 outputs: exported label images matched native pixels and identifiers exactly, and numerical measurements met absolute and relative tolerances of 1e-6. OpenHCS produced these results with Python 3.12 and NumPy 2; native CellProfiler 4.2.8.1 ran with Python 3.9.25, NumPy 1.24.4 and SciPy 1.9.0. Its release pins SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]. The tested workflows therefore retained their outputs without retaining CellProfiler's older runtime and dependency versions. The comparison included 21 CSV profiles, three SQLite profiles and six image/array profiles. Five workflows received added exports comprising five label images and three numerical images (Supplementary Data 1).

The workflows covered DNA damage, human and Drosophila morphology, tumor morphology, Cell Painting, protein translocation, wound healing, tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening and *C. elegans* phenotyping. Seven workflows had image comparisons, including the translocation overlay alongside SQLite measurements. Advanced segmentation and 3D monolayer imports were reloaded as editable Python with their named structures, measurements and processing sequences (Supplementary Data 5). Output equivalence thus extended across complete preprocessing, segmentation, measurement and export workflows, including multi-stage 3D analysis.

Of 85 processing modules, 54 were tested in the 30 complete workflows, and another 29 had tests of their individual behavior (Figure 6A). For the remaining two, tests covered shared components rather than each module's own algorithm. These levels distinguish testing a complete analysis, testing an individual module and testing only the supporting code it uses.

### Faster execution supports iteration and larger experiments

Revising an analysis requires rerunning it, and larger experiments repeat that work across many fields. We therefore measured execution with output export included, checking that faster processing preserved the results.

Every one of the 30 workflows was faster than CellProfiler on one core, both for processing alone and with pipeline setup included (Figure 6B). When CellProfiler's internal initialization was spread over a measured eight-sample serial batch, OpenHCS processing per sample was a median [pending]{.benchmark-claim key=amortized_execution_median}-fold faster, with minimum [pending]{.benchmark-claim key=amortized_execution_min}-fold. This comparison divides each application's time by the number of samples: eight for CellProfiler and twelve for OpenHCS, using one worker. Including pipeline setup, speedup was a median [pending]{.benchmark-claim key=amortized_total_median}-fold, with minimum [pending]{.benchmark-claim key=amortized_total_min}-fold. The largest processing gain, [pending]{.benchmark-claim key=amortized_execution_max}-fold, came from an illumination-correction workflow whose large median filter took CellProfiler about 950 s per sample at both first and repeated use. Outputs matched during warmup and every measured repetition. Supplementary Data 3 gives the single-sample summaries and individual workflow timings.

The measured eight-sample comparison also favoured OpenHCS for every workflow, both for processing alone and with pipeline setup included, using two workers against one serial CellProfiler process. Every workflow remained faster in the twelve- and sixteen-sample comparisons, which use estimated CellProfiler times. These comparisons use different worker counts and are shown separately in Supplementary Figure 6; Supplementary Data 3 gives total times and checks of the estimates.

Figure 6C compares both applications with the same number of cores and samples per core. OpenHCS times were measured; CellProfiler times were estimated from its measured initialization cost and processing time per sample. The estimate divides samples evenly among independent CellProfiler processes, each paying its own initialization cost, and assumes that running them together adds no delay. The timing formula was checked against serial batches; the matching multicore CellProfiler runs have not yet been measured (Supplementary Data 3).

On the same twelve-sample workload, every workflow ran faster with two, three and four workers than with one, both for processing alone and with setup included (Supplementary Figure 6; Supplementary Data 3). All these OpenHCS times were measured. Batches repeat copies of the same image sample to measure processing speed, not biological variation.

### Figure 6. What was tested and how much faster it ran

![Graded module coverage, measured one-worker comparisons and matched-core CellProfiler projections, with all thirty workflows shown as points.](figures/slas/submission_benchmark_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Strongest test per module; zero-count categories have no slice. Shared-code tests do not test each module's own algorithm. **(B)** Measured one-worker times: one sample each, then per-sample time for batches of eight (CellProfiler) or twelve (OpenHCS). **(C)** Matching cores and samples: measured OpenHCS versus estimated CellProfiler. Estimates assume independent single-threaded processes, each with initialization, evenly divided work and no parallel slowdown. Some per-process batch sizes fall below the validated range (Supplementary Data 3). **(B, C)** Each dot is one of 30 workflows; translucent bars are arithmetic means and black lines medians. Numbers below each distribution give its median. Logarithmic axes; red dashed line is equal speed, guides are 2×, 4× and 10×. OpenHCS times are medians of three runs after warmup. Setup includes compilation; both CellProfiler timing measures include initialization. External startup, OpenHCS library loading and warmup are excluded. Repeated samples measure processing, not biological variation.
:::

## Discussion

OpenHCS connects method development, image inspection and execution so that delegated work leaves a laboratory with an analysis it can keep using. A scientist can change an agent-developed method through graphical controls or Python and rerun it; a laboratory function gains parameter controls and agent access from its definition. Agents debug and refine methods within this same system. Their repairs become part of the delivered analysis, available for correction, extension and reuse as the experiment changes.

The biological evaluations test whether this shared system produces useful measurements. Agents selected, configured and repaired processing steps from written task briefs. All three blind neurite analyses recovered both drug responses, independent nuclear analyses reached pooled F1 above 0.90 on fields none had inspected, and an agent-selected translocation readout separated positive and negative controls. These results demonstrate method development across several biological questions while leaving each resulting analysis open to inspection.

The neurite analyses agreed with MetaXpress on the direction of both drug responses while giving smaller effect sizes. This supports using the delivered methods to detect these responses, with measurement definitions kept explicit when comparing their magnitudes. Nuclear detection showed a similar distinction between aggregate agreement and individual images: pooled scores were close, but the agents shared difficult fields with missed nuclei. Image inspection lets scientists connect each measurement to the detections that produced it and decide where further refinement is needed.

The CellProfiler comparison demonstrates that established methods can move into this system without changing their measurements. OpenHCS reproduced all 30 CellProfiler 4.2.8.1 workflows on Python 3.12 and NumPy 2, preserving exact exported labels and numerical measurements within the stated tolerances. Laboratories can reuse these workflows alongside custom CPU, GPU and deep-learning functions without keeping the entire analysis tied to CellProfiler's older environment. This preserves established analyses while allowing scientists to incorporate new methods from the wider Python ecosystem through custom functions. The analysis can therefore grow as biological questions and available methods evolve, rather than remain limited to the methods supplied with OpenHCS. Supplementary Data 1–2 specify the verified modules, settings and outputs.

Faster execution supports both method revision and larger experiments. OpenHCS was faster in every tested workflow while preserving the compared outputs. Even after CellProfiler initialization was spread across eight samples, median processing time per sample with one worker was [pending]{.benchmark-claim key=amortized_execution_median}-fold faster. The advantage persisted with OpenHCS pipeline setup included, and additional workers processed the same workload faster. Thus the measured speed advantage does not depend on assigning OpenHCS more cores. It reduces the processing cost of rerunning an analysis, whether the next revision comes from a scientist or an agent.

The software's reusable components also make it useful beyond microscopy. The eight libraries in Supplementary Table 1 handle graphical controls, edit history, Python editing, storage and communication between processes without depending on biological methods. Pipelines organize data by dimensions and processing groups rather than requiring microscope-specific fields; source tests include remote-sensing and telemetry examples. Work is underway to release the pipeline preparation and execution code separately as ArrayPipe [@ArrayPipe]. This would let other data-science and machine-learning applications combine array libraries, run processing steps in parallel and inspect intermediate results.

The trials evaluate complete agent-developed analyses, combining the model, written guide and OpenHCS runtime. The treatment-assay cohort held these components fixed; the broader trial series varied model and guide versions as recorded in Methods. This design supports comparison of the delivered analyses, while controlled component studies would be needed to attribute reliability to any one part. The nuclear uninspected subset was identified retrospectively, and independent agents analysed the same experimental material rather than adding biological replicates.

The same design can supply image analysis for self-driving laboratories, where measurements inform the next experiment. Systems using SiLA, a standard for laboratory automation, connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]; OpenHCS supplies an image-analysis component whose measurements remain linked to an inspectable method. In either a conventional or automated laboratory, the aim is the same: delegate the technical work of developing an analysis while keeping the scientist able to judge, change and extend it.

## Supplementary Data

The supplement contains the comparison methods, reference definitions, trial records and linked source files.

1. **CellProfiler workflow comparison:** unified 30-workflow results, output inventories and five-workflow export definitions.
2. **CellProfiler coverage:** module-to-workflow associations, individual setting handling, and archived processing-registration coverage.
3. **Worker measurements:** execution timings by workflow, worker count and number of repeated samples.
4. **Recorded agent workflow:** earlier method-directed NeuronCyto demonstration, model and software versions, outputs and comparison references.
5. **Complex CellProfiler workflows:** source-derived step sequences, function-call counts and editable Python for advanced segmentation and 3D monolayer analysis.
6. **Workflow regression tests:** representative configuration, generated-Python and compiler-validation checks, with source and CI-job references.
7. **Prospective agent-authored assays:** final pipelines and held-out BBBC039, BBBC007 and BBBC013 scores.
8. **Agent-authored analyses and independent repair:** a downloadable 20-record results table, first/final comparisons, full-corpus nuclear evaluation, original brief summaries and trial measurements.

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
