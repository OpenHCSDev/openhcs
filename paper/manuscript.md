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

Bioimage analysis is essential for biological research, but setting up specialized tools and getting them to work together can impede discovery for researchers without the required technical expertise. OpenHCS provides one editable analysis shared by graphical controls, Python and agents. It connects the bioimaging ecosystem's existing software tools and platforms through a native Python layer, with multiprocessing and GPU support for standard machine-learning libraries. Scientists can round-trip analysis edits between graphical controls and Python. Measurements remain linked to their source images and samples, letting scientists inspect the detections behind a result in Fiji or napari. Laboratories can load compatible Python functions within the running application without a separate plugin package and reuse existing CellProfiler pipelines within OpenHCS's modern processing engine. All 30 tested CellProfiler pipelines retained their outputs and ran faster with both applications using one processor core; parallel OpenHCS execution further reduced times on the same twelve-sample workload. From a single written biological task prompt, independent AI agents used the same tools to build, run, inspect and correct analyses autonomously, recovering drug responses, detecting nuclei and distinguishing positive and negative assay controls. OpenHCS extends laboratory automation to building and running analyses that scientists inspect, change and reuse.

## Introduction

Drug screening and studies of cell and molecular biology need open-source tools that automate measurements from microscopy images. Different disease models and biological questions require measurements ranging from cell number and morphology to subcellular protein location and signal dynamics. Each assay therefore needs its own processing sequence and often substantial troubleshooting. First described in 2006, CellProfiler was developed with academic and industry support to organize image processing and measurement into reusable pipelines [@Carpenter2006; @McQuin2018]. Its pipeline model lets researchers assemble and tune a sequence of processing steps for their assay.

Microscope-integrated commercial software offers convenient analysis tools, but licensing costs, hardware dependence and closed source code can limit access and adaptation [@Carpenter2006; @McQuin2018]. Over the past two decades, an expanding open-source bioimaging ecosystem has given laboratories alternatives that they can inspect, adapt and share. ImageJ/Fiji offers image-processing tools, macros and community-developed plugins, while napari combines interactive multidimensional viewing with Python extensions [@Schneider2012; @Schindelin2012; @NapariPlugins]. OMERO supports storing, organizing and sharing images with their experimental information [@Allan2012], and Icy combines visualization, plugins and graphical workflows [@deChaumont2012]. Access to their source code lets laboratories examine and adapt these tools to their assays and share extensions with other researchers.

Many advances in image processing have come from specialized algorithms, made available as standalone software, libraries or plugins. [BaSiCPy](https://github.com/peng-lab/BaSiCPy) corrects uneven illumination and background, N2V2 reduces noise and Cellpose finds cells [@Stringer2021Cellpose; @Hock2022N2V2]. Choosing suitable functions and settings matters because imaging artifacts can otherwise appear as biological differences. Cellpose plugins for Fiji and napari and N2V2 for napari provide host-specific access [@FijiCellpose; @CellposeNapari; @NapariN2V], but updates to the underlying libraries or host interfaces can require integration changes. The [napari-n2v installation guide](https://github.com/juglab/napari-n2v/blob/0e9fee355d5f51c8ec0f0a6a3b9e4c71fe35237e/docs/installation.md#L15), for example, states that “`n2v` is not compatible with TensorFlow 2.16 and upwards” and its [maintenance notice](https://github.com/juglab/napari-n2v/blob/0e9fee355d5f51c8ec0f0a6a3b9e4c71fe35237e/README.md#L11) says the plugin is “no longer maintained”. The documented [RunCellpose recipe for Cellpose-SAM on Apple Silicon](https://plugins.cellprofiler.org/runcellpose.html#cellpose-sam-cellpose-4) uses `python=3.9` with `cellpose==4.0.6`; Python 3.9 [reached end of life on 31 October 2025](https://peps.python.org/pep-0596/#lifespan). These examples show why laboratories must consider the integration's supported environment alongside the algorithm itself.

A repeatable end-to-end analysis must exchange images and results while preserving channels, dimensions, pixel sizes and sample identities. Researchers must maintain the connecting scripts when tools, parameters, formats or versions change, creating a barrier for those without programming training. In the image.sc support forum [@Rueden2019Forum], installation appeared in approximately 19% of roughly 500 recent threads [@Ouyang2023].

Existing Python bridges reduce some of this integration work; the [software-resource inventory](supplementary/software_resources.md) links their extension routes and learning resources. PyImageJ connects ImageJ to Python, napari-imagej makes ImageJ tools available in napari, and magicgui generates controls from Python functions [@Rueden2022PyImageJ; @NapariImageJ; @NapariMagicgui; @NapariWidgetWorkshop]. A complete analysis can still require code to connect images, detections, measurements and settings while preserving sample identities.

To address dependency conflicts between bioimaging tools, container systems such as Docker package tools with their required libraries in isolated environments. Other integration routes include Fiji–CellProfiler image and table exchange [@Dobson2021], BioImageIT's packaged processing and data management [@Prigent2022], CellProfiler's Python and Docker plugins [@Weisbart2024], and MCMICRO's coordination of tissue-imaging tools through containers and files [@Schapiro2022; @MCMICROImplementation]. Different dependency versions can increase container-image storage, and file-based workflows add reads and writes between steps. Scientists must also coordinate settings, execution and inspection across the packaged tools, choosing parameters and checking the resulting measurements.

Much research effort has gone into platforms where AI assistants aim to reduce this technical burden by helping researchers develop and run analyses from written requests. We outline community-linked assistance, generated Python and specialist tool use, including the Model Context Protocol (MCP) for invoking software operations, in [Supp. Table 3](supplementary/README.md#supplementary-table-3.-ai-assistance-and-evaluation-resources). BIABench separately evaluates agent-produced analyses against reference answers and expert assessments: performance was stronger on routine 2D tasks, while repeated runs were unreliable on more complex data [@Pan2026BIABench].

Connecting individual pairs of tools leaves scientists to assemble those connections into an analysis they can build, run, inspect and revise. A shared workflow makes those tasks available together. We developed OpenHCS as a native Python integration layer for connecting existing bioimage-analysis tools and platforms within one editable analysis. Graphical settings can be opened as editable Python, and applying code changes updates that same analysis and its controls; pipelines can be shared as reusable presets (Figure 1A). From within the running application, laboratories can add compatible Python functions without writing a host-specific plugin package; these functions receive the same controls and agent access (Figure 1B). Multiprocessing runs samples in parallel, while native GPU support lets functions use libraries such as PyTorch and TensorFlow. Results remain linked to source images and samples (Figure 2); OpenHCS uses PyImageJ for Fiji viewing and also supports napari. From a biological task brief, agents use MCP to build, run, inspect and repair these same pipelines autonomously.

We demonstrated shared graphical and Python editing, compatible-function extension and linked result inspection. We compared images, measurements and completion times for 30 imported CellProfiler workflows and measured OpenHCS worker scaling on a fixed twelve-sample workload. Independent agents also developed analyses of neurite growth, nuclei and protein redistribution; we compared their final measurements with references after development.

## Materials and Methods

OpenHCS must coordinate images across microscope formats, processing functions, storage systems, viewers and parallel processes. We built eight domain-agnostic libraries for editing, settings, data handling and communication and composed them into OpenHCS (Figures 1–2; Supp. Table 1). The Open Microscopy Environment (OME) data model describes images using spatial dimensions X, Y and Z, channels and time [@Goldberg2005]. For plate imaging, well and site identify acquisition locations rather than additional pixel axes.

### Building and editing pipelines

A pipeline combines image-processing functions into a reusable, ordered sequence of configurable steps. Each step specifies one or more compatible Python functions, their settings and inputs from source images or earlier results. Functions specify their array library and whether they accept image planes or volumes.

Preconfigured microscope handlers use file-discovery rules and metadata to identify each well, site, channel, Z plane and timepoint. Supported rich image containers without a specialized handler are read through Bio-Formats. For ordinary folders without a recognized acquisition layout, source bindings let users select readable files, extract coordinates and name pipeline inputs, tasks familiar from [CellProfiler's image-input setup](https://cellprofiler-manual.s3.amazonaws.com/CellProfiler-4.2.8/help/projects_configure_images.html). Reading a file supplies its pixels and available metadata; users can assign channel and experimental roles explicitly when that metadata is insufficient.

Laboratories can extend an analysis without maintaining a separate plugin package by selecting compatible functions from existing libraries or adding their own Python function code within the running application. We built PyQt-Reactive to generate parameter forms from the function signatures and configuration classes used by the underlying analysis code, which can run without a graphical interface. Like magicgui [@NapariMagicgui], it derives parameter names, types, defaults and documentation from Python definitions. Compatible new functions therefore receive controls without separate interface code (Figure 1B), while the forms remain synchronized with analysis settings. The same definitions supply agent-facing parameter descriptions. Each function defines its inputs and outputs; registering these definitions integrates the function with execution, graphical editing and agent access. We render graphical settings as editable Python, and applying code edits updates the same analysis and its controls. Shared defaults, step-specific settings and edit history remain with the analysis, which scientists can save as a reusable preset (Figure 1A–B). OpenHCS discovers compatible processing and storage classes through shared interfaces rather than separate implementation lists.

### Figure 1. Graphical controls and Python edit the same analysis

![Full-width high-resolution native workspace with two example plates and a nine-step pipeline; boxes mark its existing controls.](figures/slas/submission_shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** OpenHCS brings input selection, analysis editing and execution status into one workspace, shown here with the ExampleHuman and ExampleFly image folders and a nine-step ExampleHuman analysis. The Plate Manager at left lists input collections and their analyses. The Pipeline Editor at right lists object-detection, measurement and export steps in execution order, with their settings available for editing. The lower-left server panel reports execution-server and desktop-connection status. Blue outlines identify these three regions; annotations indicate their roles. Scientists can prepare and follow the analysis from this window.
:::

### Execution and viewers

Processing libraries store image pixels in different array formats. ArrayBridge handles conversions so that NumPy, TensorFlow, PyTorch, JAX and pyclesperanto functions can run in one pipeline without users writing conversion code between steps. It manages transfers between central processing unit (CPU) and graphics processing unit (GPU) memory, using supported direct transfers or copies as required.

A step collects images into stacks along a selected dimension: site, Z plane, channel or timepoint. Collecting Z planes forms a volume; collecting overlapping sites supplies tiles to a stitching function, which also needs tile positions. The remaining coordinates stay fixed. Processing groups then determine which function sequence each group of inputs receives. Grouping by channel, for example, applies different sequences to different channels without changing how images are stacked. Grouping defines the work; worker assignments determine what runs in parallel. Sample and image coordinates are retained, and later steps can inherit or replace the grouping and stacking settings (Supp. Figure 1).

To measure the intended cells or structures, processing functions need the correct images and detected objects. Steps produce processed images, object-label images, numerical measurements, object relationships and exported files. Label images assign identifiers to individual objects; relationships link related detections, such as a nucleus with its surrounding cell. Before processing begins, the compiler connects defined inputs and outputs, checks function requirements and plans data-format conversions and worker assignments (Figure 2; Supp. Figure 1). This detects incompatible configurations early and reduces repeated planning during processing. Separating the plan from its execution lets worker execution reuse the same prepared connections and function requirements rather than rebuild that logic for each execution route.

OpenHCS coordinates the editor, execution server, workers and viewers while they run concurrently. ZMQRuntime provides one native Python interface for communication between their processes (Figure 2). ZeroMQ messages carry requests, results and progress through shared client and server interfaces; applications add operations such as viewer controls through those interfaces. Separate processes keep these responsibilities apart and allow their failures to be handled at process boundaries. ZMQRuntime coordinates process startup, shutdown and progress. Workers reuse loaded libraries and CPU/GPU resources across assigned samples to reduce repeated setup, then release them after the run. Execution uses processes by default, with optional threads.

These programs also need access to images held in different forms and locations: TIFF files, compressed Zarr stores, memory or an OMERO server. PolyStore provides shared reading and writing interfaces so processing steps can use those sources without separate storage code. Viewer destinations deliver results to Fiji or napari through the same data-handling layer. A new destination implements the shared interface instead of adding a storage path to every processing step. OME-Zarr stores microscopy data in blocks, allowing selected image regions to be retrieved without downloading the entire dataset [@Moore2021]; OpenHCS reads its images, dimensions, channels and pixel sizes. Experimental OMERO support provides access to images in a shared image-management server.

These shared interfaces let saved and displayed results retain their source coordinates, processing group and producing step across supported viewers and storage formats. Scientists can therefore trace measurements back to their source images and detected structures. We made saving and live inspection independently configurable: image results can be saved to a folder and sent directly to Fiji or napari as processing proceeds (Figure 2). Scientists can inspect results without finding and loading each output file manually. Viewer sessions remain open after execution for continued inspection, and agents can query napari layers and regions of interest. During processing, the streaming service checks viewer readiness and waits for display updates.

### Figure 1, continued. The laboratory's own Python joins the shared analysis

![Real Python definition and docstring, generated controls, live editable Python and agent-facing parameter descriptions.](figures/slas/submission_custom_function.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(B)** A laboratory-specific Python function is available through graphical controls, editable code and the agent interface. The function definition specifies its parameters; the docstring describes their meaning. OpenHCS uses this information to generate the parameter controls and descriptions available to an agent. The graphical form and Python views both show gain 1.2 and offset 0.0 for the same function. Parameter changes between the graphical and Python views are documented separately in Supp. Data 5. Scientists can therefore use either view while agents work with the same analysis, rather than maintaining separate graphical and scripted interfaces.
:::

### Agent access through MCP

Learning to configure complex analysis software takes time and can discourage adoption. We designed the agent interface to help scientists get started while keeping an agent's work accessible through the same tools and settings they use themselves. We expose function discovery, pipeline editing and validation, execution and result inspection through MCP [@MCP]. Each operation's definition specifies its input and result types, implementation, permitted changes, data access and security requirements; these definitions generate the interface and govern execution. Agents can edit an analysis open in the desktop application or run one without opening a window.

To protect analyses from unintended access and conflicting edits, desktop connections require authentication and revision checks prevent an agent from overwriting intervening edits. MCP file operations check permitted directories. Processing functions run as Python code with the worker's permissions; these path checks are not an operating-system sandbox. Local clients communicate through standard input/output. A hosted HTTP interface gives remote assistants access to packaged knowledge, architecture descriptions, processing-function discovery and configuration schemas without connecting to a scientist's local application. This interface is read-only and cannot access local files, graphical state, viewers or execution sessions.

### CellProfiler import and output comparison

CellProfiler is an established reference for image analysis in academic and industrial laboratories [@Carpenter2006; @McQuin2018]. Keeping validated pipelines on fixed software versions helps preserve results, making dependency updates a reproducibility concern as well as a maintenance task. To let scientists reuse these pipelines with OpenHCS’s editing, execution and agent tools, we built an importer. We then checked their output images and measurements against native CellProfiler results before comparing execution times (Figure 3).

The importer reads `.cppipe` settings and translates processing and export modules into configurable steps and setup modules into source bindings. Module definitions specify images, objects, measurements, relationships and image-group or plate-wide operation. The resulting pipeline uses OpenHCS compilation and execution and remains editable through graphical controls, Python and MCP. Named images and objects connect measurements to inputs. We reloaded generated Python for the advanced-segmentation and 3D-monolayer tutorials to check functions and parameters [@CellProfilerTutorials] (Supp. Data 5). CellProfiler-compatible numerical implementations include Numba-compiled propagation kernels.

We checked that imported workflows retained their outputs by comparing numerical measurements and image pixels with absolute and relative tolerances of `1e-6`. Identifiers and categorical values were compared exactly after the documented formatting adjustments needed to match CellProfiler. Object-label images were compared exactly after standardizing dimensions of length one. Five workflows lacking exports received a final image or label export step without changing their processing settings. Every expected exported file was checked in each workflow. Supp. Data 1–2 provide output counts, comparison rules, imported modules and settings, and details of the additional software checks.

### Performance measurement

For the single-sample comparison, both applications used one physical CPU core, one worker and one numerical thread, so neither received extra CPU resources. Each workflow used one selected source well or sample, unchanged settings and defined comparison outputs. OpenHCS supports Python 3.11–3.14, but the reported timing runs used Python 3.12, against native CellProfiler 4.2.8.1 on Python 3.9.

**Timing intervals.** Table 1 defines the two reported intervals. Speedup was CellProfiler's first-batch time divided by the median OpenHCS time; we summarize speedups across workflows using their minimum, arithmetic mean, median and maximum.

Table: Table 1. Timing boundaries used for the execution comparisons.

| Application | Processing | Setup plus processing |
|---|---|---|
| CellProfiler | Immediately before the pipeline first runs → batch completion, including internal initialization, image-group preparation, processing, output steps and measurement-file closure. | Before initial output-directory and measurement setup → the same batch completion. |
| OpenHCS | Server execution-job start → job completion, including saving results and plate-level exports. | Sum of four client intervals: submit compilation, wait for compilation, submit execution and wait for execution. |

OpenHCS times are medians of three measured repetitions after warmup. Application/server startup, CellProfiler pipeline-file loading, initial OpenHCS library loading, OpenHCS warmup runs and subsequent output-agreement checks were excluded. OpenHCS server time is already inside the client intervals and was not added again.

**Batching and workers.** Twelve copies of one source sample measured batch-processing costs. Per-sample times divided the measured eight-sample CellProfiler time by eight and the one-worker, twelve-sample OpenHCS time by twelve. A separate measured comparison used eight copies in each application, two OpenHCS workers and one serial CellProfiler process (Supp. Data 3). The CellProfiler batch used one numerical thread with four permitted CPUs (2–5), versus one CPU in the single-sample comparison. OpenHCS batch workers also had access to those four CPUs, with one numerical-library thread per worker; workers were not pinned to individual cores. We estimated one serial CellProfiler twelve-sample time per workflow from measured eight-sample first and post-initialization batches, using a model calibrated on three workflows. We kept that estimate fixed while measuring OpenHCS with one, two, three or four workers on the same twelve-sample workload (Figure 3C). OpenHCS worker scaling was measured for both timing intervals. Combined process memory was not measured. Supp. methods: execution-time estimates and Supp. Data 3 retain formulas, calibration and the full benchmark protocol.

### Software reliability checks

Bioimage analyses combine tools, dependencies and data formats that change independently, so software updates can alter results even when a pipeline still runs. Passing tests, including AI-generated ones, are useful only when they check behavior scientists rely on. We therefore built automated checks around complete analysis tasks. Before PyPI release, the automated test workflow, known as continuous integration, is configured to install candidate wheels, run the 30 imported CellProfiler pipelines and compare their outputs with saved native results on Linux, Windows and macOS, each with Python 3.12 and 3.14. These release checks address installation, which appeared in about 19% of the surveyed image.sc threads [@Ouyang2023]. Other checks exercise storage, microscope inputs, live viewers and saving and reloading analysis settings (Supp. Table 2).

### Figure 2. One editable workflow connects editing, execution and inspection

![Shared editing, execution, workers, viewers and image storage.](figures/slas/shared_workflow.png){width=6.5in}

::: {custom-style="ImageCaption"}
Graphical forms, Python and agents using MCP edit the same analysis, including imported CellProfiler pipelines. The editor sends compilation and execution requests to the execution server, which prepares the data connections and assigns processing to workers using ZMQRuntime's communication infrastructure. Worker processes load source images, execute the analysis on CPU or GPU resources and save images, object labels and measurements. Image and region-of-interest results can also be sent to napari or Fiji for inspection. Blue arrows show requests, compiled work and status updates between the editor, server and workers; green arrows connect workers with viewers and stored data. Progress returns to the editor while the analysis runs. Separating these processes allows image inspection and editing to remain available alongside processing. Supp. Figure 1 describes how image groups, function preparation and worker assignments are assembled.
:::

### Data acquisition and generation

We used public benchmark images, distributed demonstration images and laboratory acquisitions to examine analysis reuse and agent-developed measurements.

The nuclear, cell-boundary and protein-translocation datasets came from the Broad Bioimage Benchmark Collection (BBBC): BBBC039 nuclear images, BBBC007 paired DNA/actin fields and the BBBC013 green fluorescent protein (GFP)/DNA assay.

Bright-object detection used the two-dimensional H001 image distributed as `blobs.tif` in the pinned Haase notebook collection; its comparison labels were computational, not manual biological annotations. Three-dimensional nuclear localisation used the collection's H002 nuclei volume, 60 × 256 × 256 voxels, with 15 manually marked centres covering only part of the volume. Body-separation repair used the same volume in a separate development analysis. Original specimen and acquisition details were not established for these distributed fixtures; H002 physical spacing was unverified.

Retinal cell-body detection used the user-provided R0010 whole-mount acquisition, with RNA-binding protein with multiple splicing (RBPMS) and Hoechst channel information. The retinal repair scale comes from the original CZI metadata. Public neurite tracing used paired TIFFs from NeuronCyto II image 1; coordinate-level manual traces and verified physical calibration were unavailable. Separate laboratory tracing used nine DAPI/calcein fields from one coded well, distinct from the 20-well drug-response cohort.

To test whether independent analyses recovered drug responses, we used images of primary cortical neurons from embryonic day 18 rats, imaged two days after plating. Fusicoccin-A (FC-A) and Y27632 were each tested at 0, 5, 10, 20 and 40 µM, with two technical wells per dose and dimethyl sulfoxide (DMSO) vehicle controls. Nine paired nuclear/neuronal fields were acquired per well. Medium changes, recorded channels, image dimensions and pixel size are given in Supp. methods: neurite morphometry.

### Autonomous analysis design

Agents finalized their pipelines before any comparison with reference data, and no pipeline changed after scoring began. They received no reference labels, accepted settings or score feedback while building their analyses. First-versus-final comparisons use the first completed prediction and the final settings on the same inputs. Self-directed repairs are autonomous; revisions prompted by a scientist are assisted.

To test whether agents could turn biological requests into useful measurements, we asked fresh agents to develop and inspect analyses of cells, nuclei, neurites and protein redistribution. We compared their final results with references after analysis development had finished. Separate runs let us compare independently developed analyses of the same task.

The tasks span neurite responses, nuclear and cell-boundary detection, protein redistribution, bright objects, retinal cell bodies and three-dimensional localisation and separation. Supp. Table 4 identifies each analysis's model and development/evaluation protocol, including prospectively withheld and retrospective subsets. Analysis numbers are local identifiers; Supp. Data 8 links the original runs, guides and pipelines.

Each fresh agent received a task brief, acquisition information and MCP access. The recorded gpt-6.1-sol independent trials also received the packaged OpenHCS skill, a written guide to using OpenHCS; briefs could include channel hints, requested outputs and review instructions. The skill asks agents to inspect images, read function documentation and compare results with matched raw images and overlays (Figure 4). It directs repairs to the earliest faulty step and requires rechecking previously successful examples. Earlier held-out trials used OpenHCS 0.8.5; later independent trials used 0.8.7. For the prospective evaluations, images and treatment metadata were released after finalization; only input and output folders changed.

Three fresh gpt-6.1-sol agents independently analysed the same 20 coded neurite-assay wells, with nine fields each, using the same brief, acquisition information, MCP access, guide revision and OpenHCS 0.8.7 installation. Each analysed all 180 fields and finalized its outputs before treatment identities, MetaXpress measurements and scientist-assisted results were used for evaluation. Development and subsequent review fields are listed in the cohort record (Supp. Data 8; Supp. Figure 5).

For nuclear detection analyses 2–4, image-delivery records identified 25 BBBC039 fields viewed by at least one agent; we evaluated all 200 fields and the other 175 as a retrospective image-unviewed subset, not one withheld before development. Cell-boundary analyses 2–3 used all 16 fields; protein translocation analysis 2 used all 96 wells, including four development wells. Supp. Data 7–8 provide the original task briefs, guide versions, final pipelines, data partitions, scores, model and software versions, task times and computational usage.

## Results

### Scientists can inspect, revise and extend the analysis behind a measurement

Scientists can follow a measurement back to the source field and producing step, inspect the detected objects in Fiji or napari, and revise the analysis that produced them (Figures 1–2). Graphical controls and Python operate on the same settings: an agent's changes update the desktop analysis, which the scientist can continue editing without reconstructing its steps. In the recorded example, changing the upper normalization percentile from 99.8 to 99.6 appeared in the form; restoring 99.8 updated the generated Python (Supp. Data 5).

When a different processing method is needed, a compatible library function or laboratory-written function joins that same sequence. Its parameters become available through graphical controls, Python and the agent interface (Figure 1B). The scientist can therefore inspect a detection, change its settings or method, rerun the relevant analysis and retain the revised pipeline as a reusable preset. Imported CellProfiler analyses use this shared editing mechanism too; Supp. Data 5 documents advanced-segmentation and 3D-monolayer examples.

### Established workflows retain their outputs and run faster {#established-cellprofiler-workflows-retain-their-measurements}

All 30 imported workflows reproduced native CellProfiler 4.2.8.1 outputs across assays including morphology, protein translocation, tracking and multi-stage 3D analysis. Images marking individual detected objects retained their pixels and identifiers exactly; numerical measurements agreed within absolute and relative tolerances of 1e-6. Comparisons also covered calculated pixel values, measurement tables and SQLite measurement databases for CellProfiler Analyst compatibility (Supp. Data 1). They establish output agreement; CellProfiler Analyst itself was not run. Across 85 processing modules, 54 were tested in complete workflows and 29 individually; the remaining two had shared-code tests (Figure 3A).

Output parity was retained on Python 3.12 and 3.14. The timing comparison used OpenHCS on Python 3.12 with NumPy 2 and native CellProfiler on Python 3.9 (Supp. Data 1). CellProfiler 4.2.8.1 pins SciPy 1.9.0 and scikit-image 0.18.3 [@CellProfiler4281Dependencies]. Prebuilt PyPI packages for that scikit-image release cover Python 3.8 and 3.9 among the versions admitted by CellProfiler; both Python versions are now end of life [@ScikitImage0183Files; @Python38Release; @Python39Release]. Availability of source code does not establish support for newer Python versions or native Apple Silicon. The tested workflows retained their outputs on OpenHCS's newer dependency stack.

Faster reruns make it easier to revise an analysis and check it across an experiment. We measured completion times with output export included and checked output agreement.

Every one of the 30 workflows was faster than CellProfiler on one core, both for processing alone and with pipeline setup included (Figure 3B). When CellProfiler's internal initialization was spread over a measured eight-sample serial batch, the median per-sample processing speedup across workflows was [pending]{.benchmark-claim key=amortized_execution_median}-fold, with a minimum of [pending]{.benchmark-claim key=amortized_execution_min}-fold. This comparison divides each application's time by the number of samples: eight for CellProfiler and twelve for OpenHCS, using one worker. Including pipeline setup, speedup was a median [pending]{.benchmark-claim key=amortized_total_median}-fold, with minimum [pending]{.benchmark-claim key=amortized_total_min}-fold. Supp. Data 3 provides individual workflow timings, batch summaries, CellProfiler estimates, calibration checks and a separate measured eight-sample, two-worker comparison.

Figure 3C holds the workload at twelve samples and compares measured OpenHCS times with a fixed serial CellProfiler estimate derived from measured eight-sample batches. Increasing the OpenHCS worker count from one to four increased the median speedup relative to this unchanged baseline. Every workflow was faster than the serial estimate at each worker count, for processing alone and with setup included. This comparison measures the benefit of OpenHCS parallel execution relative to a serial reference, not equal CPU allocations.

Measured OpenHCS-only scaling confirms the separate parallel-execution benefit: on the same twelve samples, every workflow ran faster with two, three and four workers than with one, for both timing intervals (Supp. Figure 6).

### Figure 3. CellProfiler compatibility and execution speed

![Graded module coverage, measured one-worker comparisons and a fixed serial CellProfiler estimate compared with measured OpenHCS worker counts on twelve samples.](figures/slas/submission_benchmark_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
Imported CellProfiler workflows were checked for output agreement before their execution times were compared. **(A)** Each module is counted once under its strongest test; zero-count categories have no slice. Shared-code tests do not test each module's own algorithm. **(B)** Measured one-worker comparisons: one sample each on the same CPU core, then per-sample time for batches of eight (CellProfiler) or twelve (OpenHCS). Batch CPU affinities differ from the single-sample comparison (Methods: Performance measurement). **(C)** Twelve copies of one source sample: a fixed serial CellProfiler estimate derived from measured eight-sample batches, divided by measured OpenHCS time at each worker count. The serial estimate retains initialization and is identical across all four worker counts. **(B, C)** Speedup is CellProfiler time divided by OpenHCS time; values above 1 mean faster OpenHCS execution. Each dot is one of 30 workflows; translucent bars are arithmetic means and black lines medians. Each distribution is labelled with its minimum, arithmetic mean, median and maximum speedup. Logarithmic axes; the red dashed line marks equal speed. Intervals and exclusions as in Methods: Performance measurement.
:::

### Figure 4. Delegated specialist work leaves an analysis the scientist can inspect

![Guide-directed procedure from biological brief through image inspection, analysis revision and editable delivery.](figures/slas/submission_autonomous_loop.png){width=6.5in}

::: {custom-style="ImageCaption"}
Analysis procedure described by the agent guide. The biological brief specifies the question, requested measurements and acquisition information. Image inspection establishes channels, feature scales and representative regions before the agent selects processing functions and runs the pipeline. Results are compared with raw images from the same region; errors lead to revised settings and further inspection before delivery. The scientist receives the analysis settings, images and measurements and can continue editing the analysis. Figure 6E–H shows recorded repair examples, rather than guarantees of the procedure.
:::

### Agent-developed analyses produce useful assay measurements

#### Three blind agents recover drug responses in a laboratory neurite assay

All three analyses found increased mean outgrowth per cell and total outgrowth at every nonzero dose of FC-A and Y27632 (Figure 5A–B). Across the 20 wells, each agent's mean outgrowth per cell correlated closely with MetaXpress (Pearson r 0.963 to 0.996), but response magnitudes were generally smaller. At 40 µM, mean outgrowth per cell increased 1.32–1.65-fold for FC-A and 1.49–1.69-fold for Y27632, against 1.98- and 2.05-fold for MetaXpress. Thus independently developed analyses recovered both drug responses while differing in their estimated size. Supp. Figure 5 gives cell-count, process-length and branching comparisons; these remain algorithm-defined measurements rather than manual tracing ground truth.

### Figure 5. Three independent agents recover both neurite outgrowth responses

![Drug responses from three independent blind agents, followed by a separate laboratory neurite tracing demonstration.](figures/slas/submission_neurite_results.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A–B)** Mean neurite outgrowth per cell after treatment with fusicoccin-A (FC-A) or Y27632. Three independent blind agents and MetaXpress analysed the same 180 fields from 20 wells; analyses 1–3 identify independent agent runs. OpenHCS well values are unweighted means of nine fields. Each drug curve is normalized to the mean of its two zero-dose DMSO wells; 1 denotes no change from vehicle. Dots are two technical wells per dose for each method; whiskers show sample standard deviation (SD) among those wells, excluding uncertainty in the control mean. All three analyses recover increased outgrowth for both drugs, with smaller response magnitudes than MetaXpress. **(C⁠–⁠E)** A laboratory field shown as a raw image, detected cell bodies and neurites, and an overlay on the raw image. This separate nine-field autonomous analysis is not one of the three drug-response analyses in A–B. Scale bars in C–E are 271 µm (200 pixels at the recorded acquisition scale). Supp. Figure 5 shows additional measurements and the scientist-assisted comparison; Supp. Data 4 retains the separate public-image comparison.
:::

#### Agent-built nuclear pipelines span expert CellProfiler pipelines on a public benchmark

On BBBC039’s official 50-image test partition (5,720 nuclei), the agents’ per-image mean F1 at IoU ≥ 0.5 was 0.898 to 0.903; F1 balances recovery of reference nuclei against false detections. Using Caicedo et al.'s released evaluator, the frozen agent pipelines scored 0.792–0.823 (F1 averaged over IoU 0.50–0.90), spanning the expert-configured CellProfiler 3.0 pipelines (0.790 and 0.811) and below the learned methods (0.840–0.898) [@Caicedo2019]. Two of the three analyses viewed no official test field before their methods were frozen; the third viewed one, and excluding that field changed its scores by less than 0.001. Our agents received no reference labels while building their pipelines. Supp. methods: analysis scoring gives the evaluator, the 49-field check and the supplementary 44-field robustness check.

On the separate retrospective subset of 175 BBBC039 fields not viewed by any agent, nuclear detection analyses 2–4 reached pooled F1 of 0.906–0.910 (Figure 6A). Pooled scores combine object counts across fields. Most errors were missed nuclei, and all three analyses scored below 0.80 on the same six fields. Their similar overall accuracy therefore coexisted with shared local failures. Supp. Figure 3 and Data 7–8 retain per-field errors, all-field and earlier withheld-evaluation results, and the repair that recovered nuclei while increasing splitting.

#### An agent-developed translocation analysis separates assay controls

Protein translocation analysis 2 separated controls across 96 BBBC013 wells, including four development wells, with Z′ of 0.849 for LY294002 and 0.726 for Wortmannin (Figure 6D). Z′ compares the separation of control means with variation between wells; both values exceed 0.5, the conventional threshold for an excellent screening assay [@Zhang1999]. The agent chose each well's median log2 nuclear-to-cytoplasmic GFP ratio, using cells with measurable cytoplasm and four wells per treatment group. Supp. Figure 2 and Data 7–8 retain eligibility counts and the earlier analysis on 92 wells withheld before development, which used a different well summary.

### Image review identifies repairs and remaining errors

Matched image inspection exposed errors that overall scores could hide. Agents corrected a split bright object, merged nuclei, fragmented retinal outlines and an over-split three-dimensional body (Figure 6E–H). Bright-object reference F1 rose from 0.929 to 0.944 on one development image; the remaining examples show local image-supported corrections rather than measured whole-dataset accuracy. On 16 BBBC007 DNA/actin fields, cell-boundary analyses 2–3 placed 0.743 and 0.740 of their predicted borders between touching cells within two pixels of a manual outline (Figure 6B).

Orthogonal views let scientists check three-dimensional detections across planes. Nuclear localisation analysis 1 recovered all 15 manually marked centres within 30 voxels; 11 predictions lacked a matching annotation, but the partial reference cannot establish their false-detection rate (Figure 6C; Supp. Figure 4M–O). Wider matched views retain residual merges, unsupported cell-body growth and unresolved neurite crossings (Supp. Figure 4; Figure 5C–E). Captions and Supp. Data 4, 7–8 identify the separate analyses, references and repair trajectories.

### Figure 6. Analysis measurements and matched image repairs

![Nuclear, boundary, localisation and translocation measurements above matched bright-object, nuclear, retinal and volume repairs.](figures/slas/submission_analysis_summary.png){width=6.5in}

::: {custom-style="ImageCaption"}
**(A)** Nuclear analyses 2–4: pooled F1 on 200 BBBC039 fields and the retrospective 175-field image-unviewed subset; matches require IoU ≥ 0.5. **(B)** Cell-boundary analyses 2–3: fraction of predicted touching-cell borders within two pixels of manual outlines, 16 fields each. Dots are fields; lines pool pixels. **(C)** Nuclear localisation 1: mean error of centres matched to partial manual annotations; labels give matches among 15 centres, dashed line the 30-voxel limit. Unmatched predictions cannot establish a false-detection rate. **(D)** Translocation 2: 96 wells, including four development wells. Dots are well-median log2 nuclear/cytoplasmic GFP ratios; marks show mean ± sample SD across four wells per dose. Drug plots share limits; Z′ measures control separation. **(E)** Four bright-object development versions, then matched raw/first/final crops. Computational-reference F1 increased 0.929 → 0.944; first execution took 14 min and the whole task 45 min. **(F)** Matched DNA-region nuclear repair (H003_POSTPAUSE_88), separate from the paired-channel Fresh26 analysis. Bar, 10 pixels. **(G)** Raw RBPMS and first/final retinal outlines (R0010_FRESH16_88); image-review evidence, not measured accuracy. Bar, 20 µm from CZI metadata. **(H)** Raw, first labels, final labels and final overlay at Z = 36 in the separate H002_FRESH22_89 development repair. Bars, 10 voxel-index units; physical spacing is unverified. Image regions are matched within comparisons; colours distinguish detections within a view. Detailed trajectories and final-only orthogonal views are in Supp. Data 8 and Figure 4M–O.
:::

## Discussion

OpenHCS connects existing bioimage-analysis tools through a native Python layer, combining analysis editing, execution and inspection. Shared Python definitions supply graphical controls, editable Python and agent descriptions, while imported CellProfiler pipelines enter the same compilation and execution path, letting scientists and agents inspect, revise and reuse analyses through the same tools.

Preserving the outputs of established workflows lets laboratories extend analyses without discarding their existing processing choices. The 30 CellProfiler workflows retained their outputs on OpenHCS's newer Python environment (Figure 3). Scientists can extend these pipelines with compatible CPU, GPU and deep-learning functions from existing libraries or laboratory code as biological questions change.

Faster reruns reduce the cost of inspecting a result, changing the pipeline and checking it again across an experiment. With one worker and CellProfiler initialization spread across eight samples, OpenHCS retained a median [pending]{.benchmark-claim key=amortized_execution_median}-fold per-sample speedup (Figure 3B). The advantage persisted with pipeline setup included, and additional OpenHCS workers shortened execution further. The single-core comparison shows an execution advantage without extra CPU resources; measured worker scaling adds a separate parallel-execution benefit.

Separating general computing tasks from microscope-specific definitions also makes the components reusable outside microscopy (Supp. Table 1). Pipelines organize data by dimensions and processing groups without requiring microscope-specific fields; source tests include remote-sensing and telemetry examples. Work is underway to release preparation and execution separately as ArrayPipe [@ArrayPipe], so other data-science and machine-learning applications could combine array libraries, run processing steps in parallel and inspect intermediate results.

All three neurite analyses recovered both drug responses but estimated smaller effects than MetaXpress (Figure 5A–B). The commercial reference's site weighting and analysis settings were unavailable for comparison; the OpenHCS measurements remain traceable to their detections, settings and source images. All three nuclear analyses also missed nuclei in the same six difficult fields. Scientists therefore need access to the detections behind a measurement even when independent analyses agree.

Repeated agent runs have been unreliable on complex data [@Pan2026BIABench], and Agentic-J describes independent-session repeatability as future work [@Johanns2026]. Here, three independently developed nuclear analyses agreed within about 0.004 pooled F1 across three guide revisions, and all three neurite analyses recovered both drug responses with the same model, guide and runtime. These are independent analyses of the same experimental material, not biological replicates.

The shared analysis infrastructure can also benefit from stronger agents and vision models. They can use the existing authoring, execution and image-inspection tools to choose methods and revise results, while new machine-learning functions join the same editable Python pipelines. Multicore execution distributes samples among workers, and GPU-capable functions use their declared array frameworks. Methods that distribute work over multiple GPUs must retain that coordination within their underlying library; OpenHCS's current compiler assigns a device to each required framework. This separates the platform's useful interfaces from the particular agent models and processing methods evaluated here.

OpenHCS addresses analysis development and execution within laboratory automation, with external agents driving OpenHCS over MCP in our trials. Systems using SiLA, a standard for laboratory automation, connect instrument control and laboratory data [@Hinkel2023; @Lange2026; @Courtney2025; @Thieme2024; @Rihm2024]. In either a conventional or automated laboratory, the aim is to delegate technical analysis work while keeping scientists able to judge, change and extend it.

## Supp. Data {#supplementary-data}

Supp. figures provide additional assay results and image comparisons. Supp. Data 1–3 contain CellProfiler output comparisons, module coverage and timing measurements; Data 4–6 contain NeuronCyto references, editable workflows and software checks; Data 7–8 contain agent instructions, final pipelines, evaluation partitions and individual analysis results.

## Code and Data Availability

OpenHCS source code: <https://github.com/OpenHCSDev/OpenHCS>.

OpenHCS documentation: <https://openhcs.readthedocs.io/>.

Supp. files contain figure inputs and generation scripts, final pipelines, scores and benchmark measurements. Versioned repository copies are available at <https://github.com/OpenHCSDev/openhcs/tree/192500f312c25d7d8f406516e1b7f1cec908334f/paper/supplementary> and <https://github.com/OpenHCSDev/openhcs/tree/192500f312c25d7d8f406516e1b7f1cec908334f/benchmark/results>.

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
