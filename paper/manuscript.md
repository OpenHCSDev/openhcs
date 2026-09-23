---
bibliography: openhcs_references.json
csl: styles/elsevier-vancouver.csl
reference-section-title: References
link-citations: true
link-bibliography: true
---

# OpenHCS: shared microscopy workflows for scientists and AI agents

**Authors:** Tristan Simas, Jathav Puvirajan, and Alyson Fournier

**Affiliation:** McGill University, Montreal, Quebec, Canada

**Correspondence:** Tristan Simas, <tristan.simas@mail.mcgill.ca>

**Short title:** OpenHCS: shared microscopy workflows

**Keywords:** microscopy; image analysis; laboratory automation; agentic AI; interoperability; high-content screening

## Abstract

Scientists need to inspect and revise image analyses built by AI agents. OpenHCS is an open-source platform in which scientists and agents edit the same microscopy pipeline through graphical controls, Python or the Model Context Protocol (MCP), which lets an AI client request analysis operations. Each registered processing function supplies the parameter names, types and defaults used to generate its controls and describe it to agents. The selected functions and settings remain editable as Python. Before execution, OpenHCS connects the selected images and intermediate results to each step and checks their compatibility. Established CellProfiler pipelines and custom Python functions use this model, with images, regions of interest and measurements available for inspection in napari and Fiji. All 30 imported CellProfiler workflows passed selected reference-output comparisons, including five supplemented with exports of computed images or object labels. A public neurite-outgrowth example documented an agent constructing, executing and inspecting an analysis without further human input after a detailed prompt. Validation rejected invalid pipeline documents before execution; subsequent visual review identified a tracing error that output checks had missed. Three prospective agent-authored workflows were frozen before held-out scoring: nuclear segmentation reached object F1 0.746, cell-boundary agreement was 0.671 within two pixels, and a translocation assay yielded Z-prime values of 0.751 and 0.554 for two drugs. Separate repeated-input runs measured throughput and memory across all 30 workflows. OpenHCS connects established analysis methods to agent-guided laboratory workflows while keeping processing choices and results available for scientific review.

## Introduction

Automated microscopy supports screening, time-course experiments, and quantitative studies of cells and tissues. Turning the resulting images into useful measurements requires an analysis workflow: identifying the image channels and dimensions, selecting processing functions, inspecting segmentation, and repeating the analysis across samples. Scientists often revise these choices after reviewing intermediate images. AI-guided laboratories need access to these same operations so that analysis can respond to experimental goals and scientist feedback.

An agent-operated analysis must also remain usable by the scientist. Researchers need to see which images were selected, how parameters were chosen, and whether the resulting masks match the structures of interest. They need to revise the pipeline directly and rerun it on another experiment. These requirements connect agent access to existing image-analysis tools, viewers, data stores, and execution systems.

Laboratory automation already uses shared declarations to connect instruments and software. SiLA 2 standardizes device communication, and the Tecan SiLA2 SDK generates server and client interfaces from annotated software declarations [@Hinkel2023]. Lange and colleagues demonstrated modular SiLA-based infrastructure linking device control and data management, while Courtney and colleagues integrated cell-culture instruments into an out-of-hours autopilot [@Lange2026; @Courtney2025]. Related work has connected liquid handlers to workflow orchestration and linked laboratory assets through shared information models [@Thieme2024; @Rihm2024].

Microscopy analysis requires a corresponding connection between processing functions, scientist-facing controls and agent access. OpenHCS applies declaration-driven interface generation to this analysis stage (Figure 1). A registered function supplies the parameter names, types, defaults and documentation used to build its controls and searchable catalog description. The shared workflow records selected functions and configured values as editable Python. A scientist can therefore open an agent-authored pipeline, change a parameter in a control or in code, and run the revised analysis. Imported CellProfiler workflows and custom Python functions use the same model.

Fiji/ImageJ, CellProfiler, Icy and BioImageIT support image processing and workflow construction [@Schneider2012; @Schindelin2012; @Carpenter2006; @McQuin2018; @deChaumont2012; @Prigent2022]. napari provides interactive multidimensional viewing, while OMERO, OME-NGFF and Bio-Formats support image management and access [@Napari; @Allan2012; @Moore2021; @BioFormats]. Scientific Python and GPU libraries supply additional algorithms [@vanDerWalt2014; @Haase2020], and workflow systems organize reproducible computation [@Koster2012; @DiTommaso2017; @Galaxy2020; @Galaxy2024]. Combining these resources requires keeping image identities, parameter choices and intermediate results consistent as an analysis moves between tools.

MCMICRO combines interchangeable processing modules for multiplexed tissue imaging [@Schapiro2022]. AI assistants also support executable bioimage analysis: BioImage.IO Chatbot connects community resources with analysis extensions, Omega generates and runs Python within napari, and Agentic-J generates scripts and coordinates Fiji tools with debugging and quality-assurance agents [@Lei2024; @Royer2024; @Johanns2026]. OpenHCS exposes a shared workflow object for agent operation: submitted pipeline documents are validated before analysis execution and remain editable through the scientist's controls and Python interface.

Before execution, OpenHCS prepares the workflow (compilation) by combining function requirements with configuration and image-source mappings. It resolves the selected images, checks the inputs and outputs of each step, and prepares work for execution processes. Scientists and agents receive feedback on setup errors before running the analysis, and can inspect selected intermediate results in napari or Fiji.

CellProfiler import provides a direct test of workflow preservation. A `.cppipe` file contains image-loading rules, module settings, image names, object names, measurement expectations, display choices, and output behavior. OpenHCS translates these files into editable workflows. Comparing their outputs against native CellProfiler tests whether the imported analyses retain the expected measurements and images.

We show that graphical controls and Python retain the same configured analysis through an editing round trip, and that all 30 imported CellProfiler workflows pass selected reference-output comparisons. An agent constructed, corrected and executed a neurite-outgrowth workflow through MCP; later visual review identified a tracing error despite successful output checks. Separate repeated-input experiments show how throughput and memory change with worker count and queue depth. Together, these results demonstrate shared workflow editing, reuse of established analyses and agent-operated execution with inspectable results.

### Figure 1. Scientists and agents operate a shared microscopy workflow

![Shared workflow, source connections and execution.](figures/slas/shared_workflow.png){width=6in}

\(A) Desktop, Python and MCP operations act on a shared pipeline; CellProfiler import supplies an editable analysis in that model. The processing sequence is illustrative, with functions chosen for each assay. (B) Image-source bindings and established or custom functions connect to the same definition. OMERO is experimental. (C) Compilation resolves inputs, dependencies and array requirements before worker processes execute the analysis. Selected intermediate results can be inspected in napari or Fiji, and retained images, ROIs and measurements support review and subsequent edits. CPU/GPU support depends on the selected functions; performance measurements are presented separately in Figure 5.

## Materials and Methods

### Workflow definition and image sources

An OpenHCS pipeline is an ordered sequence of analysis steps with shared settings. For example, a pipeline can select the nuclear channel, segment nuclei, pass the resulting labels to a measurement step, and display the labeled image alongside its measurements. Each step specifies a Python function or a sequence of functions with their parameters. A step uses shared defaults unless it supplies its own values, called overrides.

Before a run, OpenHCS identifies each step's source images and earlier results, checks their compatibility and prepares the function calls, array conversions and output destinations. This preparation is called compilation. It resolves shared defaults and step overrides into the values needed for execution. Execution units, called workers, receive the prepared plan (Supplementary Figure 3).

The parameter names, types and defaults declared by a Python function form its signature. OpenHCS combines this information with the workflow's current settings to generate on-screen controls and editable Python. Each function also declares which array library it expects, allowing images to pass between compatible CPU, GPU and deep-learning libraries. Volumetric analysis uses functions that support three-dimensional inputs, while two-dimensional functions operate on image planes.

Users can register custom Python functions for use in ordinary pipeline steps. The registered function appears in the editor's function list; its signature and documentation supply parameter controls and the searchable descriptions available through MCP (Supplementary Figure 5).

In the nuclear-segmentation example, a source mapping selects the nuclear channel at each site. Step settings choose Z stacks or individual planes and divide images into processing groups. Grouping by channel lets nuclear and neuronal images use different function chains. Later steps inherit source choices or select different inputs; measurements remain linked to their source images and metadata. Sample, site, channel, plane and time coordinates are recorded separately from storage locations, preserving image identity through stacking and later processing.

Microscope handlers interpret acquisition-specific layouts and metadata. Bio-Formats-backed discovery provides image-plane records from microscopy containers. The OME-Zarr source reads declared axes, channels, pixel scale and image or plate structure. Explicit source mappings assign roles where acquisition metadata are insufficient. Experimental OMERO support supplies managed images and metadata through the same source model.

### Execution, intermediate results and viewers

Each result keeps its connection to the images and processing step that produced it. Steps produce named images, labels, measurements, object relationships and files. For example, a measurement can remain associated with the segmented nucleus it describes. Each function declares its required inputs and available outputs; the compiler connects later operations to the source images or earlier results they need. Named results retain their producing step, source coordinates and processing group. Saving a result and sending it to a viewer are independent choices (Supplementary Figure 4).

napari and Fiji receive selected outputs together with their source coordinates and producing step. The streaming service checks that each viewer is ready and waits for pending display updates to finish. Viewer sessions remain available for inspection after execution. Local files, in-memory data, Zarr-backed stores and OMERO provide storage routes; the OME-Zarr array source is read-only.

The execution server coordinates analysis runs and remains available between requests. Within a run, each worker processes its assigned samples using the prepared plan and reuses loaded libraries and initialized array backends. Worker resources are released when that execution finishes. Worker count controls how many samples can be processed concurrently. Workers normally run in separate processes; a configuration option selects threads instead.

### Agent access through MCP

Through MCP, an AI client requests defined operations for discovering functions, editing and validating pipelines, running analyses, and inspecting progress and results [@MCP]. Each operation's declaration specifies its request and result types, implementation, changes it can make, data access and security requirements. The MCP interface is generated from these declarations, which also govern execution.

Function-discovery operations return descriptions derived from registered processing functions. An agent uses those descriptions to select functions and edit the shared workflow. Registering an additional function makes it available through the existing catalog and workflow operations without requiring a function-specific MCP tool.

Deployment profiles determine which operations are available. Desktop operations edit and run workflows in the live application; headless operations run without the graphical interface in a separate execution context. Local clients communicate with the MCP server through standard input and output. Desktop access uses an authenticated connection, and revision checks detect edits based on an outdated workflow state. Filesystem reads and writes are restricted to permitted locations. The hosted HTTP service provides a selected read-only subset in isolated server-side workspaces.

### Reusable workflow infrastructure

The mechanisms that turn declarations into interfaces and coordinate execution are packaged for reuse independently of the microscopy functions (Table 1). Eight libraries discover implementations, read function definitions, track settings, generate controls and Python, convert arrays, route stored results and coordinate processes. OpenHCS supplies the microscopy functions, configurations, source handlers and viewer integrations. New processing functions use these shared mechanisms when they enter the workflow.

**Table 1. Reusable libraries and their roles in the shared workflow.**

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

### Agent-operated analysis

The recorded run used Codex 0.146.0 with gpt-5.6-sol on Linux, connected by local stdio MCP to the desktop profile of OpenHCS 0.7.13 in a source-checkout virtual environment. The input was field 1 from the public NeuronCyto II dataset [@NeuronCytoII], comprising two 800 x 800-pixel, unsigned 8-bit TIFF images. Both were assigned to one biological image, with separate neuronal/neurite and soma/nuclear channels. Supplementary Data 4 identifies the software revision, input checksums and exact task prompt.

The prompt requested normalization, dim-neurite enhancement, segmentation and per-neuron morphology measurements, with saved images, regions of interest (ROIs), graph paths, SWC neuron-morphology files, tables and a reviewable napari presentation. It authorized changes to a dedicated desktop session and writes under the stated output directory, and instructed the agent not to use shell commands or inspect the repository. The client's approval checks and operating-system sandbox were disabled for this run. Compliance with the MCP-only instruction was assessed from the tool trace: no non-MCP calls or subsequent human interventions were recorded.

The event trace was used to count attempted calls, returned errors and subsequent corrections (Supplementary Data 4). Agent wall time was measured from the recorded start and end timestamps; pipeline execution time was reported separately. Checks covered completed execution, saved files, editable pipeline source, and delivered viewer outputs and coordinates. Subsequent review examined the saved object outlines and the published NeuronCyto II manual-tracing measurements for image 1 [@NeuronCytoII]. Supplementary Data 4 records these reference values separately from the agent's execution checks; object-level segmentation and tracing accuracy remain to be scored.

### Prospective agent-authored assay evaluation

Three public BBBC assays were prepared before separate pipeline-authoring trials. A fresh gpt-5.6-sol agent received a bounded development partition, the biological task, channel identities, the OpenHCS desktop and MCP endpoints, and a result directory. Reference annotations, treatment metadata, held-out images, evaluation code, prior trial pipelines and repository source were withheld. The agent used registered functions through the connected desktop. Its scientific functions and parameters were frozen before the held-out path was disclosed; the held-out run changed only the input and result roots. These are single prospective attempts rather than repeated estimates of agent reliability. The corpus manifest binds the original archives, converted inputs, partition assignments and evaluation artifacts (Supplementary Data 7).

BBBC039 supplied four development and 50 held-out fields with independent nuclear instance annotations. One-to-one matching used an intersection-over-union threshold of 0.5; reported measures include object precision, recall and F1, foreground Dice, signed count error, and explicitly defined split and merge diagnostics. BBBC007 supplied four development and 12 held-out DNA/actin fields with manual outlines. Its directed boundary measure reports the fraction of predicted adjacent-cell boundary pixels within two pixels of the manual-outline union. The outlines do not provide exhaustive object correspondence, so this score is not an instance-accuracy estimate.

BBBC013 supplied four development and 92 held-out wells from a two-drug FKHR-GFP translocation assay. The frozen endpoint was the per-well mean of cell-level mean nuclear GFP divided by mean cytoplasmic GFP. Each cell required the same retained object identity in the nuclear and cytoplasmic measurements. Z-prime used sample standard deviations across the four positive and four negative control wells for each drug; cells were not treated as independent replicates. BBBC013 provides treatment truth rather than manual segmentation truth. Prediction bytes were frozen before the evaluator opened held-out annotations or treatment metadata. The exact pipelines, typed score receipts, limitations and infrastructure repairs are retained in Supplementary Data 7.

### CellProfiler import and reference-output comparison

CellProfiler `.cppipe` files are parsed into modules and settings. Setup modules define image sources; registered processing and export modules become editable OpenHCS steps. Each module declaration specifies the images, objects, measurements and relationships its function needs, together with whether it runs per image group or across the plate. The same function is exposed in the GUI, Python and MCP.

The imported ExampleCometAssay illustrates this mapping. Its 16 modules become image-source configuration and 12 processing steps containing 16 function calls. One step measures the size and shape of three named object sets: Comet, CometHead and CometTail. Another defines CometTail by masking the comet with the inverted head mask. These names connect each measurement to the object set it describes.

Two additional workflows illustrate larger imports: the advanced segmentation tutorial and the 3D monolayer tutorial [@CellProfilerTutorials]. Enabled modules were parsed from the benchmark pipeline files, translated using the importer, and counted alongside their generated function steps and individual calls. The imported Python documents were reloaded to check preservation of function identities and parameters. Supplementary Data 5 provides the complete step sequences and source records; output comparisons are reported separately below.

Imported `ExportToDatabase` modules run once per plate after image-group processing. They collect the selected images, objects, measurements, relationships, thumbnails and grouping information into CellProfiler Analyst tables [@Jones2008]. The export produces a self-contained SQLite database and matching `.properties` files. Non-SQLite databases, custom filter rows, `.workspace` generation and some historical aggregation settings remain unsupported; unsupported requests fail or are identified in the compatibility documentation.

Automated testing for the OpenHCS 0.8.5 release checked execution of all 30 imported workflows and compared selected outputs for the 25 with retained CellProfiler-produced reference values. The continuous-integration (CI) job built installable packages from the release source and its dependencies on Linux with Python 3.12. It acquired the workflows and image sets at the revisions specified in the benchmark manifest, then compiled and executed each imported workflow through the execution server. Every OpenHCS analysis ran afresh. The historical release test required 30 successful execution records and no differences in its selected comparisons. Supplementary Data 1 preserves the per-workflow observations, run metadata and tested revision.

The manifest selects exported values for comparison. CSV tables and CellProfiler Analyst SQLite tables and `.properties` values are checked. Image comparison selects files, including NumPy arrays, from native reference-output directories that contain images and no CSV files. This includes the NPY-only illumination workflow and the completed translocation tutorial's overlay alongside its SQLite measurements. Images accompanying CSV measurements in 14 profiles remain outside image comparison. Absolute and relative tolerances are `1e-6` for numeric values and image pixels, with no pixels allowed outside tolerance; identifiers and categorical values are compared exactly after documented CellProfiler-compatible normalizations.

For the five workflows without file exports, terminal image or object-label exports were appended while preserving the original processing modules and settings. Native CellProfiler generated eight additional reference artifacts. A subsequent unified run compiled and executed all 30 workflows afresh and compared each candidate with its selected native reference values. Object labels were compared exactly after singleton-axis normalization; numerical images used the stated float tolerances. The unified run used OpenHCS 0.8.5 current source on Python 3.12.3 with NumPy 2.1.3 and SciPy 1.18.1. Native references used CellProfiler 4.2.8.1 on Python 3.9.25 with NumPy 1.24.4 and SciPy 1.9.0. Supplementary Data 1 links the export definitions, reference inventory, per-workflow comparisons and exact source identities separately from the historical release CI records.

The corpus contains 22 workflows and associated image sets from the official CellProfiler 3 examples repository, seven workflows and image sets from the official CellProfiler tutorials repository, and one workflow from the supplement to the CellProfiler 4 performance study [@CellProfilerExamples; @CellProfilerTutorials; @Stirling2021]. The CellProfiler project and the cited dataset contributors retain authorship and provenance for these materials. The retained manifest maps workflow names to pipeline and image locations; Supplementary Data 1-3 provide the corresponding comparison, coverage and throughput tables.

### Performance measurements and reproducibility

Archived May development runs measured throughput and peak memory by assigning the same source images to multiple well identifiers, creating repeated analysis work (Table 2). Queue depth specifies how many assignments were supplied per configured worker. Each condition has one recorded run per workflow. The retained rows report completed assignments but do not preserve worker-process traces or per-run output inventories.

**Table 2. Performance experiments across the 30 workflows.**

| Measurement | Varied | Held fixed |
| --- | --- | --- |
| Completed assignments per execution second | 2, 3, 4 workers | 4 assignments per worker |
| Peak memory | 1, 2, 3, 4, 6, 8 assignments per worker | 4 workers |

Throughput uses execution time after initialization and compilation. The recorded configuration disables default saving of named results and return of detailed worker records, and requests removal of unused steps whose outputs are not saved. Supplementary Data 3 identifies these settings, the individual runs and the limits of their historical output-policy provenance. These rows characterize that archived analysis-focused workload, not the current output-complete CellProfiler translation. Measurements cover CPU execution on local or explicitly mounted image sources; GPU and cloud or network-storage performance were not measured.

The archived single-sample benchmark specifies one thread/core, CPU-only execution and no batching, with one retained comparison observation per workflow. The harness committed with the tables times the native CellProfiler command from subprocess launch through completion, including its startup. It times OpenHCS execution after initialization and compilation. Total-phase values also include different work, including benchmark validation and comparison on the OpenHCS path. Supplementary Figure 6 and Supplementary Data 1 report these observations with their timer definitions; they do not establish a like-for-like speed comparison. The wound-healing native duration equals the 900-s timeout ceiling without an explicit completion flag and is excluded from timing statistics.

The supplementary package separates the release CI comparison records from the earlier performance measurements. Its software-snapshot table identifies the revision and evidence for each evaluation. Figure scripts regenerate panels from saved CSVs and record source and output checksums. Supplementary Data 6 links automated tests of workflow editing and pre-execution validation to their source and CI jobs.

## Results

### One executable workflow retains analysis state across tools

The desktop interface, generated Python and MCP operations read and modify the same workflow definition (Figure 1). A pipeline created by an agent can be opened in the editor, revised by a scientist and run again. Source mappings connect folders, Bio-Formats containers and managed images to named inputs. Intermediate images and measurements retain their source coordinates and producing step, allowing a displayed result to be traced back to its processing choices.

A recorded authoring check demonstrates this connection directly (Figure 2). An MCP request applied edited Python to the normalization step, changing its high percentile from 99.8 to 99.6; the control then showed 99.6. A subsequent MCP field-edit request restored 99.8, and regenerated Python contained that value. The full application view, parameter controls and function-code window were captured in the same session, using the source commit released as OpenHCS 0.8.5. Forms show the values that will be used, including shared defaults; clearing a step's override restores its shared setting.

Automated regression tests check nested configuration, inherited defaults, parameter order and function-step reconstruction through generated Python. Separate tests reject incompatible array, grouping and stack requirements before execution, and reject function-detail requests based on an outdated catalog revision. Supplementary Data 6 identifies the tested cases and successful CI jobs.

Stacking, grouping and scheduling express different choices. A step can assemble Z planes into an array, apply different function chains to different channels, and supply named segmentation labels to a later measurement step. When time is configured as sequential, the entire pipeline finishes for one timepoint before the next begins; separate wells can run in parallel (Supplementary Figure 1). Each selected function determines its array-library support and whether it processes individual planes, whole stacks or reduces a stack to an output.

The UI submits work to a separate execution server using ZeroMQ messaging. The server compiles the workflow and coordinates workers. Workers execute the prepared steps and stream selected results to separate napari or Fiji processes, while progress returns through the server to the UI (Supplementary Figure 2).

### Figure 2. Forms, Python and MCP edit the same analysis

![Matching main window, recorded MCP edits, parameter controls and Python code.](figures/slas/editable_analyses.png){width=6in}

\(A) Full NeuronCyto II main window, with enlarged step and connection details. (B) MCP applies edited Python to the step and checks the updated control, then edits the field and checks regenerated Python. (C, D) Same-session crops show matching controls and code, with high percentile restored to 99.8 and parameters in signature order. Captures use OpenHCS 0.8.5; Figure 3 shows the current replay and retained measurements.

### An agent builds and inspects a neurite-outgrowth workflow

From a detailed prompt identifying the two NeuronCyto II channels and requested outputs, the agent built and inspected a neurite-outgrowth analysis without further human input.

The agent inspected the images' organization and constructed a two-step pipeline: normalization followed by a registered neurite morphology and topology function (Figure 3). Of 140 attempted MCP calls, one was rejected for an invalid operation name; 30 others returned an error from the requested operation. Seventeen of those 30 errors came from code-document validation, which rejected invalid preset imports, document structure or configuration values before analysis execution. These counts include repeated authoring attempts. The agent revised the document until validation succeeded, then compiled and ran it in the desktop session. The remaining errors concerned request formats, discovery, file queries and UI operations (Supplementary Data 4). The saved record reports 609 s from start to completion, including authoring, corrections, execution and agent output checks; pipeline execution took 16.5 s. Outputs included neuron and nuclear labels, per-neuron measurements, neurite paths, ROI files and an SWC morphology file. The pipeline remained editable in Python and the graphical interface.

The final napari view displayed enhanced neuronal signal, unified neuron labels and neurite paths, with a feature table linking paths to measurements. Structured viewer checks found all nine expected outputs present with no missing or duplicate coordinates. The original analysis reported nine neurons, ten nuclei and 25 graph paths. Subsequent visual review identified a crossover classified as branching and a soma split between two neuron labels. The retained outlines also divide the nuclear signal at that soma into three objects. The published manual-tracing table lists eight neurons for image 1, providing an independent reference for investigating the count discrepancy [@NeuronCytoII].

A separate current-source replay used nuclear-supported soma detection and soma-rooted path assignment. It produced eight cell bodies, eight nuclei, 18 processes, two branch events and 24 graph paths. Per-cell measurements agree with graph distance features, totaling 2556.137 pixels under unit spacing. Supplementary Data 4 retains the original run, intervening correction and current replay separately. Document validation caught invalid authoring attempts before execution; image review identified errors in the biological result.

### Figure 3. Agent-authored neurite workflow and current-source review

![Original inputs, current native viewer inspection and retained neurite measurements.](figures/slas/figure3_agent_workflow.png){width=6in}

(A, B) Original 800 x 800-pixel NeuronCyto II field-1 inputs [@NeuronCytoII], displayed linearly over their unsigned 8-bit range. The boxes name the two saved pipeline functions. (C) Native napari capture of the current replay, combining neuronal signal, unified labels and graph paths; selecting neuron 8 links its three paths. (D) Retained nucleus, soma and assigned-neuron labels for the lower field cell, shown in magenta, cyan and yellow, respectively. Label identities are matched by pixel overlap. (E) Crossing paths remain assigned to separate neurons. (F, G) Per-neuron and summary measurements derived from the retained tables. Lengths are pixels because the public input has no recorded physical calibration. The original unattended run remains separately retained in Supplementary Data 4.

### Frozen workflows recover held-out assay structure

The three prospectively authored workflows were applied without scientific parameter changes after their held-out partitions were disclosed (Supplementary Figure 7 and Supplementary Data 7). On the 50 BBBC039 fields, 4,733 of 5,720 reference nuclei matched at intersection over union at least 0.5. Pooled precision was 0.680, recall was 0.827 and object F1 was 0.746; mean field foreground Dice was 0.935. The workflow predicted 6,964 nuclei, 1,244 more than the reference, and the overlap diagnostic identified more split reference instances than merged predictions. The first blind pipeline therefore recovered nuclear foreground well while over-segmenting instances.

On the 12 BBBC007 fields, 29,450 of 43,875 relevant predicted adjacent-cell boundary pixels were within two pixels of a manual outline, a pooled fraction of 0.671. The workflow predicted 1,274 nuclei and 1,273 cells; every predicted nucleus overlapped a cell and one cell shared two nuclei. The manual outlines enclosed 1,082 closed nuclear interiors, while 12 open or frame-connected regions were excluded. Because the boundary score is directed from predictions to the outline union, it can reward an incomplete segmentation and does not establish object correspondence.

The BBBC013 run produced matched nuclear and cytoplasmic measurements for 14,262 cells across all 92 held-out wells. Wortmannin controls separated with Z-prime 0.751 and mean nuclear-to-cytoplasmic GFP ratios of 7.235 and 0.915 for positive and negative controls. LY294002 controls gave Z-prime 0.554 and means of 7.219 and 1.127. Both held-out dose series showed the expected increase in nuclear translocation. This result evaluates recovery of the assay response; BBBC013 does not supply manual masks with which to score segmentation.

### Imported CellProfiler workflows match the compared reference outputs

All 30 workflows passed selected reference-output comparisons in one unified current-source run, with zero reported differences. The selected reference profiles comprised 21 with CSV measurements, three with SQLite measurements and CellProfiler Analyst properties, and six containing only retained images or arrays. The five supplemented workflows contributed five object-label images and three numerical images. All five label images matched exactly after singleton-axis normalization, and all three numerical images passed with zero out-of-tolerance pixels. Supplementary Data 1 identifies every selected output and preserves the unified observations and source identity.

Image comparison executed for seven workflows: six image- or array-only profiles and the completed translocation example, whose overlay was compared alongside its SQLite measurements. Figure 4 shows how named images, objects and operations are retained in the imported Comet Assay.

The assays include DNA-damage measurement, human and Drosophila cell morphology, tumor morphology, Cell Painting morphology and quality control, protein translocation, wound healing, time-lapse tracking, imaging flow cytometry, colocalization, positive-cell classification, yeast screening, and *C. elegans* phenotyping. Supplementary Data 1-2 identify the workflows and imported settings.

The archived coverage tables list 58 distinct module names and 7,158 setting rows. They record whether a setting supplies a function parameter, an input/output requirement, an infrastructure option, or is intentionally ignored. Coverage describes how configurations are imported; the comparison results assess their outputs. Database export remains an ordinary terminal workflow step, using the same measurements and source identities as preceding steps.

### Figure 4. A familiar CellProfiler pipeline expressed as OpenHCS steps

![CellProfiler modules, imported function steps and named-object relationships.](figures/slas/cellprofiler_translation.png){width=5.8in}

\(A) The public ExampleCometAssay pipeline maps image loading to source bindings and processing to 12 function steps. Rows align original modules and imported functions; multiplicity marks repeated calls. Spreadsheet export runs plate-wide. (B) MeasureObjectSizeShape applies the same function to Comet, CometHead and CometTail within one step. (C) Masking the comet with its head, with inversion enabled, defines CometTail. The diagram is derived from the source pipeline and importer; function identities, parameters and counts are checked against its retained mapping.

### Complex workflows retain their processing and measurement structure

The advanced segmentation tutorial corrects illumination in five channels and identifies nuclei, cells, cytoplasm, nucleoli and mitochondria. Its 23 enabled modules become 16 steps containing 59 function calls (Supplementary Data 5). Measurements include colocalization, intensity, radial intensity distribution, size and shape, and neighbors. Object relationships associate nucleoli with nuclei and mitochondria with cells before SQLite export. Repeated channel/object measurements become function lists within a step, retaining the selected inputs and parameters.

The 3D monolayer tutorial segments nuclei and cells in volumetric images. It combines resizing and filtering, hole filling, nuclear watershed segmentation, seed preparation and cell watershed segmentation, followed by intensity and shape measurements, overlays, label-image saving and spreadsheet export. Its 35 enabled modules become 31 steps containing 35 function calls. Both workflows passed their selected output comparisons in release CI. The separate authoring checks preserved their function identities and parameters through generated Python.


### Throughput and memory across worker counts and queue depths

In the archived analysis-focused repeated-input runs over all 30 workflows, median throughput with four assignments per configured worker was 1.79, 2.67 and 2.96 completed assignments per execution second at configured maxima of two, three and four workers, respectively (Figure 5A). Every assignment was recorded complete. These rates do not establish throughput for the later output-complete translation; Supplementary Data 3 retains the individual historical rows and their provenance limits.

Each worker uses memory for imported libraries, cached arrays, and intermediate outputs. Across all 30 OpenHCS workflows in the four-worker queue-depth sweep, median peak RAM increased from 3.89 GiB at one assignment per worker to 4.15 GiB at eight assignments per worker, with maximum peak RAM reaching 14.3 GiB. Memory summaries include the wound-healing workflow because its OpenHCS run completed; only comparisons requiring its native CellProfiler timing exclude it. In these runs, more workers increased median throughput, while memory requirements varied substantially between workflows.

### Figure 5. Measured OpenHCS throughput and memory use

![Archived benchmark measurements.](figures/slas/figure2_benchmarks.png){width=5.5in}

\(A) Completed repeated-image assignments per execution second with four assignments per configured worker. (B) Peak memory with four configured workers and increasing assignments per worker. Each point is one of the 30 workflows, shaded boxes span the interquartile range, vertical lines span the observed range and black lines mark medians. Every assignment was recorded complete. These archived analysis-focused runs follow compilation, disable default named-result saving and detailed worker records, and request removal of unused unsaved-output steps. They do not measure the later output-complete translation. Throughput uses a logarithmic axis. Supplementary Figure 8 shows the same observations by workflow; Supplementary Figure 6 presents the separate historical single-sample timings.

### Inspecting results in Fiji and napari

Figure 6 shows streamed images and objects in both viewers. napari additionally exposes structured image, layer and ROI information for agent inspection; Supplementary Figure 4 links a selected object to its saved measurements and viewer features. Fiji provides native image and ROI display with a smaller programmatic inspection interface.

### Figure 6. Image and object inspection in Fiji and napari

![Recorded image and ROI inspection in two viewers.](figures/slas/inspectable_results.png){width=5.5in}

\(A) Fiji displays a single NeuronCyto II field 1 nuclear plane with nine corresponding native ROI Manager entries. (B) A separate three-plane napari demonstration shows segmented objects, a selected ROI-list entry and the displayed channel/Z coordinates. Its accompanying recording shows selection navigating between planes. These are retained viewer demonstrations, separate from the unattended analysis in Figure 3; their segmentation outputs are not compared with each other. Details enlarge the ROI entries and a nuclear outline in A, and the selected object, highlighted list entry and coordinates in B. The full captures and checksum records are retained in the gallery archive.

## Discussion

OpenHCS connects interactive and agent-operated microscopy analysis through a shared workflow definition. Parameter controls, editable Python and catalog descriptions draw on the registered functions, while the compiler combines their requirements with configuration and selected images. A scientist can therefore revise the same pipeline that an agent constructed.

Workflow reuse can reduce the setup required for a new experiment. A laboratory can import a CellProfiler analysis, adjust its source mapping and parameters, add an assay-specific Python function, and inspect the resulting masks in Fiji or napari before processing further samples. Pipelines can also be authored directly in OpenHCS. Keeping the processing choices explicit provides a basis for review as analysis methods and experimental conditions change.

The evaluations cover complementary parts of this workflow. The unified current-source run establishes selected reference-value agreement across all 30 imported workflows, while the release CI record independently preserves package-level execution for the released source. The single-field neurite demonstration records completion under one prompt and client/model configuration; image review then exposed cell-assignment and crossover errors despite successful execution checks. Three prospective trials extend evaluation to held-out annotations or treatment structure. They show useful first-attempt results while also identifying nuclear over-segmentation and the limits of directed boundary and treatment-level references. Because each assay used one authoring attempt with one model and prompt, they do not estimate the probability that an agent will produce an acceptable workflow on a new assay. The separate archived throughput measurements describe a configured analysis-focused workload, not current output-complete performance; matched native CellProfiler throughput remains to be established.

Further evaluation can extend reference comparisons to additional modules and settings, compare repeated agent trials with expert-reviewed results, and measure paired CellProfiler/OpenHCS throughput with matched outputs and resource limits. Explicit image-source mappings keep channel and dimensional choices available for review as pipelines move to new experiments. The reusable libraries in Table 1 supply the supporting mechanisms independently of the microscopy functions.

OpenHCS provides an analysis component for AI-guided laboratories in which established workflows, custom functions and intermediate results remain accessible through the same editable pipeline. Scientists can delegate pipeline construction and execution, then inspect the results in familiar viewers and revise the analysis through graphical controls or Python.

## Supplementary Data

The [supplementary index](supplementary/README.md) links the retained files and describes their fields and interpretation.

1. **CellProfiler workflow comparison:** unified 30-workflow current-source observations, reference inventory and exact run provenance; historical OpenHCS 0.8.5 release-CI evidence; the five-workflow export definitions and per-artifact audit; and separate historical timing records.
2. **CellProfiler coverage:** module-to-workflow associations, individual setting handling, and archived processing-registration coverage.
3. **Worker and memory measurements:** measured execution and memory by workflow, worker count and repeated-image assignment count, including completion status.
4. **Recorded agent workflow:** evaluated client, model and software versions; input checksums; exact prompt; tool trace and error counts; original outputs; and separately identified later corrections.
5. **Complex CellProfiler workflows:** source-derived step sequences, function-call counts and editable Python for advanced segmentation and 3D monolayer analysis.
6. **Workflow regression tests:** representative configuration, generated-Python and compiler-validation checks, with source and CI-job references.
7. **Prospective agent-authored assays:** frozen pipelines and held-out score receipts for BBBC039, BBBC007 and BBBC013, with quantitative results and operational findings.

## Code and Data Availability

OpenHCS source code: <https://github.com/OpenHCSDev/OpenHCS>.

OpenHCS documentation: <https://openhcs.readthedocs.io/>.

Benchmark scripts and records are indexed in the [supplementary data](supplementary/README.md). Figure-generation scripts and figures are located under `paper/figures/` in the source repository.

The benchmark uses biological images and pipelines distributed by the CellProfiler project rather than OpenHCS-authored benchmark data. Original sources:

- official CellProfiler example pipelines and images: <https://github.com/CellProfiler/examples> [@CellProfilerExamples]
- official CellProfiler tutorial pipelines and images: <https://github.com/CellProfiler/tutorials> [@CellProfilerTutorials]
- CellProfiler 4 benchmark supplement: <https://github.com/carpenterlab/2021_Stirling_BMCBioInformatics> [@Stirling2021]

The benchmark manifest maps workflows to pinned revisions of their source collections. The [unified comparison evidence](../benchmark/results/official30_unified_value_comparison_20260916/README.md) preserves current-source observations, the selected reference inventory and exact run provenance for all 30 workflows. The [release CI evidence](supplementary/ci_official30_085/README.md) separately preserves the OpenHCS 0.8.5 package-level test, with checksums and links to its exact source revision and hosted job. Historical performance records and separately versioned agent demonstrations are indexed alongside them.

Table 1 links the source repositories for the eight reusable libraries.

## Acknowledgements

We thank the CellProfiler project, its contributors, and the authors of the underlying biological datasets for making the example, tutorial, and benchmark materials available.

## Author Contributions

[To be confirmed by the authors: assign contributions to the final author list.]

## Funding

[To be confirmed by the authors: list applicable funding bodies, grants and fellowships, or confirm that no specific funding supported this work.]

## Declaration of Competing Interests

[To be confirmed by the authors: disclose relevant financial or personal relationships, or confirm that there are no competing interests to declare.]
