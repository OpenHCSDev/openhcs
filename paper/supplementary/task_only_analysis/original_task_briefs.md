### Original scientific briefs

The following retained scientific instructions are reproduced verbatim, including technical hints and operational restrictions. Identical texts are shared across trials; the [complete instruction archive](task_only_analysis/original_task_briefs.json) retains operational TASK files and exact byte hashes, mapping every retained trial to its documents. These instructions demonstrate the supplied task context, not usability with untrained scientists or proof that every instruction was followed.

The public assay briefs supply typed source bindings, catalogue tracks and output contracts. BBBC007 explicitly requests seeded cell segmentation; BBBC013 specifies nuclear versus cytoplasmic GFP measurement. Optional registered-custom tracks are also supplied, although their presence does not establish that an author used them. The H003 brief directs `SourceBindingsConfig` pairing. Neurite briefs request crossing review; the thick-shaft-only target was clarified later, not supplied retrospectively. Some historical packets contain resource caps subsequently removed from the programme. They are reproduced as history, not current requirements.

#### Brief 1: BBBC007_cell_boundaries blind OpenHCS authoring surface

Trials: `BBBC007_FRESH651_88`; `BBBC007_FRESH08_96`; `BBBC007_FRESH10_ROTATION_89`; `BBBC007_RETAINED_DEV13_94`; `BBBC007_FRESH19_95`; `BBBC007_FRESH26_96`.

Technical guidance: explicit source bindings, catalogue authoring tracks, typed artifact requirements and freeze procedure; optional custom-registration tracks where stated. These are not method-free briefs.

> \# BBBC007_cell_boundaries blind OpenHCS authoring surface
>
> Use this directory as the complete filesystem mount for the authoring agent.
> It contains inputs and public metadata only. Manual references, accepted metric
> values, and the trusted scorer are deliberately outside this tree.
>
> \## OpenHCS DSL contract
>
> - Source components: well, site, channel
> - Grouping metadata: `well`
> - Variable components: site
> - Source sets: 16
> - Source planes: 32
> - Source bindings: import `source_bindings_config` from `source_bindings.py`.
> - Preserve typed artifacts and materialization declarations in the frozen pipeline.
>
> The compiled dimensional transitions expected from the source declaration are:
>
> - source planes {well, site, channel} -> named channel bindings per source set
> - bound image arguments -> image/label artifacts retaining {well, site}
> - label artifacts -> object tables keyed by source set and object label
> - per-source artifacts -> declared materialization paths and plate summaries
>
> \## Authoring tracks
>
> - `catalog_seeded_cell_segmentation` (catalog): Use paired DNA and actin bindings to segment nuclei and seeded cells with catalogue functions and materialize both label sets. Expected artifacts: nucleus_labels, cell_labels.
> - `typed_sparse_jaccard_extension` (registered_custom): Register a typed sparse-reference comparison function, expose it through the same reflected UI/MCP catalogue, and materialize its metric table. Expected artifacts: sparse_metric_table.
>
> For a registered-custom track, add a typed function through OpenHCS registration
> so its signature drives the UI, Python document, MCP schema, and compiler. Do not
> inject code into a viewer or bypass the pipeline runtime.
>
> Freeze the final pipeline before the trusted scoring surface is mounted. Preserve
> every authoring attempt, compile refusal, generated source file, materialized
> artifact, MCP event record, and multi-percentile raw/result overlay.

#### Brief 2: Paired DNA and actin: full released sixteen-source collection

Trials: `BBBC007_FRESH19_95`.

The full retained instruction is reproduced below; no successful-run method has been substituted for it.

> Paired DNA and actin: full released sixteen-source collection
> \============================================================
> Use only the declared BBBC007 public images and source_manifest/source_bindings pairing. Inspect physical channels and source axes through MCP. Produce nucleus and seeded-cell labels, per-object tables and qualified image-level summaries across all sixteen sources using a complete PipelineDocument. Without verified physical calibration, retain pixel-native geometry.
> Choose your own method from measurements and packaged guidance. Preserve FIRST separately from scientific repairs and technical retries. Perform matched distributed raw/result/combined QA including faint, crowded, sparse and background controls. No method, settings, expected count or crops are supplied. Manual references, scorers, notebooks and earlier-agent outputs are withheld until scientific freeze.

#### Brief 3: BBBC013_u2os_translocation_bmp blind OpenHCS authoring surface

Trials: `BBBC013_REPEAT94`; `BBBC013_DEV02_94`; `BBBC013_DEV89`; `BBBC013_REMEDIATION02_89`; `BBBC013_FRESH13_88`; `BBBC013_FRESH15_96:01a10d07-78ae-7ac3-b98c-fd27a48fee37`; `BBBC013_FRESH15_96:01a10d7c-7c64-79f2-8988-3c12cb208ef8`; `BBBC013_FRESH20_88`; `BBBC013_FRESH23_96`.

Technical guidance: explicit source bindings, catalogue authoring tracks, typed artifact requirements and freeze procedure; optional custom-registration tracks where stated. These are not method-free briefs.

> \# BBBC013_u2os_translocation_bmp blind OpenHCS authoring surface
>
> Use this directory as the complete filesystem mount for the authoring agent.
> It contains inputs and public metadata only. Manual references, accepted metric
> values, and the trusted scorer are deliberately outside this tree.
>
> \## OpenHCS DSL contract
>
> - Source components: well, site, channel
> - Grouping metadata: `well`
> - Variable components: none
> - Source sets: 96
> - Source planes: 192
> - Source bindings: import `source_bindings_config` from `source_bindings.py`.
> - Preserve typed artifacts and materialization declarations in the frozen pipeline.
>
> The compiled dimensional transitions expected from the source declaration are:
>
> - source planes {well, site, channel} -> named channel bindings per source set
> - bound image arguments -> image/label artifacts retaining {well, site}
> - label artifacts -> object tables keyed by source set and object label
> - per-source artifacts -> declared materialization paths and plate summaries
>
> \## Authoring tracks
>
> - `catalog_translocation_measurement` (catalog): Segment nuclei/cells from paired DNA and GFP planes, measure nuclear versus cytoplasmic GFP, and materialize per-cell and per-well tables. Expected artifacts: nucleus_labels, cell_labels, cell_table, well_table.
> - `typed_plate_statistics_extension` (registered_custom): Register a typed plate-statistics function over the per-well table and materialize dose-response, Z-prime and replicate-SD V-factor outputs. Expected artifacts: assay_statistics, dose_response_table.
>
> For a registered-custom track, add a typed function through OpenHCS registration
> so its signature drives the UI, Python document, MCP schema, and compiler. Do not
> inject code into a viewer or bypass the pipeline runtime.
>
> Freeze the final pipeline before the trusted scoring surface is mounted. Preserve
> every authoring attempt, compile refusal, generated source file, materialized
> artifact, MCP event record, and multi-percentile raw/result overlay.

#### Brief 4: BBBC039_nuclei_segmentation blind OpenHCS authoring surface

Trials: `BBBC039_FRESH594_88`; `BBBC039_FRESH612_96`; `BBBC039_FRESH656_88`; `BBBC039_FRESH08_88`; `BBBC039_FRESH10_COVERAGE_96`; `BBBC039_FRESH13_88`.

Technical guidance: explicit source bindings, catalogue authoring tracks, typed artifact requirements and freeze procedure; optional custom-registration tracks where stated. These are not method-free briefs.

> \# BBBC039_nuclei_segmentation blind OpenHCS authoring surface
>
> Use this directory as the complete filesystem mount for the authoring agent.
> It contains inputs and public metadata only. Manual references, accepted metric
> values, and the trusted scorer are deliberately outside this tree.
>
> \## OpenHCS DSL contract
>
> - Source components: plate, well, site, channel
> - Grouping metadata: `plate, well`
> - Variable components: none
> - Source sets: 200
> - Source planes: 200
> - Source bindings: import `source_bindings_config` from `source_bindings.py`.
> - Preserve typed artifacts and materialization declarations in the frozen pipeline.
>
> The compiled dimensional transitions expected from the source declaration are:
>
> - source planes {plate, well, site, channel} -> named channel bindings per source set
> - bound image arguments -> image/label artifacts retaining {plate, well, site}
> - label artifacts -> object tables keyed by source set and object label
> - per-source artifacts -> declared materialization paths and plate summaries
>
> \## Authoring tracks
>
> - `catalog_instance_segmentation` (catalog): Author and visually debug a catalogue-only DNA instance-segmentation pipeline, then materialize one label image and object table per field. Expected artifacts: instance_labels, object_measurements.
>
> For a registered-custom track, add a typed function through OpenHCS registration
> so its signature drives the UI, Python document, MCP schema, and compiler. Do not
> inject code into a viewer or bypass the pipeline runtime.
>
> Freeze the final pipeline before the trusted scoring surface is mounted. Preserve
> every authoring attempt, compile refusal, generated source file, materialized
> artifact, MCP event record, and multi-percentile raw/result overlay.

#### Brief 5: H001 — bright-object segmentation

Trials: `H001_FRESH10_96`; `H001_FRESH586_96`; `H001_FRESH19_89`; `H001_FRESH22_96`; `H001_FRESH25_FOURTH_95`; `H001_FRESH25_ROTATION_94`.

Technical guidance: 2-D instance labels, pixel areas, counts and matched regional review; no segmentation algorithm or parameter values.

> \# H001 — bright-object segmentation
>
> Use only `image.tif` in this directory as scientific input. Build an OpenHCS
> PipelineDocument that produces a 2-D instance-label image, per-object area in
> pixels, and an image-level object count. Keep every attempt and execution
> receipt in your own trial output directory. Inspect the raw image and final
> labels together at identical native coordinates in several separated regions
> and more than one intensity window; record clear positives, misses, splits,
> merges and an explicit accept/reject decision. Do not infer physical units
> without verified calibration. Freeze the complete pipeline and outputs before
> evaluation.
>
> Do not inspect source notebooks, repository plans, external reference files,
> other agents' outputs, or public expected results. Use OpenHCS MCP for
> scientific inspection, execution and viewer operations; do not inject mouse
> or keyboard events.

#### Brief 6: H002 — 3-D centre detection

Trials: `H002_CAPACITY_DEV94`; `H002_FRESH651_95`; `H002_FRESH656_96`; `H002_FRESH10_89`; `H002_FRESH10_ROTATION_96`; `H002_FRESH13_89`; `H002_FRESH15_89`; `H002_FRESH22_89`; `H002_FRESH23_ROTATION_89`.

Technical guidance: a 3-D volume, z/y/x voxel-coordinate outputs and orthogonal multi-window review; no verified physical scale or detection parameters.

> \# H002 — 3-D centre detection
>
> Use only `image.ome.tif` in this directory as scientific input. It contains
> one greyscale 3-D volume with Z, Y and X axes. Use OpenHCS MCP to develop a
> pipeline that detects nucleus centres and saves a point table in `z,y,x`
> voxel coordinates, an image-level count and reproducible execution receipts.
> Inspect separated Z slices and orthogonal/raw-plus-point views at multiple
> intensity windows. Record obvious misses, unsupported detections, merged
> centres and an explicit accept/reject decision. No physical voxel spacing is
> verified; do not report micrometre distances. Freeze the pipeline and output
> before evaluation.
>
> Do not inspect source notebooks, repository plans, external reference files,
> other agents' outputs, or public expected results. Use OpenHCS MCP for
> scientific inspection, execution and viewer operations; do not inject mouse
> or keyboard events.

#### Brief 7: Paired nucleus and cell segmentation

Trials: `H003_POSTPAUSE_88`; `H003_FRESH656_96`; `H003_FRESH656_88`; `H003_FRESH09_95`; `H003_FRESH10_96`; `H003_FRESH15_96`; `H003_FRESH16_94`; `H003_FRESH23_89`; `H003_FRESH25_89`; `H003_FRESH26_89`.

Technical guidance: exact channel pairing through SourceBindingsConfig, compiled-workspace checks, instance outputs and multi-window image review.

> \# Paired nucleus and cell segmentation
>
> Use only the two TIFFs in this directory as scientific input. Channel 1
> (`w1`) is DNA/nuclei; channel 2 (`w2`) is actin/cell-body signal. Produce
> separate 2-D instance-label images for nuclei and cells, per-object tables,
> and image-level counts with a complete OpenHCS PipelineDocument and execution
> receipts. Preserve the channel identities and the spatial pairing.
>
> These are loose TIFFs, not a complete ImageXpress plate export. Inspect their
> source records before authoring: automatic Bio-Formats discovery may treat
> each file as a separate sample with channel 1. Declare exact file selection
> and the shared A02 well/site/Z/time plus distinct channel identities through
> typed `SourceBindingsConfig`. Confirm the compiled source workspace has one
> paired A02 source set with channels 1 and 2 before segmentation; do not infer
> that pairing from the physical filenames or the default inventory alone.
>
> Inspect the whole field and several separated native-coordinate crops at
> context and object scale. At each diagnostic position, compare raw only,
> labels only, and raw plus labels for each relevant channel, with at least two
> numeric raw display windows. Record clear positives, misses, splits, merges,
> unsupported objects, and an explicit accept/reject decision. No physical
> calibration is verified; report pixel units only. Freeze the pipeline,
> outputs, and QA record before evaluation.
>
> Do not inspect source notebooks, repository plans, external reference files,
> other agents' outputs, or public expected results. Use OpenHCS MCP for
> scientific inspection, execution, and viewer operations; do not inject mouse
> or keyboard events.

#### Brief 8: H004 blind neurite-outgrowth analysis

Trials: `H004_FRESH08_95`; `H004_FRESH10_89`; `H004_FRESH20_95`; `H004_FRESH22_94`; `H004_FRESH25_ROTATION_89`.

Technical guidance: paired-channel soma/process outputs and crossing/extent review. Declared channels and calibration, where supplied, are acquisition hints. Retained-development and mosaic instructions are continuations, not fresh trials.

> \# H004 blind neurite-outgrowth analysis
>
> Analyze only the two source TIFFs in this directory, `field_w1.tif` and
> `field_w2.tif`. Treat them as one paired field with distinct channels. Infer
> their biological roles by inspecting both raw channels; no channel identity,
> segmentation, expected result, or method is supplied here.
>
> Use OpenHCS through its MCP server. Read the complete `use-openhcs` skill and
> the relevant authoring/viewer-review guidance before analysis. Work in your
> own isolated X display `:91` and VNC port `5991` (localhost-only, passwordless)
> and create a Remmina VNC profile for the user if the display is brought up.
> Do not use mouse or direct X-input automation. Do not disturb displays `:0`,
> `:88`, `:89`, or `:90`, or another worker's viewer, service, or output tree.
>
> Create a reproducible pipeline and trial artifacts only under
> `/home/ts/code/projects/openhcs/mcp_outputs/neurite_blind_20260928/trials/H004`.
> Identify neuron/soma and neurite-outgrowth structure, and produce justified
> per-object and image-level measurements where supported. Record the exact
> source pairing, pipeline source, compilation/execution receipts, and output
> paths. Visually inspect raw-only, result-only, and combined views at multiple
> positions/scales and at least two numerical contrast windows. Check uncertain
> connections, missed faint neurites, spurious background, and ownership around
> crossings. Reject or revise a candidate when native-coordinate evidence fails.
>
> Stay blind: do not inspect any sibling directory, prior neurite analysis,
> notebook, reference image, expected table, or other agent's work. Freeze your
> candidate and evidence before asking for a reference comparison. Report any
> unmet scientific or runtime acceptance condition explicitly.
>
> Resource guardrail: check available RAM before loading or running, keep one
> viewer and bounded samples, and stop if memory pressure or swap growth becomes
> substantial. Do not reconfigure the user's desktop session.

#### Brief 9: Paired-field soma and neurite-outgrowth analysis

Trials: `H004_FRESH20_95`.

Technical guidance: paired-channel soma/process outputs and crossing/extent review. Declared channels and calibration, where supplied, are acquisition hints. Retained-development and mosaic instructions are continuations, not fresh trials.

> Paired-field soma and neurite-outgrowth analysis
> \==============================================
>
> Analyze ONLY field_w1.tif and field_w2.tif in the declared input directory.
> Treat them as one spatially paired field with distinct channels. Infer their
> biological roles from both raw channels through MCP metadata and native review;
> no prior segmentation, expected result, method or parameter is supplied.
>
> Produce a complete reproducible OpenHCS PipelineDocument, justified soma and
> process outputs, per-object/image measurements where supported, original
> compile/execution receipts, output tables and matched native captures.
> No verified physical calibration is supplied; use supported pixel geometry
> and qualify biological identity/ownership/extent rather than inventing units.
>
> Inspect distributed raw-only/result-only/combined views at context and object
> scales and numeric raw windows. Review supported positives, uncertain faint
> paths, background, splits/merges and crossing ownership. Preserve FIRST method
> rationale/checkpoint separately from technical retries and later self-directed
> repairs. Report useful local recovery and limitations without treating counts,
> clean overlays or successful execution as whole biological acceptance.
>
> Stay blind: do not inspect prior analyses, sibling outputs, notebooks, reference
> images, expected tables, scorer code or curator answers. Use only task brief,
> packaged skill and original MCP capabilities; no direct X input/science adapter.

#### Brief 10: Blind neurite-outgrowth development task

Trials: `P001_STITCH_DEV94`; `P001_FRESH13_96`; `P001_STITCH_DEV13_94`; `P001_INPUT_REPAIRED22_88`.

Technical guidance: paired-channel soma/process outputs and crossing/extent review. Declared channels and calibration, where supplied, are acquisition hints. Retained-development and mosaic instructions are continuations, not fresh trials.

> Blind neurite-outgrowth development task
> \=======================================
>
> Use OpenHCS to quantify neuronal cell bodies and supported neurite outgrowth
> in the supplied two-channel microscopy fields. Produce a reproducible complete
> PipelineDocument, persisted instance/path artifacts and per-object/per-field
> measurements supported by the images. Retain object identity and units;
> explicitly report unresolved crossing ownership, debris and ambiguous cells.
> Do not manufacture cell assignments where the raw evidence cannot support them.
>
> Inputs are the nine sites of one neutral coded well P001/A01, selected in
> filename order before image inspection. Channel w1 is DAPI and w2 is FITC.
> INPUT_CONTRACT.txt contains the original neutral acquisition facts. Discover
> and verify channel/layout/spacing through OpenHCS; calibration is declared
> 1.3556 micrometres per XY pixel, not an independently repeated calibration.
> There is one Z plane and one timepoint. No original identity, treatments,
> commercial measurements, expected count or reference segmentation is supplied.
>
> This is bounded development evidence, not a whole-corpus result or a claim of
> untouched-data generalization. No pixels outside this input folder are allowed.
> The author independently chooses the method using the frozen operational skill,
> current declarations and empirically measured raw features. Retain technical
> failures and biological rejection separately; a plausible count is not success.
>
> Acceptance requires personally inspected matched raw-only/result-only/combined
> views across fields and distributed positions/scales/windows, support for cell
> bodies and faint process continuity, and explicit split/merge, miss, background
> bridge and crossing decisions. Freeze the candidate, criteria and all evidence
> before any evaluation or additional data access. Abstain on unsupported claims.

#### Brief 11: Personal nine-field neurite analysis

Trials: `P001_INPUT_REPAIRED22_88`; `P001_ALLCHANNEL_RETAINED_DEV25_88`.

Technical guidance: paired-channel soma/process outputs and crossing/extent review. Declared channels and calibration, where supplied, are acquisition hints. Retained-development and mosaic instructions are continuations, not fresh trials.

> Personal nine-field neurite analysis
> \===================================
>
> Analyze the declared nine paired raw fields and their acquisition layout.
> Physical channels are w1 DAPI and w2 FITC/calcein. Use the ordinary declared
> source bindings and preserved acquisition metadata. Retain useful fieldwise
> soma and process geometry with explicit completeness and ownership limits.
> Continue authorized mosaic analysis without treating overlapping field sums
> as unique whole-sample counts. No reference answers or prior detector settings
> are provided by this brief.

#### Brief 12: Personal nine-field neurite analysis: retained development

Trials: `P001_RETAINED_REPAIR23_88`.

Technical guidance: paired-channel soma/process outputs and crossing/extent review. Declared channels and calibration, where supplied, are acquisition hints. Retained-development and mosaic instructions are continuations, not fresh trials.

> Personal nine-field neurite analysis: retained development
> \========================================================
>
> Analyze the declared nine paired raw fields and retained assembled mosaics
> under the original task. Continue your own method and findings from the saved
> review, without any external reference/expected count or hidden answers.
> Preserve local useful soma/process measurements, qualify misses, bridges and
> ownership; do not sum overlapping fields into unique-cell biology.

#### Brief 13: Unavailable pooled-stack scientific brief

Trials: `P001_POOLED_STACK_DEV25_88`.

The full retained instruction is reproduced below; no successful-run method has been substituted for it.

This retained file contains a failed-copy error, not a valid scientific brief. The corresponding operational task is retained verbatim in the archive; no missing brief has been invented.

> sed: can't read /run/media/ts/hdd/openhcs-engineering/p001-input-contract95-20261006/declared-input02/BRIEF.rst: No such file or directory

#### Brief 14: R0010 independent-author development trial

Trials: `R0010_REPAIR10_94`; `R0010_STAGED_96`; `R0010_FRESH656_95`; `R0010_FRESH09_96`; `R0010_FRESH13_89`; `R0010_FRESH22_96`; `R0010_FRESH23_94`; `R0010_FRESH25_94`; `R0010_FRESH26_94`.

Technical guidance: RBPMS/Hoechst channel hints, instance/count outputs and distributed matched-view review; additional workflow/resource restrictions remain visible in the text.

> R0010 independent-author development trial
> \=========================================
>
> Analyse ONLY input/R0010.czi, copied from the authorized retinal development
> split. Assay: retinal whole-mount RBPMS/Hoechst. Acquisition hints are AF647:
> RBPMS and H3258:Hoechst; confirm actual channel/axis/carrier identities yourself
> through MCP metadata and raw-image inspection. Produce inspectable RBPMS-positive
> soma instance labels, object measurements and a qualified image-level count,
> with a complete PipelineDocument and actual compile/execution receipts.
> Biological boundaries or uncertain class/extent must be reported, not inferred
> from an attractive count. No parameter, expected count or earlier method is
> supplied for this field.
>
> Source SHA2563609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851,
> 20946528bytes. This is an already-public DEVELOPMENT input, not held-out data.
> Do not read any other development/held-out image, reference answer, notebook,
> scoring code, repository plan or earlier agent scientific output. The parent
> did not inspect this field's pixels. Agent fork_context=true follows the user's
> standing instruction; inherited conversation is explicitly not a clean-context
> benchmark. Retain independent choices and all later assistance accurately.
>
> Use the full exported harness/skills/use-openhcs/SKILL.md and task-relevant
> references/live MCP contexts. Health first, first_use then selected task context,
> capability discovery and original responsive native/catalog preparation. All
> scientific image reads, processing and viewer control MUST use public MCP in
> the original persistent dev-client shell. No TIFF/CZI Python decoding, viewer
> console, mouse/keyboard/X input, private science adapter or direct execution.
> Source authoring and provider-free synthetic tests are separate from image work.
> If custom source is necessary, read NRA and the authoritative refactor-audit.skill
> plus its pattern catalog first; extend existing nominal declaration/behavior
> owners, shared ancestor algorithms and minimal capability hooks.
>
> Start sh output/launch.sh ONCE in a persistent PTY, retain its exact live handle.
> The existing ordinary installed target is installed-4e745 (OpenHCS0.8.7),
> reviewed source4e745/productionbd2, merged main902913616. Existing dependency
> interpreter is immutable; do not install/download/change it or any package.
> One CPU/pool, no CUDA, shared Fiji cache with downloads disabled. Do not make
> new model/provider calls. Original tool idle limit remains10s; observe exact
> native/catalog/job handles and real progress. Observation expiry does not
> authorize restart, replay, uncertain submission adoption or another process.
>
> Own isolated DISPLAY:89, VNC localhost5989, viewer6000/ACK7000, native6001/ACK7001.
> Parent checked these four execution/ACK ports absent before preparation.
> Do not touch display0, H001display88/5994/5995, H002display90 or neurite91.
> Do not adopt foreign UI bridges/endpoints/locks. Existing Xvfb/VNC belongs to
> parent and remains available after this run; author closes only exact owned
> viewer/runtime via MCP, proves process/listener exit, then cleans owned scratch.
>
> Run resource helper before startup. Twenty GiB disk is advisory; require11GiB
> available RAM at startup,8GiB before jobs/viewer,2GiB filesystem free. The
> entire output plus owned scratch must stay below512MiB. Launcher bounds its
> whole process tree to4GiB RAM/no additional swap/one CPU; take bounded native
> samples before whole-volume operations. If pressure prevents a safe step,
> checkpoint actual live/terminal state and reduce materialization/fleet through
> owners; do not blindly restart or erase partial evidence.
>
> Initial work interval20minutes from actual MCP startup; continue useful
> self-corrections in the SAME context, recording each semantic change and
> failed attempt. Discover validated unrelated Official30 examples and retain
> their exact retrieved pipeline/import/assumptions/parity tier before adapting.
> Measure representative raw features through MCP before selecting scale/size/
> threshold/background/separation settings; use lazy typed configuration.
>
> Distributed QA includes overview plus separated dim/bright, sparse/dense and
> centre/edge witnesses at multiple scales/windows. Personally open matched
> raw-only, labels-only and combined MCP PNGs at identical native coordinates,
> axes/camera/canvas, including faint-signal windows when relevant. Record a
> supported positive, miss/ambiguity and split/merge control and explicit decisions.
> Re-read state after changes; counts and JSON are not visual acceptance. Parent
> may independently review matching artifacts but supplies no expected parameters.
>
> Automatic recording: launcher retains EVERY MCP input/output/timing through
> script; native agent JSONL retains ALL tool calls and image openings. Always
> set snapshot output_dir_path under output/screenshots with unique files. Keep
> all failures, maintain a personally-opened capture index and freeze source,
> parameters, input/package/skill identities, receipts, outputs and denominator.
> No held-out release or reusable-recipe promotion is authorized by this trial.
>
> Owned disposable scratch:
> /home/ts/.cache/agent-scratch/rbpms-r0010-development-434-20261002.
> Persistent source/session/evidence root is this directory under /home/ts/wt.

#### Brief 15: Retinal whole-mount RBPMS analysis

Trials: `R0010_STAGED_96`; `R0010_FRESH656_95`; `R0010_FRESH09_96`; `R0010_FRESH13_89`; `R0010_FRESH22_96`; `R0010_FRESH23_94`; `R0010_FRESH25_94`; `R0010_FRESH26_94`.

Technical guidance: RBPMS/Hoechst channel hints, instance/count outputs and distributed matched-view review; additional workflow/resource restrictions remain visible in the text.

> Retinal whole-mount RBPMS analysis
> \================================
>
> Analyse only R0010.czi in this input directory. Assay: retinal whole-mount
> RBPMS/Hoechst. Acquisition hints AF647:RBPMS and H3258:Hoechst; confirm physical
> channel and axis identity through MCP metadata and raw inspection. Produce
> RBPMS-positive soma instance labels, per-object measurements, qualified counts
> and a complete PipelineDocument with compile/execution receipts. Report
> uncertain identity, extent and dividing boundaries explicitly.
>
> This is authorized development input. No expected count or earlier method is
> supplied. Do not inspect other images, reference answers, notebooks, scorer code,
> repository plans or prior agents' scientific outputs. Use only this input, MCP
> and packaged guidance. Preserve FIRST, later self-directed repairs and matched
> distributed raw/result/combined QA; assess your final selected method at its
> supported scope. Current AUTHOR-PACKET owns operational paths and resources.

#### Brief 16: Retinal whole-mount RBPMS analysis

Trials: `R0010_FRESH22_96`; `R0010_FRESH23_94`; `R0010_FRESH25_94`.

Technical guidance: RBPMS/Hoechst channel hints, instance/count outputs and distributed matched-view review; additional workflow/resource restrictions remain visible in the text.

> Retinal whole-mount RBPMS analysis
> \==================================
>
> Analyse ONLY the authorized public development input:
> /home/ts/wt/openhcs-issue-batch-20260929/next-rbpms-h003-94-20261003/input/R0010.czi.
> Source SHA2563609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851,
> 20946528 bytes. This is development data, not a held-out input.
>
> Assay: retinal whole-mount RBPMS/Hoechst. Acquisition hints AF647:RBPMS and
> H3258:Hoechst; confirm physical channel/axis/carrier identity yourself through
> MCP metadata and raw inspection. Produce RBPMS-positive soma instance labels,
> per-object measurements, qualified image-level count and a complete original
> PipelineDocument with compile/execution receipts. Report uncertain extent,
> class and boundaries explicitly. No expected count or earlier method supplied.
>
> Use only this acquisition and packaged OpenHCS MCP/skill. Do not inspect other
> images, reference answers, notebooks, scorer code, repository plans or prior
> agents' scientific outputs. Inspect distributed native raw/result/combined
> views and keep exact source/channel/view-state provenance. Preserve the first
> scientific checkpoint, later repairs and their independent QA decisions.
> Technical execution/count agreement does not establish biological acceptance.

#### Earlier prospective records

The resource catalogue contains no recoverable original instruction file for `BBBC007_PROSPECTIVE_20260916`, `BBBC013_PROSPECTIVE_20260916`, `BBBC039_PROSPECTIVE_20260916`. Their published prospective protocol and partitions remain in Supplementary Data 7; author-written candidate plans are not relabelled as original prompts.
