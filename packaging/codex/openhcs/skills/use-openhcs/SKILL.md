---
name: use-openhcs
description: Operate local OpenHCS microscopy workflows through the bundled MCP server. Use when Codex needs to inspect plate data, discover processing functions, author or validate pipelines, compile and execute jobs, control viewers, or interact with a running OpenHCS GUI.
---

# Use OpenHCS

1. Call `openhcs_health_check` before relying on other tools. Report a bootstrap or stale-server failure instead of working around it.
2. Call `openhcs_get_authoring_context` with `kind="first_use"` when choosing or resuming an OpenHCS workflow, then request exactly the task context it names. For multisite assembly, registration, normalisation, segmentation review, or image-result QC, `kind="image_analysis_workflow"` is the canonical operating guide; follow it rather than reconstructing those rules from this skill.
3. Treat Python pipeline source as one complete `PipelineDocument`: `pipeline_config` plus ordered `pipeline_steps`. Never send a steps-only fragment, mirror configuration through a second argument, or strip source bindings from the reviewed document. UI-visible and headless routes use these same declarations even though their process and state owners differ.
4. Call `openhcs_search_capabilities` with task-relevant workflow, target, or text filters. Its current `surface_profile`, registry-owned workflow metadata, side effects, and security metadata—not a remembered tool list—decide whether to use a UI-visible or exposed headless route. Use `openhcs_list_capabilities` only when the complete selected surface is required.
5. Search knowledge and examples before authoring. For CellProfiler or benchmark work, search the biological task plus `OpenHCS Python` and retrieve the returned Official30 section with `max_chars=50000`. CellProfiler image, object, measurement, relationship, and export semantics lower into the same OpenHCS declarations and runtime.
6. Inspect real plate data and registered function declarations before authoring. If the microscope is unsupported, use typed pipeline-level `SourceBindingsConfig` declarations to filter files, extract metadata, name semantic sources, and project a virtual workspace; make each consuming `FunctionStep` select those aliases through its step-local source bindings. Never parse filenames inside processing functions. Reflect `global` or `pipeline` configuration with `openhcs_describe_config_schema` before setting non-obvious fields. Keep filesystem operations inside configured read and write roots.
7. Validate and compile before execution. Do not infer that source code, UI state, or an earlier validation result implies a current compiled plan.
8. Start read-only. Use capability-registry metadata as the authority for mutation and exposure; before mutation, execution, UI actions, viewer launch, network use, or external data exposure, show the target/change, obtain approval, and refresh revision or request tokens.
9. Preserve the active ownership route. Discover the GUI bridge before UI tools and apply code/state changes with current tokens. Use headless tools only when their workflow group is exposed. Treat structured errors and recovery hints as authoritative; never bypass path policy, stale-process checks, compile requirements, or bridge authentication.

## Image-analysis QA

For segmentation, neurite tracing, faint structures, or a report that an overlay
looks wrong, load both `image_analysis_workflow` and `viewer_review` before
tuning or judging the result. These MCP contexts supply the shared raw-first
biological interpretation, native-coordinate inspection, display-window,
stage-diagnostic, and validation-split rules; do not depend on a prior agent's
conversation or on a separately installed assay skill. Follow the earliest
failed-stage decision through one bounded diagnostic and inspect its retained
artifacts before expanding the run.
Before choosing a detection channel or changing a threshold, inventory the
physical source's available channels and verify their identities from acquisition
metadata. Load the relevant raw channels together through MCP, inspect them at
the same native coordinates under appropriate display windows, and establish
which shows the target cell bodies versus nuclear or subcellular signal. A
single-channel exported plate or trial output is not evidence that the source
has only one channel. If the comparison cannot be made, record that limitation
and do not tune or biologically accept the detector from that view alone.
Make this a multiscale, spatially distributed review before tuning or accepting
a result. Inspect the whole field for illumination, tissue, focus, and density
variation; then inspect a grid of distinct positions at intermediate context
and native object scale, including bright and dim, central and edge, sparse
and dense, and suspected failure regions where present. Do this in every
relevant raw channel at matched coordinates, not just one attractive crop.
At each position and scale, compare the same raw pixels under multiple numeric
display windows: one that preserves faint structure and a tighter one that
reveals local contrast. Open the captured bitmaps yourself, and log the
coordinates, scale, channel, window limits, and what changed in interpretation.
Do not confuse display clipping or contrast crushing with absent biological
signal. Compare local background and candidate-cell appearance across the
sampled positions before treating a global threshold as representative. If
background is uneven, distinguish display-window effects from raw-pixel
variation and do not assume its cause; test any proposed analytical correction
on held-out-looking regions of the development set while preserving the actual
held-out split.
Do not accept a count, mask, or measurement merely because compilation or
execution succeeded. First save a same-coordinate raw-plus-result witness with
the raw biological channel visible, its channel identity and display limits
verified from viewer state, and the result overlay visible at native scale.
Before capture, compare the raw and result routes' native XY scale and
translation, source spacing, and component identities. If routes from different
plates disagree, stream the raw pixels from the result's declared source plate
and recheck; reject the earlier capture rather than treating an invisible or
misplaced overlay as biological evidence.
For segmentation diagnostics, capture a matched three-view set at each sampled
position: raw only (hide the result), result only (hide every underlying image
layer, leaving the result visible against the empty canvas), and raw plus result
(restore the image layers). Toggle layer visibility through MCP rather than
altering the pixels. Keep the same coordinates, Z/time index, camera scale,
result presentation, and raw display window for both raw-bearing views; record
the window limits. Read MCP viewer state
before each set and compare canvas geometry (or screenshot dimensions on an
older viewer), camera, axes, layer visibility, and intensity with the prior
set; the user may have changed the window.
The raw-only view exposes misses; result-only exposes fragments and splits
hidden by the image; combined tests biological support and alignment. Repeat at
whole-field, context, and object scale as needed; none of the three views alone
is an acceptance witness. If the canvas or presentation changed between
captures, recapture the matched set before comparing them.
Open and visually inspect the captured bitmaps yourself; a viewer-state JSON,
tool success response, or another agent's summary is not an image review.
Record the witness path, the raw channel and window, at least one clear
positive and one plausible miss or ambiguity, and an explicit accept/reject
decision in the trial log before widening the run or quoting any count.
A labels-only view by itself, a black or wrong-channel background, or a thumbnail
where objects cannot be judged is not a QA pass. Compare clear positive objects,
misses, fragments, and unsupported detections; reject the attempt when the
overlay contradicts the raw image. Reconcile label IDs, ROI rendering, and
physical-unit measurements against the persisted artifacts before expanding
to more images or quoting a count.
For nuclei or other compact objects, treat a watershed split as a hypothesis,
not an extra cell. At the suspect native-coordinate crop, inspect raw-only
under both faint-preserving and detail-preserving windows, then result-only
and combined. Ask whether the proposed labels occupy distinct raw objects
with a credible boundary, or merely divide one continuous bright body at
internal peaks. Check close pairs elsewhere too: tuning away one false split
can merge real neighbors. Change one seeding, unclumping, or watershed setting
per trial; keep both the repaired and regression-control crops in its log.
For primary-to-secondary segmentation, verify more than matching object counts
or label IDs. Compare each secondary area with its own primary area and inspect
any zero-growth or implausibly large regions on the secondary raw channel at
the same coordinates. A secondary label identical to its nucleus may be a
retained seed rather than a segmented cell body. Use the raw-only/result-only/
combined set to distinguish a genuinely unsupported body from a threshold or
propagation failure; record the failure before tuning one secondary parameter.
Do not report the secondary count as a biological cell-body count until these
checks and spatially distributed visual QA pass.
When an image defect motivates analytical preprocessing, read
[the preprocessing decision guide](references/image-preprocessing.md) before
changing the pipeline. Keep raw and processed routes available for matched
inspection; a viewer contrast or gamma change is not preprocessing.
For qualitative visualization, err toward a slightly brighter background
rather than erasing faint, supported cell bodies or continuous neurites. Compare
the same native-coordinate raw pixels under several whole-mosaic display
windows; local background subtraction is not automatically the best view.
Keep display-only adjustments separate from analytical preprocessing.
For comparative stitched-image figures, consider one percentile fit over the
complete representative-image stack, a large-radius rolling-ball estimate per
mosaic, then a gentle shared percentile stretch. Compare the same raw neurite
paths before and after. Before accepting a display change, freeze native-scale
witness crops spanning faint paths, ordinary background, bright bodies, and
tile joins; compare candidate curves on those crops and the whole mosaic.
Track background level/spread, highlight clipping, and path-to-nearby-background
contrast. Reject both erased paths and excessive haze or clipped bodies; use
raw pixels or annotations to decide biological identity, not a display metric.
Apply the canonical guide's visual triage of possible dying cells or debris:
an ambiguous compact focus is not automatically a missed neuron and should
not stall review of clear, connected neurite misses.

For apparent round-object over-segmentation, discover the registered
`inspect_metaxpress_round_objects` function and inspect its typed labels and
measurements at the same raw coordinates. Interpret them by the canonical
`image_analysis_workflow` policy; do not invent a second segmentation or a
viewer-only diagnosis.
