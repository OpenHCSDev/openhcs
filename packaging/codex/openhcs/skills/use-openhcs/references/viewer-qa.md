# Review microscopy images and results in the managed viewer

Use this procedure before tuning a pipeline, accepting its output or reporting
a biological count. Read the live `image_analysis_workflow` and `viewer_review`
contexts for current evidence and control contracts. Use MCP for navigation,
layer visibility and captures; never inject mouse or X11 input. A tool success,
viewer-state JSON or another agent's summary is not your own bitmap inspection.

## Establish the source and channel interpretation

Inventory the physical acquisition's channels and verify identities from
metadata. A single-channel trial/export does not establish that the source has
only one channel. Load relevant raw channels together at matched native
coordinates, then inspect the composite. Form a provisional interpretation of
nuclei, bodies, subcellular structures, processes, background and debris yourself.
Ask for missing biological information only when it changes the decision. If
channel comparison is unavailable, record that limitation before tuning.

Verify execution/source/component identity, native XY scale and translation,
source spacing and selected Z/time before comparing raw and results. Aggregate
viewer indices may differ from route-local semantic coordinates. If routes from
different plates disagree, stream raw from the result's declared source and
recheck. Reject black, wrong-channel, stale or misplaced captures; an invisible
overlay is not evidence that the detector found nothing.

For feature-bearing 3-D point results, check the persisted point coordinates
against the viewer's native point geometry, declared Z domain, and selected
feature row. Select a point by its data index through MCP and verify that the
same row and exact Z coordinate remain attached. A result-only Points layer
may have a native slice range determined solely by its points, so a displayed
integer Z label or `current_step` alone does not establish the point's Z or
its alignment with raw planes. Confirm that alignment in the combined view;
record any disagreement rather than treating a visible point as a QA pass.

## Choose a distributed, multiscale sample

Inspect the whole field for illumination, tissue, focus and density variation.
Choose distinct bright/dim, central/edge, sparse/dense, tile-join and suspected
failure positions where present. Inspect intermediate context and native object
scale in every relevant raw channel. A thumbnail cannot decide a small split
or a thin neurite connection.

At fixed coordinates, compare numeric windows preserving faint structure and
revealing local detail, plus full range when useful. Record applied limits,
not labels such as "bright". Compare bounded local distributions and background
across positions. Contrast crushing can conceal real signal; an uneven field
does not establish the background's cause. Display contrast/gamma is not
analytical preprocessing.

Before selecting analysis scales or thresholds, follow
[the empirical measurement procedure](measurement-interpretation.md#measure-feature-scales-before-choosing-parameters)
on the distributed raw witnesses. Record native boundary spans, genuine
neighbour separation and local intensity/background evidence as relevant; link
each to its parameter rationale. A provisional result's geometry is not an
independent raw-feature measurement, and screen-pixel length is not native length.

## Capture and inspect a matched three-view set

Read viewer state before each set: route, channels, axes, camera/crop, scale,
canvas geometry, visibility and intensity limits. On older viewers use screenshot
dimensions if canvas geometry is unavailable. The user can resize, pan or alter
layers between calls; do not assume the previous state persists.

At the same position, Z/time and camera scale, capture:

1. **Raw only:** hide the result. Inspect supported bodies, weak structures and
   plausible misses without an overlay obscuring them.
2. **Result only:** hide every underlying image layer, leaving the result on the
   empty canvas. Inspect fragments, splits, gaps and disconnected components.
3. **Raw plus result:** restore raw and result. Inspect biological support and
   alignment, with the same raw window as the first view.

Toggle visibility through MCP without changing pixels or result identity.
Open all bitmaps yourself. If canvas, coordinates, axes, camera or presentation
changed during capture, re-establish state and recapture the matched set before
comparison. Repeat at necessary field, context and object scales; no single
view is an acceptance witness.

## Diagnose one failure and preserve a regression control

Log a clear positive, a plausible miss/ambiguity and an explicit
accept/reject/ambiguous judgement. For suspect nuclear splits, inspect raw
internal structure under both windows and retain a genuine close pair elsewhere.
Compare foreground and markers before changing watershed. For secondary objects,
inspect body-channel support and growth beyond each object's own primary seed;
matching counts or retained seed IDs do not prove cell bodies. For neurites,
inspect faint supported soma-to-process continuity, endpoints, crossings,
branches and background bridges. Triage ambiguous debris separately so it does
not prevent review of clear supported misses.

Use [segmentation diagnostics](segmentation-diagnostics.md) for the earliest
failed stage and [preprocessing](image-preprocessing.md) for its nuisance model.
Change one semantic operation or parameter group, then recheck failure and
regression-control crops against raw. Also revisit the preselected distributed
bright/dim and centre/edge witnesses: a local repair cannot pass if it adds
misses, merges or background elsewhere. For uneven illumination or denoising,
inspect the correction field or residual and processed pixels before downstream
labels; an independently auto-stretched display can conceal the regression.
Reconcile persisted labels/ROIs,
measurements and physical units before widening the run or quoting a count.
Retain witness paths, state/coordinates, channels/windows, pipeline/result
identity, observed differences and decision in the authorised trial log.

## Choose an honest display for figures

Keep display fitting separate from detection and measurement. Compare native
witness crops spanning faint paths, ordinary background, bright bodies and joins,
plus the whole mosaic, before accepting a curve. A modestly elevated background
can be preferable to erased supported paths, but reject excessive haze and
clipped bodies too. Compare background level/spread, highlight clipping and
path-to-nearby-background contrast; display metrics do not establish identity.

For comparable stitched figures, a shared percentile fit across representative
images, a large-scale background estimate per mosaic and a gentle shared stretch
are candidates, not a mandatory recipe. Compare individual effects and ordering
on fixed development witness crops. Never choose a figure transformation because
it hides segmentation failure. See [measurement interpretation](measurement-interpretation.md)
for shared mappings and measurement-image boundaries.

This procedure preserves local OpenHCS review lessons and complements the
[source-backed biological evidence](biological-image-analysis-evidence.md).
Live typed policies and callable/artifact contracts remain operational owners;
this procedure is not an automatic pixel-review gate.
