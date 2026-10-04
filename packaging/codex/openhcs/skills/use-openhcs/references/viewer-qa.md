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

Check contrast for **each distinct image**, including a new site, Z/time plane
or processed output, even when its channel name is unchanged. Signal range,
background and processing units can differ drastically. Inspect that image's
bounded intensity/background samples and raw-only views at multiple windows
and scales before choosing its review limits/gamma; do not inherit a previous
image's limits without checking. Keep the chosen raw window unchanged within
a matched raw/result/combined set, or recapture the set after changing it.

When channels share an image layer, its contrast limits can remain unchanged
when the channel axis changes. After switching channels or restoring a view,
read back the physical source/component, visible route and applied numeric
limits/gamma; explicitly apply the review window appropriate to that channel.
A correct channel label with another channel's window can hide the structures
being analysed. Do not infer the current presentation from the last request.
If remote-desktop compression is suspected, open a native MCP PNG capture at
the same viewport before attributing absent paths to the transport. Distinguish
hidden raw signal from paths actually missing in a saved processing stage.

## Choose a distributed, multiscale sample

Inspect the whole field raw-only, with results hidden, for illumination, tissue,
focus and density variation.
Choose distinct bright/dim, central/edge, sparse/dense, tile-join and suspected
failure positions where present. Inspect intermediate context and native object
scale in every relevant raw channel. A thumbnail cannot decide a small split
or a thin neurite connection.

### Reveal faint structures and nuisance variation

1. At fixed coordinates, progressively **lower the numeric upper display limit**
   on the relevant raw channel. Keep near-background values visible rather than
   raising the lower limit to make the field black. Record both applied limits
   and gamma, not labels such as "bright". There is no universal window for an
   assay or intensity scale.
2. Compare more than one window, including a less compressed view of bright
   boundaries. Repeat the raw-only scan at full-field, context and native scales
   across the distributed positions. Bright somas may intentionally saturate:
   seeing or segmenting faint neurites does not require every body to retain
   intensity detail in the diagnostic view. Aggressive low upper limits can
   conceal paths in a uniformly bright patch or make noise look like neurites;
   do not accept an interpretation from that window alone.
3. Inspect supported faint paths and nearby background together. Use the scan
   to assess noise amount/texture, background level and uneven illumination as
   well as continuity, endpoints and crossings. Visible haze or clipped bright
   bodies are not automatic failures in this diagnostic view. Compare bounded
   local distributions across positions; one uneven field does not identify
   the nuisance's cause.
4. If signal quality needs analytical improvement, follow
   [preprocessing selection and composition](image-preprocessing.md#establish-spatial-coverage-before-tuning):
   interpret the nuisance and discover compatible declared operations and order.
   Segment or trace on the chosen processed alias, then use
   [claim-appropriate measurement inputs](measurement-interpretation.md#detection-pixels-versus-measurement-pixels):
   processed-derived masks/traces can support geometry, count, area and length;
   original-fluorescence photometry needs its appropriate intensity source.
   Inspect distributed raw/processed/result witnesses and the matched sets below
   to find missed processes or false bridges and guide the next repair. Do not
   infer an analytical threshold from a display limit or assume a prettier
   background preserves faint biology.

Changing viewer limits/gamma changes presentation, not the working array.
An explicit pipeline transform may legitimately clip, remap, denoise or correct
working analytical pixels for segmentation. Retain acquisition source and
processing provenance as the reproducible reference; this procedure does not
authorise overwriting acquisition files. Validate the transform against raw
support, faint-path preservation and connectivity. Choose measurement inputs
by the [measurement claim](measurement-interpretation.md#detection-pixels-versus-measurement-pixels),
not a blanket requirement that every analytical pixel remain unchanged.

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

Toggle visibility through MCP without changing the candidate's arrays or result
identity during the matched set. This comparison control does not prohibit
analytical preprocessing in a subsequent candidate.
Open all bitmaps yourself. If canvas, coordinates, axes, camera or presentation
changed during capture, re-establish state and recapture the matched set before
comparison. Repeat at necessary field, context and object scales; no single
view is an acceptance witness.

### Points and centres

Point results need the same three-view comparison; selected raw-plus-points
captures or point counts alone are insufficient. Identify the intended final
Points layer and its persisted result/source identity, excluding earlier result
versions and unrelated Labels, Shapes or Points from the matched set.

- **Raw only:** hide the point result and other result layers.
- **Point only:** hide **every image layer**, not just the selected raw image,
  and show only the intended final Points result. Keep raw mounted but hidden
  so its source/domain context remains available; do not unload it for this
  comparison.
- **Combined:** restore the matching raw image and that same Points layer,
  retaining the raw window and the set's native coordinates, camera and axes.

For feature-bearing points, select by the final layer's `data_index` through
MCP and verify the attached feature row against the persisted point and native
geometry. For 3-D results record the exact, possibly fractional, Z coordinate
and declared source Z domain, not only the displayed integer slice label.
Visibility or selection changes can alter a point-only view's native slice
range. Read back camera, axes and coordinates after each transition; restore
the matched view if they changed. Keeping raw mounted is not proof that the
viewer preserved that state. Inspect genuine XY/XZ/YZ views when the source
and exposed contracts support them; record unavailable views without inventing
a projection or source domain.

Open all three captures and judge raw support, placement and separation at
distributed positions and scales. Relate points to masks or structures only
when that association belongs to the intended measurement; there is no
universal requirement that every centroid lie inside a mask. Record geometry,
row or alignment disagreements instead of treating a visible point as a pass.

## Keep iterative review within its resource budget

Treat durable candidate evidence and the active viewer scene separately.
After a candidate's execution and captures are settled, retain its source,
result/intermediate paths, matched PNGs, state and decision on disk. Keep the
current matched raw/result routes and any raw references or regression routes
still needed for the next comparison; previous candidates need not all remain
mounted to preserve their evidence.

Before adding another candidate, read the unfiltered viewer state through
`openhcs_get_viewer_window_state` and check mounted routes, component groups and
the trial's actual memory/output headroom. A route-filtered layer count is not
the whole scene. Hiding a route with `openhcs_navigate_viewer_window` or showing
only chosen routes with `openhcs_isolate_viewer_window_layers` changes visibility,
not buffer lifetime. A new execution's stream reset is not selective retirement
of earlier mounted results. Do not budget hidden layers as released memory.

Discover the installed selective-retirement capability and reflect its request
before using it. When the compatible `openhcs_retire_viewer_window_layers`
contract is exposed:

1. Preserve durable candidate files, source/declarations, captures and decisions.
   Resolve execution/stream mutations to a known terminal disposition and let
   receiver work settle before retirement. UNKNOWN, pending or in-flight work
   is not permission to discard a route. A known failed terminal candidate can
   be explicitly retired once no mutation is outstanding and its evidence is
   retained; failure does not require keeping its buffers forever.
2. Read fresh, unfiltered viewer state on the same viewer incarnation. Choose
   only explicitly superseded routes; retain the current matched candidate,
   raw/source domain and reference routes still needed for the next comparison.
   Build `expected_producers` by mapping each chosen **exact `route_key`** to
   its **complete `producer_identities` array** from that readback, including
   `invocation_key`. Do not shorten, fabricate or substitute identities from a
   previous candidate, title or port. The receiving owner checks the whole set
   before removal; a changed producer requires a fresh disposition/readback,
   not a weaker identity check.
3. Submit that explicit mapping once. Retain the typed acknowledgement and
   check `observed`, `applied`, errors, exact `retired_route_keys` and untargeted
   `remaining_route_keys`. After a timeout or error, preserve the original
   reply/disposition and inspect actual state read-only; do not assume rollback
   or replay the mutation. This operation releases the selected scene/cache
   entries, not persisted files or scientific history.
4. Read back survivor payload/source identities, domain, native calibration,
   axes, camera and presentation, then verify the current matched comparison.
   Check selected feature-row indices too: preserving the active layer/style
   does not establish preserved Points/Shapes `selected_data`. Record a lost
   or changed row as a receiving discrepancy, not another object's evidence.

Compare permitted **actual memory telemetry** for the same native process or
scope before and after settled retirement. A removed/hidden layer count is not
an RSS/PSS measurement. Native cache/scene release and lower process RSS are
different observations: allocators may retain released memory, and a small
retirement need not show a measurable RSS drop. Record the measured change or
missing attribution and keep resource accounting conservative; do not assume
reclaimed headroom from the UI. Do not use blanket scene clearing, history
deletion or viewer restarts as an iteration policy.

If no compatible retirement operation is exposed, record that contract gap
and request its original runtime owner; do not invent a remove-layer command,
invoke private control messages or manipulate the viewer outside MCP. Continue
only the work that fits the remaining authorised resources, rather than adding
candidate buffers without accounting for them. Keep frozen witnesses and
UNKNOWN operations intact. Scope OOM, layer counts and retained output bytes
are different observations: none alone identifies a memory leak or the
responsible process. Record actual memory attribution or its absence.

## Diagnose one failure and preserve a regression control

Log a clear positive, a plausible miss/ambiguity and an explicit
accept/reject/ambiguous judgement. For suspect nuclear splits, inspect raw
internal structure under both windows and retain a genuine close pair elsewhere.
Compare foreground and markers before changing watershed. For secondary objects,
inspect body-channel support and growth beyond each object's own primary seed;
matching counts or retained seed IDs do not prove cell bodies. For neurites,
inspect faint supported soma-to-process continuity, endpoints, crossings,
branches and background bridges. Assess supported misses, erased paths and
induced bridges/artifacts by their distributed extent and effect on the claim,
using the linked claim-scoped criteria rather than a zero-error rule; saturation of
bright somas alone is not a diagnostic or segmentation rejection gate. Triage
ambiguous debris separately so it does not prevent review of clear supported
misses. Apply [claim-scoped conclusions](analysis-strategy.md#scope-conclusions-to-the-evidence)
to retain supported findings and identify which objects or relationships remain
uncertain, rather than converting every result into a blanket abstention.

Use [segmentation diagnostics](segmentation-diagnostics.md) for the earliest
failed stage and [preprocessing](image-preprocessing.md) for its nuisance model.
Change one semantic operation or parameter group, then recheck failure and
regression-control crops against raw. Also revisit the preselected distributed
bright/dim and centre/edge witnesses: assess whether a local repair introduces
material misses, merges or background elsewhere, not just whether it changes
one object. Reuse the recorded native crop, Z/time, orientation, camera scale
and raw window for both the predecessor and revised candidate. Restore and
read back that state before capture; a repeated field name with a shifted
viewport is not the same regression witness. If the canvas changed, compare
the same native region rather than screen-pixel positions.

At those coordinates compare recovered and lost structures, separation and
mask footprints: a revision can find more objects while eroding supported
boundaries, merging neighbours or truncating paths elsewhere. Record the
benefit and regression separately, and choose the candidate against the
task's measurement claims. More labels or longer graphs alone do not establish
a task-wide improvement; useful supported findings do not require every
ambiguous object to be resolved.

For uneven illumination or denoising,
inspect the correction field or residual and processed pixels before downstream
labels; an independently auto-stretched display can conceal the regression.
Reconcile persisted labels/ROIs,
measurements and physical units before widening the run or quoting a count.
Retain witness paths, state/coordinates, channels/windows, pipeline/result
identity, observed differences and decision in the authorised trial log.

## Choose an honest display for figures

Keep display fitting separate from detection and measurement. Compare native
witness crops spanning faint paths, ordinary background, bright bodies and joins,
plus the whole mosaic, before accepting a curve. State the figure's intent.
For a publication panel claiming body detail or comparable fluorescence, reject
a mapping that obscures the claimed detail with haze or clipped highlights.
For a diagnostic faint-process view, elevated visible background and deliberately
saturated somas can be appropriate; do not import that publication criterion as
a segmentation hard gate or erase supported paths for a cleaner-looking field.
Retain a complementary window when bright detail also matters. Compare background
level/spread, highlight clipping and path-to-nearby-background contrast; display
metrics do not establish biological identity or photometric validity.

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
