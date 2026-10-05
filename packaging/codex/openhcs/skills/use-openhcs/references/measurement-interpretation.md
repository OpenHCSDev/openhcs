# Choose valid microscopy measurements and comparisons

## Measure feature scales before choosing parameters

Use this procedure before selecting the detection/declumping method as well as
setting object diameter, seed separation, smoothing, background-removal scale,
spot/ridge width or a shape prior. Base a starting
range on representative raw features in the managed Napari viewer, not a
remembered cell size or a convenient detector default. These are development
measurements, not ground truth or an automatically validated parameter choice.

1. Read `image_analysis_workflow` and `viewer_review`, then search the current
   capability registry for measurement, profile and geometry operations.
   Establish source/route/channel, Z/time, native dimensions, layer transforms
   and verified spacing. Inspect raw-only at object scale and retain a context
   view using [the matched viewer procedure](viewer-qa.md). Camera zoom and
   canvas pixels are not source pixels. World coordinates must be converted
   through the layer transform before becoming index-space sample coordinates.
2. Choose clear isolated objects, a genuine close pair and faint/small examples
   across preselected bright/dim, sparse/dense and centre/edge regions, at context
   and native feature scales. Measure an envelope of supported widths, sizes
   and local signal/background values, including narrow and broad structures,
   clear positives and faint controls. One early feature is not the assay's
   scale range. Retain extremes and ambiguity rather than measuring only objects
   the current detector finds. For 3-D, inspect multiple Z planes and orthogonal
   views when exposed; a projected width does not establish Z extent.
   Where available, include whole near-background/no-object fields using
   [the first-candidate and pre-widen control](#include-no-object-fields-before-widening),
   not only background patches beside positive objects.
3. Use exposed native measurement capabilities where available and retain their
   receipts. For bounded raw evidence, `openhcs_sample_viewer_window_image`
   takes `route_key`, route-local `axis_indices`, native `y`, `x`, `height`,
   `width` and optional exact values. Request `include_array_values=true` with
   `height*width<=max_array_elements` when the claim needs pixels. A 16x16 XY
   tile needs at least256 elements; its origin comes from the actual source,
   not this example. Verify returned record identity, origin, dimensions, dtype
   and truncation; tile a larger region rather than treating a partial sample
   as a whole object. `openhcs_get_viewer_window_payloads` exposes bounded
   image/shape geometry; `openhcs_summarize_viewer_window_rois` exposes existing
   ROI bounds and area summaries. Neither establishes independently verified
   raw-cell masks. For a feature-bearing layer, select `data_index` through
   `openhcs_navigate_viewer_window` and verify the returned selection and
   object/point identity before linking a table row to a visible object.
4. Measure the feature relevant to the intended parameter:

   | Intended input | Evidence to collect | Avoid |
   | --- | --- | --- |
   | Object-size range | Long/short raw boundary spans across isolated and touching examples; per-axis extent for 3-D | Calling a current mask's size independent evidence, or confusing radius with diameter |
   | Seed separation | Centre-to-centre distance of genuine neighbours and multiple maxima within one textured object | Using diameter as minimum separation and suppressing real close pairs |
   | Smoothing/spot/ridge scale | Supported narrow-to-broad width envelope, noise texture, positive/faint-path and close-pair controls | Equating diameter with Gaussian sigma or assuming one scale preserves every supported width |
   | Background-removal scale | Target width plus extent and variation of nearby background in multiple regions | A universal kernel radius or subtracting cell signal as background |
   | Threshold/prominence | Values on the actual consumed alias or response: object/background or peak/valley separation, weak positives, noise and saturation; matched raw views establish biological support | Substituting raw-channel SNR for enhanced-response thresholds, or deriving cutoffs from contrast, gamma or label colours |
   | Roundness/shape prior | Isolated raw contours, elongated/lobed examples and an unsupported-shape control | Forcing every cell to be round or treating a round-looking mask as validation |

   Retain native coordinates, measurement method, units and boundary uncertainty.
   Straight calibrated XY distance is
   `sqrt((delta_y*spacing_y)^2+(delta_x*spacing_x)^2)`; keep the selected endpoints.
   Without verified calibration report pixels/voxels, not micrometres. A curved
   neurite needs path length, not an endpoint chord. Given an independently
   supported 2-D area, equivalent-circle diameter is `2*sqrt(area/pi)`; it is
   neither a major-axis length nor evidence of roundness. ROI contour-member
   count is not necessarily instance count.
5. Record source/route/axes, witness coordinates, receipt/capture, raw measurement
   and uncertainty, chosen callable/method/parameter, unit conversion and rationale in
   the trial log. Summarise the observed range and regional variation. Reflect
   the exact registered callable before applying a number: radius versus
   diameter, sigma versus kernel width, anisotropic spacing and intensity units
   differ between algorithms. Keep unsupported precision as an interval or
   limitation. Label mask-derived estimates provisional and check against raw,
   including missed objects; do not tune a detector solely from its own output.
   A single-scale filter can favour one width class while suppressing another.
   Inspect its response across the measured envelope before changing downstream
   thresholds. If discovery returns a compatible multiscale callable, describe
   its actual scale units, supported arguments and response-combination contract;
   do not invent a scale-list parameter or assume a single-scale argument accepts
   one. Estimate intermediate/response memory before a bounded comparison.
   For a compound detector, relate each measurement to the stage it supports:
   raw width or local signal/background difference does not by itself justify
   admission on an enhanced response, seed extraction or final object acceptance.
   Reflect the effective contract: one width may also control smoothing or
   background scale, while a size-acceptance bound need not change markers.
   Before the first proposal, predict both faint-signal recovery and rejection
   of regional negatives, preserving ordinary/narrow/broad and genuine-pair
   controls. Inspect the earliest available response/support in the first
   bounded candidate before interpreting downstream losses; do not automatically
   lower admission or enlarge width because a plausible raw scalar missed a
   structure. Use [stage-specific diagnostics](segmentation-diagnostics.md)
   to distinguish response generation, admission and later acceptance.
6. Compile one bounded candidate, inspect its earliest changed intermediate,
   then compare matched raw/result/combined at the measured failures and
   regression controls. Revisit distributed regions after every change; a
   local repair can fail elsewhere under uneven illumination. Freeze measurement
   receipts and rationale with the complete candidate before held-out access.
   Expected counts or reference masks must not choose measurements in a blind run.
   Link the measured envelope and remaining exclusions to the affected phenotype
   claims through [the analysis strategy](analysis-strategy.md), which owns
   claim-scoped conclusions rather than blanket abstention.

Worked faint-path contrast: a continuous raw path stands above nearby background,
but its detector requires enhanced candidate support AND a local-response gate.
Raw width and contrast can support a scale and provisional local cutoff, not
calibrate the enhanced admission factor. An unmeasured default remains a trial
hypothesis. Use the first bounded candidate to compare support along that path
and a nuisance-only control. If only the intersected mask is exposed, missing
support locates the loss before rooting but cannot identify which gate rejected
each pixel. A controlled gate change tests recovery without changing supported
width/body detection; newly admitted background bridges oppose it. Check optional
[seed/component retention](segmentation-diagnostics.md#separate-support-recovery-from-rooted-graph-validity)
before attributing loss to rooting. If support survives the declared admission
and retention gates but reported paths are absent, investigate rooting/topology
rather than lowering admission.

### Include no-object fields before widening

Before the FIRST threshold proposal and before widening a positive-only sample,
inspect whole near-background or apparently no-object fields where the available
development data includes them. Use faint-preserving raw views at context and
native scales, across relevant axes, to distinguish no supported target from dim
objects, debris or an unhelpful display. A percentile, histogram, low count or
one quiet crop alone does not establish that a whole field is empty. If this
stratum is unavailable, record that coverage limit rather than inventing it.

An automatic threshold is not an object-presence test. [Otsu's histogram
partition](https://bioimagebook.github.io/chapters/2-processing/3-thresholding/thresholding.html)
can separate brighter noise from darker noise even when no target objects are
present. Successful labels on signal-bearing fields therefore do not establish
specificity in no-object fields. Inspect threshold support and resulting labels
against matched raw/result/combined views in both strata before wider execution.

If background partitioning is the failure, a measured lower threshold bound is
one possible hypothesis only when the reflected callable supports it and the
[consumed intensity units](#current-processing-intensity-units), acquisition and
preprocessing mappings are comparable across fields. Measure background and
genuine dim-positive values on that alias; a source-unit floor cannot be copied
unchanged onto a normalised or remapped response. Check that the effective bound
rejects unsupported background while retaining dim-positive support and ordinary
positive boundaries. Do not infer a universal floor from dtype, an observed
maximum or a percentile-based blank classification. If the distributions overlap
or units are incomparable, reconsider the supported admission/preprocessing model
and retain the uncertainty instead of forcing a blank result.

### Choose the marker landscape before the first candidate

Measuring a body's diameter does not justify a declumping method. Before the
initial run, connect the bright/dim regional samples above to three decisions:
whether local body-versus-background contrast supports foreground admission,
whether intensity peaks represent bodies or texture within them, and whether
the proposed marker landscape distinguishes a genuine close pair. Use native
profiles or bounded samples to compare within-body peak distances and valleys
with the pair's centre spacing, boundary gap/neck and supported widths. Check
ordinary broad/oval bodies as well as small ones; diameter and seed separation
answer different questions.

Observed multiple peaks inside one continuous raw body invalidate **unexamined
intensity-maxima defaults** as a justified starting choice. They do not forbid
intensity-based markers: those need evidence that smoothing/prominence separates
within-body texture from genuine neighbours on the consumed image. Where the
supported foreground's shape better distinguishes compact touching bodies,
consider a declared distance/shape-based marker method; elongated or lobed
single bodies can also have multiple distance peaks. Neither landscape is a
universal watershed mandate. Foreground missing dim bodies needs an admission
or preprocessing decision, not stronger downstream suppression.

Reflect the callable's effective method and basic/advanced/automatic settings,
not just the arguments copied from a validated example. In the CellProfiler
primary-object contract, `use_advanced_settings=False` selects basic threshold
behavior; it does not justify the inherited declumping choices. Marker extraction
and watershed dividing-line landscapes are separate controls, and automatic
smoothing/suppression can override entered sizes. Inspect those effective
choices before assuming your measured settings are active. Before proposing
the first method, also justify the boundary landscape on the same isolated
body and genuine pair: plausible seed positions do not prove that intensity
or shape-based dividing lines will follow the supported inter-body boundary.
An internally textured intensity surface can cut one body unevenly even when
its markers are appropriate; inspect the expected seam as well as peak placement.
A validated example
supplies a working contract, not evidence that its intensity landscape matches
this raw morphology. Choose the method first, then justify smoothing, prominence
and minimum separation in that method's units, keeping the genuine pair and
faint body as simultaneous controls. When the callable retains marker or
landscape artifacts, inspect those alongside support in the first bounded run.

Worked contrast: a broad continuous body has several internal intensity peaks,
while a genuine close pair has separate supported interiors and an intervening
valley. Local body/background evidence first supports admission that retains
the broad body and pair, not just their bright islands. Choosing a distance
landscape removes direct intensity texture from seed extraction, but lobes or
waists in that support can still produce several shape maxima inside one body.

Compare within-body and true-pair peaks on the actual smoothed intensity or
distance alias consumed by the marker extractor. On a distance transform,
an absolute peak-height cutoff measures distance to background (an inscribed
radius), not prominence or peak separation; its units follow the transform's
spacing. Exclusion distance uses the extractor's declared metric and coordinate
units, not body diameter or screenshot spacing. Propose smoothing, prominence
or exclusion from the measured nuisance-versus-neighbour landscape, rather than
assuming a switch to shape seeds establishes one marker per body.

Worked crowded-haze contrast: distinct compact raw bodies can sit inside one
broad admitted foreground region. Its distance transform measures distance to
the region's background, not to each raw body's boundary. A broad plateau or
bridge can therefore dominate shape markers even when the raw diameters and
entered separation look reasonable. In the first bounded candidate, compare
the actual support and landscape at the crowded bodies with an isolated body
and a faint positive. A distance peak spanning several raw bodies, or much
larger than their supported radii, is evidence against treating that landscape
as a body-scale measurement. Follow support, emitted markers, unfiltered basins
and retained labels: maximum-size rejection can hide a large merged basin and
make the final image look like absent signal.

If diffuse foreground causes the mismatch, test a justified admission or
background-correction change through the
[foreground diagnostics](segmentation-diagnostics.md#foreground-before-unclumping)
before increasing suppression or simply relaxing the size limit. Local
thresholding alone may retain the same haze; choose its model from measured
regional classes, not the word adaptive. Keep the faint positive and regional
nuisance controls, and judge recovered individual bodies rather than increased
counts or changed secondary-cell partitions. This contrast motivates an early
diagnostic, not a fixed threshold method, window size or requirement to perfectly
separate every crowded object before retaining useful detections elsewhere.

For neighbourhood maximum filters, peak-centre spacing alone does not predict
which seeds survive. A weaker genuine neighbour can lose its seed because the
footprint includes a brighter body's shoulder, even without including that
body's peak centre. Inspect the effective footprint and consumed smoothed
response around the weaker peak; distinguish this from explicit pairwise
peak-distance pruning. Check both the unequal-brightness pair and continuous
textured-body control when choosing suppression, rather than only comparing
their centre distances.

Competition scope is another part of that proposal: where a peak finder
competes per label, a binary support label groups all foreground together,
whereas distinct connected-component labels can restrict competition locally.
Changing that scope and spacing is not a spacing-only repair; a connected
component can still contain a genuine touching pair. If within-body and real-pair
peak scales overlap, reconsider a supported body-association/representative rule
instead of enlarging global exclusion. Predict one representative in the sampled
continuous body and two retained in the genuine pair, then inspect those local
controls and their supported dividing boundary in the first bounded candidate.
This is a morphology-grounded prediction, not a dataset count target or approval
gate; use [stage-specific diagnostics](segmentation-diagnostics.md) to test it.

Worked unequal-neighbour contrast: in a retained development comparison, a
distance landscape favoured an admitted bridge between raw-supported interiors.
A measured intensity response instead had two peaks and emitted distinct
markers, but the unfiltered basins differed while both witnesses mapped to one
accepted label. Changing the dividing-line landscape alone recovered their
local separation. This is a positive stage-linked boundary repair, not evidence
that intensity markers or dividing lines suit every body. An independent faint
neighbour remained merged: its raw peak was flattened in the consumed smoothed
response, and reducing smoothing did not resolve the final merge.

A later hypothesis multiplied distance by smoothed intensity raised to a power.
Estimated distances and brightness values at body centres and a neck explained
the proposal; they did **not** measure the consumed response. Neither a larger
estimated product at a centre nor a changed exponent establishes a local
maximum in the extractor's neighbourhood. Raw brightness is not its smoothed
factor, and within-body texture or an admitted bridge can still compete with
the faint neighbour. The retained final labels alone did not locate that loss.

For such a hypothesis, use the declared diagnostic artifacts and existing
`openhcs_measure_viewer_polyline` or bounded `openhcs_sample_viewer_window_image`
operations to link same-coordinate faint interiors, within-body texture and a
genuine pair to actual support, consumed response, emitted marker IDs,
unfiltered basins and accepted labels. Keep alias/source/axes and units with
the receipts. Inspect available factors as well as their combination; a line
profile alone cannot establish all two-dimensional maxima. Distinguish missing
admission or response peaks from competition that excludes a peak, then from
a seeded basin lost during partition or acceptance. If factors or stages are
not exposed, retain that attribution limit rather than treating formula
estimates as measurements. An uncomputed response remains a provisional first
candidate; its bounded diagnostic can guide the next stage-specific repair,
with the continuous-body and genuine-pair controls where available.

### Native ruler, profile and independently specified region operations

Availability is determined by the **live** capability registry, not this guide.
These source contracts accompany [issue221](https://github.com/OpenHCSDev/openhcs/issues/221);
PR225 is merged and its installed synthetic MCP/native viewer journey at
OpenHCS fbf6b2d91 / PolyStore1209068 verified a cropped two-channel fixture,
empirical measurement, snapshot and native close. The earlier source proof
also verified unchanged raw pixels/presentation and shared-cache/no-download
child policy. Neither proof establishes physical calibration or biological
accuracy. Both operations are read-only and
require a settled, scalar, non-multiscale image route in a native YX 2-D display.
Unbound stacks/RGB, ambiguous records, missing axes, sparse padding, nonfinite
inputs/pixels and out-of-bounds geometry fail explicitly; no coordinate clamps.

Both tools take `host="localhost"`, required `port`, optional `transport_mode`,
`timeout_ms=5000`, the exact `route_key`, **all** route-local component
`axis_indices` (zero-based; `{}` only for a route with no component axes), and
`vertices_yx` as source-native `[y,x]` pixel-centre pairs. Discover route-local
axes and labels from viewer state/payloads; do not guess channel index from its
name. Coordinates include the streamed record path (which may be virtual),
producer, channel/component
values, selected aggregate plane, source origin/shape/spacing, layer axes,
scale/translation and declared world units. Returned world vertices use the
full native `data_to_world` transform, including affine rotation/shear.
`physical_calibration_verified=false`: declared units/spacing are provenance,
not independent calibration; scale1 is not proof of micrometres.
Retain the stream inventory's virtual-to-physical source mapping with the
measurement receipt. Check the returned source domain/spacing against original
declared metadata before interpreting source-native or transformed quantities:
the c662202df live attempt has a retained inventory-stream failure reproducer that
loses crop/spacing metadata. A mounted scale1 plane is not acceptance of the
original acquisition coordinates. That attempt's snapshot contract also failed
on an unmatched child dependency import; the historical dependency SHA was not
captured. Those failures remain preserved, not retrospectively called passes.
The repaired inventory retains the original nominal source projection; ordinary
crop admission is separate from strict full-window receipt replay. Initialized
exact submodules plus the existing launcher/source bootstrap resolved the fresh
child snapshot failure. A paired installation needs its own proof rather than
inheriting source-pinned acceptance.
The synthetic acceptance receipt is
`tests/runtime_diagnostics/viewer_feature_measurement_live_accepted_20260929.json`;
its capture states retain exact axes, routes, native transforms, camera and
numeric windows. Boolean/outside/sparse requests fail live; a NaN dev-client
input becomes null before schema rejection, so native nonfinite-guard proof is
source-level rather than literal-NaN arrival through that transport.

`openhcs_measure_viewer_polyline` accepts 2..64 vertices and optional
`line_width=1` (1..31), `interpolation_order=1` (0 nearest or1 bilinear),
`max_samples=4096` (1..4096) and `max_pixels=262144` (1..262144).
Two vertices give a ruler; more give a path. Results distinguish `data_length`
and `data_chord_length` in pixels from `world_length` and
`world_chord_length` in declared world units. The profile includes
`profile_distance_data`, `profile_distance_world`, `profile_values` and raw
statistics. Each segment uses `ceil(length+1)` endpoint-inclusive samples;
shared junctions retain the preceding segment's sample. Width is a centred
perpendicular pixel band reduced by mean, not a radius. The full band must
fit real source support before interpolation. Constant exterior0 is the
interpolator convention, not permission to measure outside source support.

`openhcs_measure_viewer_region` accepts 3..64 vertices forming a simple polygon
(closure is implicit; do not repeat the first vertex). Optional arguments are
`background_vertices_yx` (a separately specified 3..64-vertex polygon),
`support_threshold`, `background_sigma=2.0` (finite, nonnegative), and
`max_pixels=262144` (1..262144). Foreground/background selected pixels may not
overlap. Results separate continuous `polygon` area/perimeter/extent/roundness,
transformed `world_area`/`world_perimeter`/`world_roundness`, and `raster`
pixel-centre geometry from `skimage.regionprops` (boundary centres included,
exclusive upper bbox bounds, 4-neighbour perimeter). Roundness is
`4*pi*area/perimeter^2`, not clamped; raster perimeter may give values above1
on tiny regions. Polygon geometry is **not a biological object mask**.

`statistics` and optional `background_statistics` report raw-value count,
minimum, maximum, mean, median, population standard deviation (`ddof=0`) and
total in float64. Support is raw values **strictly greater** than
`support_threshold`; if omitted with a background polygon, the threshold is
background mean plus `background_sigma` times its population standard deviation.
Without either threshold or background, support quantities remain null. The
foreground-minus-background mean is reported separately; it does not replace
raw statistics. Window and raster/interpolation work budgets are checked before
pixel copies, masks or interpolation; lower `max_pixels` to constrain a request.
Neither operation changes source pixels, contrast/gamma, transforms, camera,
axes, selection or mounted layers.

Sampling and ROI summaries are not a dedicated ruler or line-profile contract.
If the live registry lacks the required operation, record the missing input/
output contract and use the [custom-function route](custom-function-authoring.md)
or report the limitation. Do not infer quantitative lengths from a resized
screenshot, inject mouse input, or substitute unregistered console/array analysis.
Simple arithmetic on returned coordinates is distinct from a reproducible image
measurement. The read-only ruler/profile/region sampling contracts described
here preserve their source pixels and report coordinates, axes, units and
sampling conventions. That read-only boundary does not prohibit analytical
preprocessing of working arrays in a pipeline. Retain acquisition source and
processing provenance; a native layer scale of1 does not verify physical
calibration.

## Current processing intensity units

Before choosing a threshold or prominence, identify the **current consumed
alias**, its producer/channel/axes, dtype, numeric range and processing history.
Raw-source samples establish acquisition values, not the units of a later
processed alias. Viewer contrast limits, gamma and colours change presentation,
not analytical pixels or callable bounds. Inspect the exact registered contract
and current-alias values together; a data maximum is not a threshold-unit scale.

CellProfiler-compatible image conversion scales integer inputs by their
applicable codebook but preserves floating values. `float32` therefore does not
prove unit-interval data. Acquisition dtype/maximum metadata describes source
provenance, not whether current floats still need conversion; using it blindly
can double-normalise a processed image. CP threshold bounds declared in `0..1`
are normalised processing units, not an invitation to substitute the observed
raw maximum. Do not generalise those bounds to other callable contracts.

**Worked clamp contrast:** a regional floor separates sampled noise from one
dim positive, but weaker raw-supported positives elsewhere overlap that noise
range on the consumed alias. Lowering a threshold correction factor recovers
one connector while those weaker objects remain absent. If the declared callable
multiplies its estimated threshold by the correction factor **then clamps** to
the lower bound, an unchanged floor can prevent testing the weaker regime at all.
Compare effective cutoffs and threshold support at distributed weak positives
and nuisance controls in current-alias units; raw measurements require the
verified conversion rather than direct reuse. Where their distributions overlap,
reconsider the admission model or justified preprocessing, or qualify sensitivity
limits—not automatically lower every floor. A measured floor can remain useful
for specificity; recovering one above-floor connector does not validate its
sensitivity elsewhere.

If conversion is justified, retain acquisition source/provenance and compose
a distinct processing alias through the existing registered intensity
owner, such as registry ID `openhcs:cellprofiler_rescale_intensity` (Python
`rescale_intensity`). Discover and describe the returned ID's current contract,
including typed mode and input/output semantics; choose a scale only from justified acquisition
or processing evidence. Do not infer `255` from a float dtype, silently auto-minmax,
or rescale already-normalised pixels again. If the scale is unknown, retain that
limitation rather than manufacture comparable units. Verify the resulting alias
values and earliest threshold-support artifact before interpreting objects.
Preserve an appropriate named original or calibrated intensity route where the
photometric claim requires it; this does not require geometry measurements to
consume untreated intensities.

The float-preservation and threshold-bound distinctions follow the
[CP Image conversion](https://github.com/CellProfiler/core/blob/v4.2.8/cellprofiler_core/image/_image.py)
and [CP Threshold settings](https://github.com/CellProfiler/CellProfiler/blob/v4.2.8/cellprofiler/modules/threshold.py)
contracts; they do not prescribe a scientific normalisation or establish parity
for every out-of-range input.

## Detection pixels versus measurement pixels

Thresholding, CLAHE, nonlinear gamma, high-end clipping, denoising and
normalisation can legitimately improve segmentation while changing working
analytical pixels and intensity relationships. Retain acquisition source and
processing provenance, not pixel immutability throughout the pipeline; creating
processed arrays does not authorise overwriting acquisition files. A display
upper-limit clip is presentation only; an explicit analytical high clip/remap
changes the array and must be recorded and validated.

Choose inputs according to the claim. Counts, morphology, length and area may
use labels, masks or traces derived from processed images, with validated
boundaries/connectivity and correct geometry/calibration. They do not all
require an untreated intensity image. Review distributed same-coordinate
raw/processed/result views for preserved faint paths, supported boundaries and
induced background bridges or artifacts.

For original-fluorescence or photometric claims, apply the detected mask to the
aligned, named original or appropriately calibrated intensity source. Do not
silently substitute clipped/remapped detection values, binary masks or label
colours. Record which image and mask/trace each measurement consumes. Mean and
integrated intensity differ from geometric area; background correction and
excluded pixels must be explicit for the quantities they affect.

Check saturation, acquisition settings and appropriate controls before comparing
conditions. An attractive merged figure is not evidence of equal exposure or
linear quantitative response. Segmentation error can select brighter cells
preferentially and bias intensity even when total counts appear plausible.

## Dimensionality and calibrated quantities

Distinguish 2-D plane measurements, projected measurements and true 3-D objects.
Check `openhcs_dimensionality_and_measurements` and the exact callable contract.
Stacking plane-local labels does not establish volumetric identity. One object
seen in several planes must not automatically become several independent cells.

XY area uses both pixel spacings; volume also requires Z spacing. Anisotropic
voxels require appropriate filter scales, distances and surface calculations.
For example, a physical Gaussian width of 1 micrometre corresponds to sigma
2 pixels in XY at 0.5 micrometres/pixel, but sigma 1 in Z at 1 micrometre/plane.
That is a units example, not a recommended smoothing setting. Resampling to
isotropic voxels can increase memory dramatically and changes image geometry;
prefer a spacing-aware implementation when available. Missing calibration is
an explicit limitation, not an invitation to guess a cell diameter in microns.

## Colocalisation is not one interchangeable score

Compare physically aligned channels with verified source, spacing, Z/time
indices, registration and ROI. Saturation, bleed-through, shared background,
noise and misregistration can affect apparent overlap. Preserve the scientific
planes rather than analysing an RGB composite. A projection can make signals
at different Z positions appear to overlap.

Pearson correlation measures linear intensity association, not the fraction of
objects sharing a compartment; zero Pearson does not prove statistical
independence. Manders-type overlap fractions depend on direction, inclusion and
threshold conventions. Two directional fractions can differ. Object-based
overlap or nearest-neighbour questions require segmentation and geometry, not
just a pixel correlation score. No one metric establishes molecular interaction.

Select the biological question and controls first, then inspect the registered
metric's definition, thresholds, ROI, zero/undefined handling and sample unit.
Test correction choices on controls; background subtraction is not universally
beneficial. For a randomisation significance test, report the exact returned
statistic and null model. Do not relabel a proportion of shuffled correlations
as a conventional p-value or copy a plugin's `>0.95` rule without its definition.
Uncertainty and randomisation units must reflect spatial dependence.

## Experimental units and exports

Cells, fields and technical wells are not automatically independent biological
replicates. Preserve specimen, condition, plate/well/site, object identity and
measurement units in export. Aggregate at the intended experimental unit and
retain the hierarchy; pooling thousands of pixels or cells does not create
thousands of independently treated samples. Keep controls and exclusions
visible. A statistical report must separate effect, variability and independent
sample size from image-level counts.

When measurements request several sources or slices, reconcile their intended
coverage with the compiled source bindings, invocation/grouping and typed
artifact inputs through `openhcs_inspect_pipeline_source_artifact_plan`, then
discover the exposed export-read or quantitative-results capability and check
actual source, object and slice identities and own-source values. Successful
execution can still deliver only one requested source; an unchanged label
artifact does not establish measurement coverage. Derive expected coverage from
the callable and export's declared long/wide layout, plane-local versus
volumetric identity, aggregation and exclusions—not a universal Cartesian grid
or grouping setting. In a long-format table, blank columns belonging to another
source can be legitimate when each row's own-source measurement is present.
Distinguish those blanks from an absent requested source, omitted eligible
object/slice or genuinely missing value; retain justified exclusions and any
preview truncation rather than treating a partial table as a complete export.

## Figures and reporting

Use lossless scientific artifacts for reanalysis. A PNG/WebP screenshot or RGB
figure is a presentation artifact and must not replace the acquired channels or
labels. Record numeric windows, nonlinear transforms, channel identities and
geometry for a final figure. Use a physical scale bar only when calibration is
known; otherwise disclose the missing calibration. Keep grayscale channel views
available and choose accessible colour combinations. Do not paint annotations
into analysis pixels or conceal raw features under filled overlays.

For comparison panels, apply a justified shared mapping rather than convenient
independent auto-contrast. Retain the representative-selection rule, full field
and native witness crops; disclose processing and exclusions. Image-publication
checks complement biological review but cannot certify the segmentation.

## Sources and adaptation

Adapted from Pete Bankhead's [Pixel size & dimensions](https://bioimagebook.github.io/chapters/1-concepts/5-pixel_size/pixel_size.html), [Multidimensional processing](https://bioimagebook.github.io/chapters/2-processing/7-multidimensional_processing/multidimensional_processing.html),
and [Files & file formats](https://bioimagebook.github.io/chapters/1-concepts/6-files/files.html)
via Agentic-J's CC BY 4.0 course (book commit
`a017bbc2656a747ab3c87e5d721e9897881ed4c2`, Pete Bankhead).
Inspected Agentic-J's [Coloc 2](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/coloc2_documentation)
and [publication](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/image_publication_standarts) packs at `7f3e1f0`;
the [official Coloc 2 documentation](https://imagej.net/plugins/coloc-2)
is the source for plugin metric interpretation. This guide does not import
plugin-specific significance thresholds or promise a particular metric exists
in OpenHCS. See the biological-evidence reference for the quantitative-bioimaging
and publication-checklist sources underlying these review boundaries.
