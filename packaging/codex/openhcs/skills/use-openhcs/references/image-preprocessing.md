# Choose and test microscopy preprocessing

Establish segmentation and tracing input units before tuning detection parameters.
For corrections, start from a raw biological witness and its nuisance,
not a favourite filter. Establish
the target channel, the structures that must survive and a specific nuisance
model. Retain acquisition source and provenance as a reproducible reference;
creating or modifying working analytical arrays is normal pipeline processing,
not permission to overwrite acquisition files. Distinguish detection pixels,
claim-appropriate measurement inputs and display settings. These recipes are
hypotheses, not unconditional steps to concatenate. Discover and describe the
compatible registered OpenHCS
callable before choosing parameters; the live contract owns backend, dtype,
axes, units and artifact flow.

## Establish detection inputs before tuning

Inspect the detector's declared dtype, intensity units and embedded operations.
Raw calibrated input is valid when its contract and observed support justify it;
normalization is not a compulsory extra filter. When normalization is required
by the callable or chosen to improve detection, declare its mapping, fit domain
and target range before choosing intensity-dependent parameters. If the existing
source/processing owner already supplies that input, verify it instead of
applying a duplicate transform. Internal feature rescaling does not establish
an externally requested input mapping.

Preprocessing may be separate FunctionSteps or earlier callables in the same
step's function chain. Both use ordinary registered operations and declared
source/axis contracts. Inspect embedded enhancement switches before adding an
external equivalent; retain only the operations whose contribution is supported
by raw/processed/result comparison. For optional neurite enhancement and its
admission gates, follow
[the detector diagnostics](segmentation-diagnostics.md#separate-support-recovery-from-rooted-graph-validity).

If rescaling is chosen, use a linear/percentile or other justified mapping through
a registered operation. For comparable fields sharing that mapping, follow
[shared scaling](#shared-scaling-for-fields-of-one-mosaic); keep that fit and
mapping fixed across the channel's fields. Measure thresholds and noise scales
in the actual consumed units, whether raw or transformed. Normalization
does not replace denoising, background subtraction or illumination correction;
select those operations from their nuisance evidence and record their order.

Processed pixels may legitimately clip bright bodies or change intensities when
the claim is segmentation, count, area or traced geometry. Validate faint
structures, neighbours and nuisance controls against raw. Original-fluorescence
quantification has a different input claim: preserve its appropriate original
or calibrated corrected source, rather than forbidding normalization of the
separate detection branch.

## Establish spatial coverage before tuning

Choose development witnesses from the whole field before fitting a correction or
tuning a detector. Include observed bright/dim background, centre/edge and
sparse/dense regions, with a faint positive and a genuine close pair or thin path.
Use [the raw-only faint-structure scan](viewer-qa.md#reveal-faint-structures-and-nuisance-variation)
to expose faint paths, noise texture, background level and uneven illumination.
Keep those witnesses across trials; add newly discovered failures rather than
replacing inconvenient controls. Compare local background level/spread and
signal-to-background contrast. A dim region may reflect additive background,
multiplicative shading, focus, missing photons or genuine biology; do not flatten
it simply because it differs. Saturated acquisition values and lost focus are
not repaired by normalisation; intentionally saturated display highlights are
a different, reversible presentation choice.

Translate the observed nuisance into compatible declared operations. Depending
on the evidence, test rolling-ball background subtraction or a white top-hat
alone, denoising plus background subtraction, denoising plus flat-field and
background correction, or another justified sequence. These are alternatives,
not a mandatory stack or ordering. Distinguish additive background from
multiplicative shading, focus loss and genuine diffuse biology before choosing
a correction. Discover and describe each live callable's units, axes and artifact
contracts rather than assuming a method name establishes compatibility.

Review the correction field or denoising residual, raw/processed images and
downstream labels across the same positions and scales. Record numeric display
limits in each image's units; independent auto-contrast can hide a failed
correction. Local improvement is insufficient if other regions develop misses,
merges, erased faint structures or unsupported foreground. Keep held-out pixels
sealed while choosing the method, fitting sample, parameters and QA criteria.

## Bright outliers and compressed display range

First compare numeric display windows using the linked raw-only scan; a few
bright objects may only make the viewer unhelpful. If an explicit detection
transform is needed, test a bounded high-end clip/rescale or monotone tone curve
on the development sample. Record
the input percentile/value, output range and whether fitting is shared across
fields. Saturating bright somas in a suitable analytical transform is acceptable
for segmentation if distributed raw/processed/result QA supports the required
boundaries, faint paths and connectivity without induced background bridges or
artifacts. Inspect both bright-object boundaries and faint positives; saturation
alone is not a rejection gate. Analytical clipping changes working pixels,
unlike a display-only upper limit. It can erase intensity differences, and gamma
changes their relationships. For original-fluorescence photometry, choose the
appropriate original or validated calibrated intensity source rather than
silently substituting the detection transform; see
[measurement-image choice](measurement-interpretation.md#detection-pixels-versus-measurement-pixels).
Do not silently apply per-field normalisation to treatment comparisons.

### Shared scaling for fields of one mosaic

For fields belonging to the same well or mosaic, fit one low/high percentile
pair over the complete field stack **per channel**, then apply that shared
mapping to every field. This applies whether segmentation is field-by-field
or follows stitching; stitching is not required to obtain consistent scaling.
Independent field fits give the same raw signal different analytical values
depending on its neighbours and can distort seam and detection comparisons.
Use the canonical `image_analysis_workflow` assembly/grouping contract and
inspect the compiled SITE scope and live stack-normalisation callable: a
singleton field invocation does not pool the other fields. Keep channels and
unrelated wells separate unless the task explicitly calls for a wider fit.
Pooling the tiles and fitting a stitched image express the same shared-scaling
intent, but overlap duplication, blending and mosaic padding can change the
exact histogram. Record the fit domain rather than assuming identical bounds.

Consistent channel placement does not require one cross-channel runtime
artifact. For embedded acquisition geometry, discover and describe
`acquisition_tile_positions`: its declared route uses SITE as the variable
component and CHANNEL grouping, producing each channel's ordered positions for
its compatible assembly invocation. Source ingestion validates common site
layouts across channels; a DAPI-only producer does not thereby supply a FITC
consumer. Inspect the compiled producer/consumer scope rather than treating
equal coordinates as permission to broadcast an artifact.

For image-derived registration, a composite or preprocessed image used to
estimate placement is a registration input, not an analytical channel merge.
Follow the canonical two-branch assembly recipe: estimate positions, then
reload original channel stacks and assemble raw or explicitly justified
normalised inputs. Reuse fitted positions across channels only where the live
artifact contract and compiled source relation support that scope and ordered
tile correspondence. Inspect overlaps for repeated nuclei, parallel process
ghosts and broken continuations in separate raw channels, not only a composite
or matching position lists. Acquisition-coordinate placement is not evidence
of image registration. Judge seam alignment separately from pooled scaling;
a repaired local join does not validate every seam.

## Slowly varying additive background

Test subtraction of a background estimate or a white top-hat. Its spatial scale
must exceed the structures to retain, not merely exceed the filter's default.
Compare a crop containing a broad cell body and one containing a thin faint
process. A small radius can subtract the cell itself; an excessively broad
estimate can fail to remove the actual nuisance. Inspect halos, negative values,
object extent, leakage and connected paths, using float arithmetic where needed.
Uniform detector offset, out-of-focus haze and biological diffuse fluorescence
are not automatically the same background model.

## Multiplicative illumination or shading

Repeatable channel-specific shading across comparable fields motivates an
illumination-field estimate and division. An additive dark offset must be
handled consistently with that model. One uneven field is not proof of shading:
compare fields/controls and avoid learning the field from treatment-dependent
morphology. Check small or invalid divisors and edge amplification. Search the
Official30 illumination examples and inspect the calculation/application pair's
source grouping, rather than fitting a fresh field independently for every
condition without justification.

### Shared-field calculation and application recipe

Discover `openhcs:cellprofiler_correct_illumination_calculate` and
`openhcs:cellprofiler_correct_illumination_apply`, then retrieve the closest
Official30 illumination pipeline. Fit one channel-specific field from comparable
development observations using the declared `calculation_scope`; `EACH` is a
current-invocation fit, while all-images scopes average the leading-axis
observations. Verify which physical fields the compiled grouping actually pools.
Never relabel Z as observations or pool independent channels to satisfy an array
shape. Reuse the named fitted artifact on the original image route, not on the
calculation output, and inspect its exact source/producer relation in the plan.

Choose `IlluminationCorrectionMethod.DIVIDE` for evidenced multiplicative
shading or `SUBTRACT` for additive background. Select estimation/smoothing scale
above the biology to retain, and inspect the field itself for cell outlines,
tissue gradients and tile seams. Inspect dim edges for amplified noise. Reflect
`truncate_low`/`truncate_high` and input scaling: the application's high clamp
is at 1, not the maximum of an arbitrary raw intensity range. Record clipping
fractions and preserve float analytical output when needed. Compare untreated
and corrected detection, not just background uniformity. Freeze the fit policy
and its data provenance before evaluation; using evaluation images to refit is
only permissible under an explicitly declared evaluation protocol.

### BaSiCPy recipe and readiness boundary

BaSiCPy's upstream workflow fits a flatfield, optional darkfield and observation
baseline, then transforms images. Use comparable same-channel observations with
changing foreground and shared acquisition shading; inspect the fitted fields
for biological structure before applying them. An observation stack is not
automatically a physical Z stack. Do not claim that the bundled NumPy/CuPy
BaSiC-style approximations are the upstream BaSiCPy algorithm.

Search and describe `basic_flatfield_correction_jax`, but treat registry presence
as discovery only. Confirm the installed BaSiCPy/JAX versions and a bounded real
fit/transform through the compiled runtime before selecting it. Inspect actual
parameter forwarding, observation grouping, output dtype/range and whether field
artifacts can be retained for QA. A missing package or misleading wrapper
parameter is an implementation gap, not a reason to silently substitute an
unvalidated approximation. Separate numerical smoke-test evidence from
biological acceptance across the distributed witnesses.

## Noise and false markers

For grainy foreground or too many local maxima, test mild Gaussian smoothing
below the smallest feature scale; for sparse impulsive outliers, test a small
median filter. Increasing smoothing can erase puncta, join close nuclei and
shorten thin processes. Photon noise is signal-dependent; background noise
alone does not characterise every bright object. Denoising cannot recover
unrecorded photons or saturated acquisition. Compare the same faint positive,
close pair and noise-only background before accepting a filter.

### Fast non-local means recipe

Choose the spatial domain before the implementation. For independent grayscale
planes, discover
`openhcs:processors_numpy_processor_non_local_means_denoise_planes` and confirm
its live `PURE_2D` contract. The existing contract slices the declared runtime
plane axis and restores the stack's metadata and provenance; scikit-image owns
the denoising algorithm. A singleton SITE axis is still an acquisition axis,
not evidence that the input should receive volumetric NLM. This operation
rejects bare volumes instead of guessing an axis. When patches should cross
physical Z planes, inspect the original
`skimage:restoration.denoise_nl_means` volumetric route instead. Compile the
actual source and axis scope; do not squeeze or relabel axes to select a method.

The per-plane operation exposes upstream `patch_size`, `patch_distance`, `h`,
`fast_mode`, `sigma` and `preserve_range`. Inspect the incoming dtype and
intensity units: upstream integer-to-float conversion and `preserve_range`
affect the meaning of `h` and `sigma`. Use a registered noise estimate or
bounded local statistics and test a modest noise-scale-based cutoff bracket,
not a normalised-image default applied to detector counts. Start with a small
odd patch below the feature scale and a bounded search distance. Fast mode
trades additional memory for speed; per-plane execution does not bound memory
for an arbitrarily large plane. Check the intended image size and working set
before widening a trial. A tiny compile/pixel-equivalence check proves an
engineering route, not preservation of faint biology on a new assay.

For CellProfiler recipe transfer, `openhcs:cellprofiler_reducenoise` remains an
alternative with its own full-stack contract. It uses fast scikit-image NLM,
names the upstream `h` parameter `cutoff_distance`, casts integers to float
without normalising their values, and does not expose `sigma`. Do not assume
the same settings have the same intensity or axis semantics across wrappers.
These CPU routes need no GPU or `torch_nlm`. Keep runtime-owned slice controls
out of callable kwargs; choose the declaration that owns the required behavior.

Review raw-minus-denoised residuals for erased puncta, bodies and thin
paths, plus denoised foreground/markers and downstream labels at dim and bright
witnesses. Reject newly joined neighbours or lost weak positives even if noise
looks lower. For original-fluorescence photometry, use the named original or
validated calibrated intensity source, not silently the denoised detection image.
Counts, morphology, area and path length may use validated processed-derived
labels or traces; follow the linked measurement-image guidance. NLM reduces
noise; it does not estimate a shading field or justify a globally tuned threshold
on uneven illumination.

## Weak rims and morphological gap repair

For a supported body whose rim is broken, closing is one hypothesis, not an
automatic way to obtain a cell envelope. Measure the within-body gap AND the
smallest supported gap between genuine neighbouring bodies on the consumed
response. A footprint smaller than the body radius can still bridge neighbours;
cell diameter alone does not justify its scale. Inspect the actual grayscale
or binary operation and its threshold order: their effects are not equivalent.
Compare foreground connectivity, markers and final labels at the broken rim
and the close pair. If the rim improves but the pair joins, retain that failed
trial and compare a smaller footprint or the unclosed support. Inspect
marker/partition behavior or another evidenced admission model rather than
assuming more closing is needed.

## Local contrast and local thresholds

CLAHE can reveal local structure but can also amplify noise and alter intensity
relationships. Use viewer windows first. If CLAHE is used for detection, retain
its tile/clip settings and inspect tile boundaries and background false positives;
do not measure intensity from the CLAHE image by default.

Adaptive thresholding addresses spatially varying foreground/background
separation only when the neighbourhood is meaningful for object and background
scales. Too small a neighbourhood can detect texture inside a body; too large
can approach the failed global threshold. Test dim edge regions and bright
centre regions, not just a single successful crop. Global Otsu is most plausible
when classes separate; a dominant background with a sparse foreground tail
requires checking that assumption rather than blindly choosing Otsu.

For textured/ring-shaped bodies amid diffuse nuisance, compare
[body-admission models](segmentation-diagnostics.md#compare-body-admission-models)
before choosing a correction: local background differences and intensity-class
separation fail differently. Judge corrected support against local body extent
AND regional negatives, not background uniformity, nuclear eligibility or a
preferred count. Opposite faint-loss/background-flooding outcomes motivate a
model change, not repeated scalar toggles.

### Body-scale contrast recipe

When soma-sized support is distinct from fine texture and broader haze, one
candidate is a smoothed body image minus a more broadly smoothed background.
Choose the finer Gaussian scale to suppress measured grain/internal texture
while retaining body envelopes and genuine neighbour valleys; choose the
broader scale to distinguish that support from the observed background.
Subtract through declared image artifacts in float, recording any negative-value
clipping and the actual input aliases. Serial Gaussian filters combine their
scales; smoothing the already smoothed body image is not the same declaration
as applying both filters independently to raw.

Measure clear bodies, dim rims and regional nuisance on the resulting response
before selecting its cutoff. Compare the support and final labels across those
positions: this model can recover broad somata while shortening weak rims or
removing thin processes. A body-detection branch need not also be the process
branch. Retain useful detections and their extent uncertainty separately, and
use the appropriate intensity source for photometry rather than this band-pass
response. The recipe is a conditional alternative, not a default or a claim of
validated whole-cell boundaries.

## Spots, edges and thin processes

Difference/Laplacian of Gaussian can enhance objects at a selected scale; ridge
enhancement can emphasise line-like structures. Their responses are detection
features, not preserved fluorescence measurements. Match scale to calibrated
structure width and inspect broader somata, faint branches, noise and halos.
Unsharp masking can introduce conspicuous edges without resolving real objects.
Do not use stronger enhancement as proof that a dim bridge is a neurite.

For faint structures connected to clear positives, consider high-confidence
seeds grown within a lower-threshold support mask (hysteresis/reconstruction).
This can retain supported weak structure but can also connect into background;
inspect endpoints, crossings and nearby disconnected debris on raw pixels.
Measure the response along the intended continuous path, including weak troughs,
not only its peaks. A threshold below every sampled peak can still erase the
connections between them. Compare those troughs with near-track nuisance and
far-background profiles in the same response units. Where this evidence supports
it, separate strong-seed admission from lower-threshold connected support;
inspect the retained mask before thinning and recheck faint endpoints and false
bridges. Two thresholds do not establish crossing ownership or guarantee that
weak paths remain distinguishable from noise.

If discovery finds no contract-compatible hysteresis/reconstruction callable,
follow [custom-function authoring](custom-function-authoring.md) on the intended
process owner. A typed registered operation using an appropriate existing
implementation is a normal pipeline step, not permission to process saved images
outside MCP. A negative search alone does not make the recipe unavailable;
check the proposed operation's actual axes, dtype, units and artifact flow.

## Discover compatible OpenHCS implementations

Search functions and inspect the full reflected contract before using a recipe.
Possible starting points are `openhcs:cellprofiler_rescale_intensity`,
`openhcs:processors_numpy_processor_tophat` and the paired
`openhcs:cellprofiler_correct_illumination_calculate` /
`openhcs:cellprofiler_correct_illumination_apply`; their availability and semantics
come from the live registry, not this note. Retrieve `openhcs_function_library`
section `choosing-preprocessing` and the closest Official30 illumination example
for declared composition, grouping and reference settings.

## Compose one falsifiable change

Test individual operations before their combination. Clipping or denoising
before background estimation changes that estimate's input; smoothing before
seeding changes its maxima. Record the actual operation order and each consumed
alias as part of the pipeline. Retain only necessary diagnostic
intermediates and compare raw/processed at matched coordinates with recorded
windows, then review downstream masks/traces against raw biological signal.
Inspect residuals or correction fields for removed faint positives, biological
structure and amplified noise. Recheck path connectivity and background-bridge
controls at the same coordinates, not only background uniformity.

Accept only when the predicted failure improves without erasing the faint
positive or creating new splits/merges/leakage. Check that secondary objects
actually grow beyond their own primary seeds. A successful run or prettier
background is not that evidence. Freeze the development candidate before
scoring held-out fields.

## Source and adaptation

Condensed adaptation of Pete Bankhead's [Point operations](https://bioimagebook.github.io/chapters/2-processing/2-point_operations/point_operations.html), [Thresholding](https://bioimagebook.github.io/chapters/2-processing/3-thresholding/thresholding.html), [Filters](https://bioimagebook.github.io/chapters/2-processing/4-filters/filters.html), [Morphological operations](https://bioimagebook.github.io/chapters/2-processing/5-morph/morph.html) and [Noise](https://bioimagebook.github.io/chapters/3-fluorescence/3-formation_noise/formation_noise.html).
Agentic-J's [course package](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/bioimage_course)
records book commit `a017bbc2656a747ab3c87e5d721e9897881ed4c2`,
CC BY 4.0, Pete Bankhead. Assay-specific recipes and validation decisions here
are OpenHCS adaptations, not parameter defaults demonstrated by that course.

Implementation references: scikit-image's [non-local means API](https://scikit-image.org/docs/stable/api/skimage.restoration.html#skimage.restoration.denoise_nl_means)
and BaSiCPy's [fit/transform example](https://basicpy.readthedocs.io/en/latest/notebooks/timelapse_brightfield.html).
These upstream interfaces do not establish local dependency or wrapper readiness.
