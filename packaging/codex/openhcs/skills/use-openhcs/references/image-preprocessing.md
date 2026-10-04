# Choose and test microscopy preprocessing

Start from a failed raw biological witness, not a favourite filter. Establish
the target channel, the structures that must survive and a specific nuisance
model. Retain acquisition source and provenance as a reproducible reference;
creating or modifying working analytical arrays is normal pipeline processing,
not permission to overwrite acquisition files. Distinguish detection pixels,
claim-appropriate measurement inputs and display settings. These recipes are
hypotheses, not unconditional steps to concatenate. Discover and describe the
compatible registered OpenHCS
callable before choosing parameters; the live contract owns backend, dtype,
axes, units and artifact flow.

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

One shared position artifact keeps channel placement consistent, but does not
prove that tiles are aligned. Inspect overlaps for repeated nuclei, parallel
process ghosts and broken continuations in separate raw channels, not only a
composite or a matching position list. A composite used to estimate placement
is a registration input, not an analytical channel merge: follow the canonical
assembly branch, reload original channel stacks and apply the shared positions
to raw or explicitly justified normalised inputs. Judge registration separately
from pooled scaling; a repaired local join does not validate every seam.

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
