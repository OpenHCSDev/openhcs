# Choose and test microscopy preprocessing

Start from a failed raw biological witness, not a favourite filter. Establish
the target channel, the structures that must survive and a specific nuisance
model. Keep an untreated route and distinguish detection pixels, measurement
pixels and display settings. These recipes are hypotheses, not unconditional
steps to concatenate. Discover and describe the compatible registered OpenHCS
callable before choosing parameters; the live contract owns backend, dtype,
axes, units and artifact flow.

## Bright outliers and compressed display range

First compare numeric display windows; a few bright objects may only make the
viewer unhelpful. If an explicit detection transform is needed, test a bounded
high-end clip/rescale or monotone tone curve on the development sample. Record
the input percentile/value, output range and whether fitting is shared across
fields. Inspect both bright-object boundaries and faint positives. Clipping
can erase intensity differences, and gamma changes their relationships; use
untreated or separately validated corrected pixels for intensity measurement.
Do not silently apply per-field normalisation to treatment comparisons.

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

## Noise and false markers

For grainy foreground or too many local maxima, test mild Gaussian smoothing
below the smallest feature scale; for sparse impulsive outliers, test a small
median filter. Increasing smoothing can erase puncta, join close nuclei and
shorten thin processes. Photon noise is signal-dependent; background noise
alone does not characterise every bright object. Denoising cannot recover
unrecorded photons or saturated acquisition. Compare the same faint positive,
close pair and noise-only background before accepting a filter.

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

Test individual operations before their combination. Clipping before background
estimation changes that estimate's input; smoothing before seeding changes its
maxima. Record order as part of the pipeline. Retain only necessary diagnostic
intermediates and compare raw/processed at matched coordinates with recorded
windows, then review the downstream labels against raw biological signal.

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
