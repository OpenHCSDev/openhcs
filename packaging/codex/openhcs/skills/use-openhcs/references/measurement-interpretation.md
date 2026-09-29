# Choose valid microscopy measurements and comparisons

## Measure feature scales before choosing parameters

Use this procedure before setting object diameter, seed separation, smoothing,
background-removal scale, spot/ridge width or a shape prior. Base a starting
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
   across preselected bright/dim, sparse/dense and centre/edge regions. Retain
   extremes and ambiguity rather than measuring only objects the current
   detector finds. For 3-D, inspect multiple Z planes and orthogonal views when
   exposed; a projected width does not establish Z extent.
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
   | Smoothing/spot/ridge scale | Narrowest supported feature width, noise texture and nearby close-pair/path control | Equating diameter with Gaussian sigma or erasing a faint neurite |
   | Background-removal scale | Target width plus extent and variation of nearby background in multiple regions | A universal kernel radius or subtracting cell signal as background |
   | Threshold/prominence | Raw object-versus-local-background values, weak positives, noise and saturation on the consumed channel | Deriving analytical thresholds from contrast limits, gamma or label colours |
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
   and uncertainty, chosen callable/parameter, unit conversion and rationale in
   the trial log. Summarise the observed range and regional variation. Reflect
   the exact registered callable before applying a number: radius versus
   diameter, sigma versus kernel width, anisotropic spacing and intensity units
   differ between algorithms. Keep unsupported precision as an interval or
   limitation. Label mask-derived estimates provisional and check against raw,
   including missed objects; do not tune a detector solely from its own output.
6. Compile one bounded candidate, inspect its earliest changed intermediate,
   then compare matched raw/result/combined at the measured failures and
   regression controls. Revisit distributed regions after every change; a
   local repair can fail elsewhere under uneven illumination. Freeze measurement
   receipts and rationale with the complete candidate before held-out access.
   Expected counts or reference masks must not choose measurements in a blind run.

Sampling and ROI summaries are not a dedicated ruler or line-profile contract.
If the live registry lacks the required operation, record the missing input/
output contract and use the [custom-function route](custom-function-authoring.md)
or report the limitation. Do not infer quantitative lengths from a resized
screenshot, inject mouse input, or substitute unregistered console/array analysis.
Simple arithmetic on returned coordinates is distinct from a reproducible image
measurement. Any measurement operation must preserve source pixels and report
its coordinates, axes, units and sampling conventions; a native layer scale of1
does not verify physical calibration.

## Detection pixels versus measurement pixels

Thresholding, CLAHE, nonlinear gamma, high-end clipping, denoising and
normalisation can improve detection while changing intensity relationships.
Use the detected mask on the aligned untreated or separately validated corrected
measurement image. Record which image each measurement consumes; never silently
measure fluorescence on the binary mask, label colours or detection enhancement.
Mean, integrated intensity and area answer different questions. Background
correction and excluded pixels alter those quantities and must be explicit.

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
