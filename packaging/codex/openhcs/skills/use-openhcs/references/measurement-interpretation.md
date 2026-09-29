# Choose valid microscopy measurements and comparisons

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
