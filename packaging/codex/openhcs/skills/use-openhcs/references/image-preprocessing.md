# Preprocessing for image analysis

Start from the failed biological witness, not a favorite filter. Identify the
target channel, the structures that must survive, and the nuisance that
currently prevents their detection. Sample raw pixels and local distributions
across bright/dim, sparse/dense, center/edge regions; compare these with the
same-coordinate raw-only, result-only, and combined views. Preserve the
untreated image as an independent route and use it for quantitative intensity
measurements unless a corrected measurement image is separately validated.

## Choose a testable recipe

- Bright outliers set an unhelpful scale: test a *bounded high-end clip followed
  by rescaling* or a gentle monotone tone curve. Record the input percentile or
  value and output range. Compare saturated objects and faint boundaries;
  clipping can erase real intensity differences. Viewer contrast limits and
  gamma are display-only diagnostics unless an explicit processing function
  applies the transform to the analytical image.
- Slowly varying *additive* background obscures bright objects: test a
  background estimate and subtraction, such as an appropriately sized white
  top-hat. Choose a scale larger than the structures to retain. Compare raw and
  processed object extent, halos, and weak connected signal. A radius near the
  cell-body or neurite size can remove the biology with the background.
- Repeatable *multiplicative* shading across comparable fields: estimate a
  channel-specific illumination field and test division; use subtraction only
  for an additive model. Do not learn a field from treatment-dependent
  morphology or mix channels/conditions. One uneven image alone does not prove
  illumination bias.
- Speckle or high-frequency noise creates false markers: test mild smoothing
  below the smallest relevant feature scale, then check lost puncta and split
  boundaries. If the source changes abruptly by region, compare adaptive
  thresholding before building a complicated correction chain.

Find the currently registered OpenHCS implementation with
`openhcs_search_functions`, then inspect its full contract with
`openhcs_describe_function`. Useful starting points are
`openhcs:cellprofiler_rescale_intensity`,
`openhcs:processors_numpy_processor_tophat`, and the paired
`openhcs:cellprofiler_correct_illumination_calculate` /
`openhcs:cellprofiler_correct_illumination_apply`. Search knowledge for
`openhcs_function_library` section `choosing-preprocessing` and the closest
Official30 illumination-correction `OpenHCS Python` section; these are recipes
to adapt, not evidence that they suit the current image.

For each bounded trial, change one analytical operation or one parameter group
and save the source, processed image, and exact numeric settings. If combining
high-end compression with background subtraction, test the individual effects
first, then the sequence; order matters because clipping changes the
background estimator's input. Inspect raw versus processed images under stated
windows at the same native coordinates and compare downstream masks against
the *raw* biological channel. Track restored misses, new merges/splits,
background leakage, zero-growth secondary labels, and supported faint paths.
Reject a prettier image if it worsens these biological controls. Hold-out data
remain sealed until the candidate pipeline and QA criteria are frozen.
