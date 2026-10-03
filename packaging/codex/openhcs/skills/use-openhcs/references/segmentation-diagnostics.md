# Diagnose microscopy segmentation by stage

Use this guide after identifying the raw target and the first failed stage.
Retain the foreground, marker, label or secondary-growth artifact needed to
distinguish hypotheses. Use the canonical viewer contexts and [viewer QA procedure](viewer-qa.md) for matched
raw-only/result-only/combined review. Never change several unrelated parameters
just because the final count seems implausible.

## Foreground before unclumping

Inspect whether the intended foreground contains whole objects, connected
neighbours, noise or just bright subcellular parts. A good seed strategy cannot
recover cell bodies absent from its support mask. Compare local raw backgrounds,
histograms and the threshold's assumptions; use the preprocessing guide when
the foreground failure is illumination, noise or contrast. Record connectivity:
4/8 in 2-D and 6/26 in 3-D produce different connected objects.

For all-foreground or empty support, compare the reported threshold with values
from the **current processing alias**, not only the physical source or viewer
window. Check [current processing intensity units](measurement-interpretation.md#current-processing-intensity-units)
before changing seeds, watershed or threshold bounds. A threshold clipped to a
normalised contract bound can be incompatible with unscaled float pixels;
raising a final bound need not undo an earlier clamp. Establish the units and
earliest failed operation first, preserving raw and any explicitly converted
alias rather than retuning downstream stages to compensate.

### A threshold fixes one region but damages another

Keep a bright touching pair and a genuine faint positive in different regions
as simultaneous controls. If raising a global threshold separates the bright
pair but removes the faint positive, while lowering it restores the positive
but joins neighbours or admits background, the opposite outcomes are evidence
against that global foreground choice. Do not alternate global factors until
one crop looks good. Inspect local background and foreground values on the
current processing alias, then test a justified background correction or local
threshold through the [preprocessing guide](image-preprocessing.md). If support
already preserves both controls, diagnose markers and splitting instead; a
threshold failure is not established by an incorrect final partition alone.

Trace a missing object through threshold support, initial components, seeds,
unfiltered labels and retained labels. A bright merged component removed by a
maximum-size filter is not evidence of absent signal; relaxing that filter may
only retain the merge. A faint object present in support but absent after
splitting or size filtering needs a different repair from one absent in support.
Use the retained stages to locate the first loss before choosing the next
change. Recheck both original controls and distributed raw/result/combined
views; a corrected count or repaired cluster cannot excuse new faint misses.

## Touching round objects and watershed

A distance-map/marker-controlled watershed is a candidate for separating
touching compact objects, not a universal definition of a cell. Inspect the
support mask, distance or intensity landscape and seed positions independently.
Many internal intensity maxima can split one continuous nucleus. Too few
markers can merge genuine neighbours; a correct marker outside the support mask
cannot rescue an absent object.

For a suspect split, inspect native raw under a faint-preserving and a
detail-preserving window. Are there distinct raw bodies and a credible valley,
or internal texture inside one body? Keep a true close-pair control elsewhere.
Test one change to seed prominence, minimum separation, smoothing or splitting
method. Prominence/H-maxima depends on the landscape's numeric units; a tolerance
from an 8-bit intensity example is not a calibrated distance-map setting.
Compare both crops after the change, not just the repaired split.

For point-only object counts, maxima are candidate landmarks, not automatically
distinct bodies. Track all candidates belonging to each sampled raw body
through Z and orthogonal views, including candidates hidden on other slices;
check bodies with several candidates and bodies with none. When internal
texture produces several candidates, test a supported body-association and
representative rule, not a larger global suppression distance alone; retain
a genuine close-pair control. Declare the centre convention and boundary
policy: a strongest-intensity voxel inside a body is not geometric-centre
validation. Check centre placement against supported body extent and keep
unresolved identity separate from ordinary detection errors; a connected
foreground region can still contain touching neighbours.

Distance and watershed operations in anisotropic Z data must respect spacing.
A distance in voxel indices is not necessarily a distance in micrometres.
Use the measurement guide before interpreting a 3-D separation or shape value.

## Primary-to-secondary cell bodies

For nucleus-seeded cytoplasm, verify the nuclear channel separately from the
body channel, their alignment and seed/artifact binding. Inspect the body
support and growth boundaries, not just matching IDs or counts. A retained seed
can masquerade as a successful cell segmentation: compare each secondary area
with its own primary area and inspect zero-growth or implausibly large objects
on raw body signal. At a crowded boundary, check whether two seeds grow into
distinct supported bodies or divide one diffuse field arbitrarily.

DAPI candidate count does not establish cell-body count. Require independent
body-channel boundary support before admitting or splitting a second cell;
another overlapping nuclear candidate alone is insufficient. Do not assume a
universal one-nucleus-to-one-cell relation.

Change the failed support/growth parameter rather than compensating with more
primary seeds. If the stain shows only a subcellular structure, record that a
whole-cell boundary is unsupported instead of manufacturing cytoplasm masks.

## Puncta, neurites and topology

Scale-selective spot enhancement can help puncta detection; compact-object
unclumping parameters are not automatically appropriate for a thin branched
network. For neurites, inspect supported soma-to-process connections, continuity,
branchpoints, endpoints and close crossings. Threshold gaps can shorten or
fragment paths; background bridges can create false branches or connections.

Skeleton pixels are not physical length by themselves: diagonal steps, spacing,
projection and branch assignment matter. Do not interpret every disconnected
bright focus as a missed neuron. Ambiguous debris or dying cells should be
logged separately while clear supported misses are diagnosed. Adding a closing
operation or pruning short branches can repair one crop and remove genuine
biology elsewhere; retain a faint-path regression control.

## Learned-model choice and operational limits

Model training domain and object representation matter more than a generic
"best model" claim. Star-convex nucleus models and whole-cell/irregular-object
models answer different tasks. Fluorescence, H&E RGB and brightfield inputs may
require different trained models and normalisation. Check the current callable,
model version/weights, channel mapping and dimensionality. Agentic-J's Fiji
StarDist plugin's 2-D limit is not a statement about every Python StarDist
implementation; its GPU model preference is not an OpenHCS default.

For large images, inspect memory and the model's supported tiling/overlap. Tile
boundaries can produce duplicates or fragments, and per-tile normalisation can
change detection. Native-coordinate review must include a tile edge and a
whole-object context crop. Use an existing resident/batched route when supported;
do not add hidden environment installation or launch a separate tool runtime
to bypass OpenHCS contracts.

## Labels and cleanup

Keep labels as discrete IDs with background semantics from the artifact
contract. Colour maps, max label value and ROI row count are not reliable
object counts when IDs are sparse, filtered or duplicated across planes.
Count actual identities within the declared scope and reconcile measurement
rows/relationships. Never stretch labels as intensities; resampling requires
label-aware handling. Area/border filters change the population: retain their
units, reasons and excluded fraction rather than hiding exclusions as cleanup.

## Sources and scope

Adapted from Bankhead's [Thresholding](https://bioimagebook.github.io/chapters/2-processing/3-thresholding/thresholding.html), [Morphological operations](https://bioimagebook.github.io/chapters/2-processing/5-morph/morph.html) and [Image transforms](https://bioimagebook.github.io/chapters/2-processing/6-transforms/transforms.html),
via the Agentic-J course at `7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67`
(Pete Bankhead, CC BY 4.0, book commit `a017bbc2656a747ab3c87e5d721e9897881ed4c2`).
Also inspected Agentic-J's [MorphoLibJ](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/morpholibj_documentation), [Cellpose](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/cellpose_documentation), [StarDist](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/stardists_documentation) and [3-D suite](https://github.com/MMV-Lab/Agentic-J/tree/7f3e1f0888cd06f22ebdfb5cf1fc43d0e7769a67/skills/3d_imagej_suite_documentation) packs.
Their plugin-specific defaults and automation scripts are not imported. The
stage-control and regression-review protocol is an OpenHCS adaptation.
