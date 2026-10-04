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

### Compare body-admission models

For broad textured or ring-shaped bodies in uneven granular background, inspect
outer-body support, dim interiors, adjacent background and nuisance-only patches
across bright/dim separated regions BEFORE choosing foreground admission. Use
values from the consumed alias alongside raw contours; a global histogram or
one central body cannot establish specificity elsewhere. A nuclear anchor may
support eligibility/association, but neither it nor a neuronal callable name
establishes body-channel boundaries.

- **Local body-minus-background admission** is a candidate when a meaningful
  outside-body reference separates positives from local nuisance. A neighbourhood
  contaminated by the body can subtract it; a permissive difference can instead
  admit diffuse/granular regions. Check complete extent and negative patches,
  not just whether a seed survives.
- **Intensity-class separation**, global where classes/background are comparable
  or local where variation justifies it, is a different hypothesis. Inspect which
  classes represent nuisance, weak body and bright rim, and how the declared
  method assigns them. Excluding an intermediate class can remove faint body;
  retaining it can leak into background. Adaptive/multiclass thresholding is not
  automatically superior: neighbourhood scale and class overlap still matter.

Choose from measured local positives/backgrounds and regional negatives, using
[preprocessing model selection](image-preprocessing.md#local-contrast-and-local-thresholds)
when nuisance or overlapping classes need correction. If lowering a scalar
restores dim positives but floods large regions, while raising it removes bodies,
another toggle is not an admission-model repair. A dramatic count/foreground-area
change is only a warning; matched support and negative controls identify the
failure. Revisit the model or preprocessing and predict its effect on both,
rather than selecting the count that looks plausible. If support is adequate but
partitions fail, move to marker/division diagnostics instead.

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
views; judge new faint misses by the
[distributed, claim-scoped quality criteria](analysis-strategy.md#scope-conclusions-to-the-evidence),
not by count agreement or a requirement of zero errors.

A below-minimum label can be the tiny bright island left by threshold shrinkage
inside a much broader dim raw body, not genuine small debris. Compare independently
measured raw chords/extent with admitted support and unfiltered geometry before
lowering the minimum-size filter. If admission caused the shrinkage, test that
stage while retaining the size rule and a bright crowded-pair control; relaxing
size alone can retain the island without recovering the body. Actual small raw
objects remain a separate inclusion-policy question.

## Touching round objects and watershed

Before the first candidate, use the measurement guide's
[marker-landscape selection](measurement-interpretation.md#choose-the-marker-landscape-before-the-first-candidate)
to connect body/background, within-body texture and genuine-pair geometry to
the method and its smoothing/separation settings. Measuring size alone does
not justify inheriting an example's intensity declumping or automatic defaults.

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

For point-only counts of extended objects, maxima are candidate landmarks, not
automatically distinct bodies. Track candidate multiplicity within each sampled
raw body across the axes present; in 3-D, inspect through Z and orthogonal views,
including candidates hidden on other slices. Check bodies with several candidates
and bodies with none. When internal texture produces several candidates, test a
supported body-association and representative rule, not a larger global
suppression distance alone; retain a genuine close-pair control. Declare a peak,
body centre or other representative rule according to the task, plus the boundary
policy: a strongest-intensity voxel inside a body does not validate its body
centre. Check the chosen representative against raw support without requiring
an exact volume, perfect mask or automatic centroid. Keep unresolved identity
separate from ordinary detection errors; connected foreground can still contain
touching neighbours. This body-association check is not a blanket requirement
for punctum-peak detectors.

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

When only a subset remains seed-sized, compare its body-channel signal with
supported secondary objects and local background under a faint-preserving window.
An independently visible body lost at a growth stage supports a model repair;
weak or absent boundary signal does not justify enlarging every secondary object
to match the nuclear count. Retain independently supported nuclear measurements,
and qualify or exclude affected body-dependent quantities with explicit identities
and denominators, following [claim-scoped conclusions](analysis-strategy.md#scope-conclusions-to-the-evidence).
Zero growth diagnoses the output, not by itself the biological cause.

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

### Separate support recovery from rooted graph validity

A faint-path admission repair can improve the mask and skeleton without
establishing a soma-rooted, per-cell graph. Inspect recovered weak paths together
with an empty-background witness, newly admitted disconnected fragments and a
clear thin positive. Then review soma interiors and exits, crossings and the
actual root/edge associations separately. Skeletonization of bright soma texture
can introduce medial-axis loops and apparent junctions that are not anatomical
branches. Do not count them as neurite branchpoints or length merely because a
backend returns those column names; inspect its soma-interior and ownership rules.

Neither blanket loop pruning nor a 2-D crossing establishes neuronal ownership.
Keep supported path geometry and the local sensitivity improvement at their
actual scope, withhold only unsupported ownership/topology-dependent claims,
and diagnose the earliest remaining graph stage rather than repeatedly changing
the foreground threshold. A binary skeleton is a candidate representation, not
proof of complete reconstruction; an unresolved crossing need not invalidate
independently supported paths elsewhere.

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
