H002 fresh10 pre-first measurement review
=======================================

Parent read the independent author's FIRST-rationale.md from
next-h002-fresh10-89-20261005/H002_FRESH10_89/author-workspace/output.
The record precedes first source authorship and distinguishes the retrieved
three-channel Official30 monolayer example from this single-channel uint16
60x256x256 volume. It does not inherit calibration or known object counts.

The author measured internal raw peaks versus a genuine neighbour pair,
ordinary and faint bodies versus nearby background, early-Z haze and axial
extent. It retrieved conditional marker/admission guidance before choosing
volumetric foreground and shape markers. These are concrete preparation
behaviours, not evidence of successful segmentation or causal skill benefit.

Parent opened these original MCP captures under the HDD science phase:

* raw-z29-native-body/20261005T020739257144Z_napari_6023_OpenHCS_Napari_Visualization.png
* raw-xz-y128/20261005T020445944070Z_napari_6023_OpenHCS_Napari_Visualization.png

The XY crop shows visibly textured continuous bodies: multiple bright internal
structures do not independently establish multiple nuclei. The XZ image shows
shorter axial support and diffuse surrounding haze. Both agree with the
author's stated reasons to examine whole-volume identity and foreground
admission instead of counting each slice or each intensity maximum.

No result-only or combined first segmentation was available in this review.
Therefore there is no first-attempt accuracy or whole-volume acceptance claim.
No parameter, coordinate or historical-result advice was sent to this author.
Review its completed support, marker and label witnesses before deciding
whether these measured hypotheses improved the actual result.

First execution checkpoint
--------------------------

Subsequent independent table readback from attempt01/staged-input_whole3d_v2/
results found 28 centre rows. The one-row image_count export agrees: 28 accepted
objects, volume shape60x256x256, support718474 voxels,15 support components,
29 markers/unfiltered basins,1 rejected small basin. The declared foreground
is9500 raw units and marker prominence3 voxel-distance units. This is table
reconciliation and stage evidence, not a reference accuracy score.

Parent opened the first-z34-raw capture20261005T022008027723Z and the separately
retained first-unsettled capture20261005T021908086089Z. They have different Z
positions/crops and the latter is explicitly unsettled. Do not treat these as
a matched QA pair or diagnose biological splits from their comparison. Settled
same-coordinate raw/result/combined witnesses and persistent 3-D identities
remain the next acceptance evidence. No feedback was sent to the blind author.

First z34 point presentation review
-----------------------------------

Parent opened first-z34-points20261005T022307653912Z and
first-z34-combined20261005T022308330743Z. Both visibly retain the raw image
with small green point markers. The original stdin's points-only request
selected the raw route while requesting the Points route visible. The existing
isolation options explicitly include the selected route in the visible set;
the canonical viewer-QA guide already explains this behaviour. These captures
therefore supply combined presentation only, not a verified result-only view.
No duplicate backend fix or added skill rule is justified by that request.

Visible markers coincide with several clear nuclear bodies. This establishes
useful local placement, not complete coverage: fractional-Z centres may be
shown on different slices and absent markers in this one plane cannot by
themselves prove a missed volumetric nucleus. Whole-volume label/point identity
and distributed settled views remain necessary for that specific conclusion.
No biological diagnosis or parameter coaching was sent to the author.

Independent presentation recovery and local partition review
------------------------------------------------------------

Parent subsequently opened first-z34-points-correct20261005T022455476572Z.
Raw imagery is genuinely hidden while the green points remain visible at Z34;
the author repaired presentation through its own ordinary MCP requests.
This demonstrates a successful independent recovery, not a new backend fix.

The bottom-Z34 label capture20261005T022634163848Z and combined-point
capture20261005T022633527063Z show the same local body layout. Several clear
body extents are covered and visible points are associated with their bodies.
However the upper-right continuous-looking rounded body is divided into two
coloured regions, and the lower central elongated body into several. These are
plausible excess partitions on this slice, requiring whole-Z identity and
support/marker review before a definitive biological split judgement.
The label capture retains underlying imagery; it is not a result-only witness.

Retain useful foreground/localisation separately from these partition concerns.
Do not equate 28 centres or one point visible on a slice with correct whole3D
instance ownership: fractional-Z visibility hides some other centres. The author
continues its independent review; no coordinate/parameter repair was supplied.

Author diagnosis and discriminating repair
------------------------------------------

The subsequently authored attempt01/RESULT.md explicitly rejects excess
partitions: the lower-border body has labels6/12/13 and the oval has labels3/4.
It retains a correct one-centre broad-body control. Attempt02/RATIONALE.md
changes only marker prominence3 to5 voxel-distance units, retaining foreground,
smoothing and minimum size. It predicts repaired internal basins while naming
the risk of merging a genuine pair. This is independent within-run diagnosis
and a proposed repair, not yet verified improvement or first-attempt success.

The first native job failed at viewer settlement after numerical processing
and materialization. The author preserves that failed status, reloads its
persisted points through ordinary MCP and records28 native points with exact
fractional Z. It disables direct pipeline streaming for the next candidate and
uses supported persisted-artifact review; this technical presentation change
is distinct from the marker change. Do not call the old job retrospectively
successful or infer numerical loss solely from viewer failure.

Parent opened corrected XZ raw/combined captures20261005T023120275740Z and
20261005T023127322184Z at y157. They preserve the same orthogonal field geometry.
The combined bitmap does not visibly establish all centre identities; a single
cross-section and point slice visibility cannot validate a whole3D census.

Unchanged repair and marker-neighbourhood diagnosis
---------------------------------------------------

Parent independently read the two image-count CSVs: both contain28 accepted
centres,29 markers and identical support718474 voxels despite prominence3 vs5.
Both actual centre CSVs have SHA256
9fad5e253ed4d9ab424adc02cea5dd7067c9b5e076de691c21ba64d9d476c134.
The author explicitly rejects attempt02 rather than mistaking a parameter
change or completed job for biological improvement.

Attempt03/RATIONALE.md identifies a different mechanism: h-maxima uses a full
neighbourhood while the custom operation groups its maxima with six-neighbour
component labelling. It proposes changing only maxima-component connectivity
to26 neighbours, retaining foreground/watershed connectivity and original
threshold/smoothing/prominence. This is the author's own source diagnosis and
proposed repair. Actual repaired geometry and pair retention are not yet proven.
The transferable lesson is to inspect operator neighbourhoods and marker
component identity when a stronger prominence leaves false splits unchanged,
not to prescribe one universal connectivity for every stage or assay.

Attempt03 numerical evidence now exists: parent diffed the original custom
operation against v3. Aside from its registered function name, the sole code
change supplies a full3x3x3 structure to maxima-component labelling. The saved
image-count table now contains26 centres/26 markers/zero small-basin rejections,
with unchanged support718474 voxels and15 components, threshold9500 and
prominence3. The mechanism changed actual marker partitioning where the earlier
prominence increase did not. This is not yet proof that all false splits are
fixed or genuine pairs remain separate; visual regression review is pending.

Attempt03 partial repair, not complete rejection of useful coverage
-----------------------------------------------------------------

Parent opened the original conn26-body-z31 raw, point-only and combined
captures at20261005T023942145773Z,023942705612Z and023943315149Z.
All retain the same crop and displayed Z32/native index31. Point-only is a
genuine empty-image canvas. The visible centre lies within the clear raw body;
only one point is visible at this slice, so this triple cannot independently
establish the number of points through that body's full Z extent.

The author's attempt03/RESULT.md records a partial repair: former lower-border
labels6/12/13 become one body, while labels3/4 still divide a continuous oval.
That local union remains author-reviewed evidence, not a parent-inspected
label-volume proof. The candidate has26 centres and useful body support;
remaining false splitting prevents a complete census claim, not retention of
the demonstrated marker-connectivity improvement. The author continues
independent development without dataset-specific parameter coaching.
