Fresh paired-channel analysis: qualified scientific completion
=============================================================

Status: the independent H003_FRESH23_89 author froze its scientific decision
and artifacts on 6 October 2026 at 02:25:56 UTC. It accepted useful DNA-defined
instances and nucleus-seeded actin regions, not an exact biological census or
complete-cell morphology. No reference answers were opened for these checks,
and no parent scientific steering was sent to the author. Runtime retirement
is a separate operational handoff. The parent's later reference comparison
below is separate from the author's blinded decision.

Run and candidate
-----------------

The author uses the receiving23 package on isolated display :89 through MCP.
The paired A02 acquisition contains DNA and Actin images of 400 x 400 pixels.
Physical calibration is unverified; geometry is reported in native pixels.
The author retained FIRST and rejected CANDIDATE02 rather than overwriting
their scientific source, outputs, matched captures or decisions.

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h003-fresh23-89-after-h00222-20261006/H003_FRESH23_89/author-workspace/output

Scientific root::

  /run/media/ts/hdd/openhcs-science/next-h003-fresh23-89-after-h00222-20261006/H003_FRESH23_89

The CANDIDATE03 proposal checksum records pipeline.py as
``879a1589ea1935a2a55505686215d02a87871369dd2bf8fb67af8285b0a59463``
and rationale.rst as
``cb8f2c7a8b08b749b3a6ccbf86733c5cf0ab308d49a18b61bbb809081b6713fa``.
These identify the proposal. FINAL-ATTEMPT.json separately identifies the
reviewed candidate, final technical audit and frozen control files.

Self-directed repair
--------------------

FIRST retained 52 nuclei and 52 seeded cell regions. The author's distributed
review found three supported nuclear bodies joined through threshold-admitted
signal. Shape markers supplied one centre, and size filtering removed the
merged object. CANDIDATE02 changed marker extraction to smoothed intensity;
the three distinct markers still produced a merged object with shape dividing
lines, and a genuine pair also merged. The author rejected that candidate.
CANDIDATE03 changed the dividing method to intensity while retaining the
candidate02 foreground, size admission and marker settings.

The parent personally opened the candidate03 missing-group raw-only,
result-only and combined DNA captures, the FIRST combined capture at that
region, and candidate03 dense-region raw and combined captures. The three
previously uncovered bodies are now represented separately in the inspected
region. Ordinary nearby nuclei remain represented. Bridge-influenced mask
extent remains a separate uncertainty; local recovery is not whole-field
boundary validation or reference agreement. This parent review does not replace
the author's own matched-channel controls.

The author personally opened all 108 final captures: nine positions, both
physical channels, two numeric contrast windows and raw/result/combined views.
The genuine pair was separate in the final candidate; a textured/lobed nucleus
remained single and its dim neighbour remained separate. Actin contact
interfaces and the bridge-influenced extent of one recovered object remained
uncertain. IDs 2 and 3 occupied a continuous-looking actin envelope, leaving
lobed-single, adjacent-nuclei and multinucleate interpretations unresolved.
The author retained these flags rather than further tuning to force a census.

Independent saved-output check
------------------------------

The parent read the existing TIFF label arrays and exported CSVs without
changing the masks, pipeline or tables. Both arrays have shape 400 x 400,
with 55 nonzero IDs each and identical ID sets. Every nuclear pixel lies
inside the cell-region mask with the same ID. Every exported object area
in Nuclei.csv and Cells.csv matches its saved array pixel count. Both tables
contain 55 rows. The minimum per-ID cell-region growth area is zero;
IDs 4 and 11 have no growth beyond their nuclear seeds.

Saved label files under input_candidate03/results::

  A02_channel-1_z_index-1_timepoint-1_Nuclei_step0.labels.tif
  A02_channel-2_z_index-1_timepoint-1_Cells_step1.labels.tif

Their independently calculated SHA256 values are, respectively::

  b3e06aa2614ccaaed3ffccc7e88cac30c05ee7b68fed75440d5e4939ebb0822e
  87726d1e391553de4434f702f57293e7d687ca66a71fcb2fa1944fdcf28d1217

This proves consistency of these saved algorithm artifacts, not 55 biological
cells. Seed-only regions, ambiguous adjacent nuclear lobes and censored image
borders retain separate review flags. No fluorescence acceptance is inferred
from area or ID agreement.

Frozen artifacts and technical audit
------------------------------------

The parent independently checked every declared byte count and SHA256 in
FINAL-ATTEMPT.json (51 control files, 7,908,603 bytes), the candidate03 payload
manifest (131 files, 19,582,579 bytes) and the AUDIT01 payload manifest
(22 files, 5,531,172 bytes). All matched. These are separate manifest scopes,
not an estimate of exclusive storage or a seal of the still-active journal.

AUDIT01 registered a typed label-integrity function on the original process.
It checked integer/nonnegative labels, aligned shapes, dense matching ID sets
and full same-ID nucleus-to-cell containment before export. No scientific
parameters or masks changed. Original execution
``d7c81e63-e109-42cc-a82c-609a61e2171a`` completed with no execution error.
The parent independently recalculated both sides of all seven retained parity
pairs: two converted label images, two runtime label TIFFs, Nuclei.csv,
Cells.csv and Image.csv. Every pair was byte-identical to the reviewed candidate.

The final decision and review_flags.csv retain seed-only regions, ambiguous
identity and censored borders. These records support self-directed detection
repair and internally consistent exports on one development field. They do
not establish held-out accuracy or exhaustive whole-cell
envelope agreement. Final native/viewer retirement and terminal journal seals
are not claimed by this scientific record.

Postfreeze reference comparison
-------------------------------

After scientific freeze, the parent applied the existing merged BBBC007 manual
outline decoder and scorer, unchanged from commit
``e99736388140e7ed910b413222a53501ec7d4a0d``. Both staged raw channels were
independently compared pixel-for-pixel to component 0 of the corresponding
official TIFFs. All four scored label hashes matched the original manifests.
The separate h003-fresh23-postfreeze-reference-comparison.json retains exact
paths, source hashes, policies and measurements. No score or reference was
provided to an analysis author or included in the skill.

One-to-one matching uses IoU at least 0.5 against 47 nuclear and 54 actin closed
reference interiors. Frame-connected regions and strokes are excluded; tiny
interiors remain included. Clipped predictions are not filtered to mirror those
reference exclusions. These are annotated-interior comparisons, not a certified
exhaustive biological census.

======== ======= ======== ======= ========== ====== ==================
Stage    Channel Predicted Matches Reference  F1     Relevant boundary
======== ======= ======== ======= ========== ====== ==================
FIRST    DNA     52       37      47         0.747  0.739
FINAL    DNA     55       38      47         0.745  0.521
FIRST    ACTIN   52       34      54         0.642  0.703
FINAL    ACTIN   55       36      54         0.661  0.700
======== ======= ======== ======= ========== ====== ==================

The last column is the fraction of non-background/frame-adjacent predicted
boundaries within two pixels of any original manual stroke. Symmetric
whole-boundary F1 is a different endpoint: DNA 0.810 to 0.818 and actin
0.663 to 0.668. Nuclear reference recall rose from 0.787 to 0.809 while
precision fell from 0.712 to 0.691. Thus visible local detection recovery
coexists with essentially unchanged nuclear object F1 and worse directed
contact-boundary agreement. Actin-region object agreement improved modestly.
This trial does not demonstrate a whole-field nuclear accuracy gain or an
isolated effect of the skill. Unmatched predictions/reference regions express
disagreement under this policy, not automatically false biological cells.
