Fresh paired-channel analysis: qualified scientific completion
=============================================================

Status: the independent H003_FRESH23_89 author froze its scientific decision
and artifacts on 6 October 2026 at 02:25:56 UTC. It accepted useful DNA-defined
instances and nucleus-seeded actin regions, not an exact biological census or
complete-cell morphology. No reference answers were opened for these checks,
and no parent scientific steering was sent to the author. Runtime retirement
is a separate operational handoff, not a new autonomous accuracy score.

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
not establish held-out/manual-reference accuracy or exhaustive whole-cell
envelope agreement. Final native/viewer retirement and terminal journal seals
are not claimed by this scientific record.
