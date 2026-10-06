Fresh paired-channel analysis: development checkpoint
====================================================

Status: the independent H003_FRESH23_89 author is still completing its own
review and final custody. This record is a parent verification checkpoint,
not a final scientific freeze or a new autonomous accuracy score. No reference
answers were opened for these checks, and no parent scientific steering was
sent to the author.

Run and candidate
-----------------

The author uses the receiving23 package on isolated display89 through MCP.
The paired A02 acquisition contains DNA and Actin images of400x400 pixels.
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
These identify the proposal, not a post-writer seal of all final artifacts.

Self-directed repair
--------------------

FIRST retained52 nuclei and52 seeded cell regions. The author's distributed
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
boundary validation or reference agreement. The author's remaining pair,
textured-single and Actin-region checks are not replaced by this parent review.

Independent saved-output check
------------------------------

The parent read the existing TIFF label arrays and exported CSVs without
changing the masks, pipeline or tables. Both arrays have shape400x400,
with55 nonzero IDs each and identical ID sets. Every nuclear pixel lies
inside the cell-region mask with the same ID. Every exported object area
in Nuclei.csv and Cells.csv matches its saved array pixel count. Both tables
contain55 rows. The minimum per-ID cell-region growth area is zero;
IDs4 and11 have no growth beyond their nuclear seeds.

Saved label files under input_candidate03/results::

  A02_channel-1_z_index-1_timepoint-1_Nuclei_step0.labels.tif
  A02_channel-2_z_index-1_timepoint-1_Cells_step1.labels.tif

Their independently calculated SHA256 values are, respectively::

  b3e06aa2614ccaaed3ffccc7e88cac30c05ee7b68fed75440d5e4939ebb0822e
  87726d1e391553de4434f702f57293e7d687ca66a71fcb2fa1944fdcf28d1217

This proves consistency of these saved algorithm artifacts, not55 biological
cells. Seed-only regions, ambiguous adjacent nuclear lobes and censored image
borders retain separate review flags. No fluorescence acceptance is inferred
from area or ID agreement.

Remaining completion
--------------------

The author must finish its own scientific decision and final artifact manifest.
The parent will then verify that manifest and exact runtime disposition before
promoting this checkpoint into a final supplementary record. No held-out or
manual-reference accuracy, exhaustive whole-cell envelope agreement, or final
native/viewer closure is claimed here.
