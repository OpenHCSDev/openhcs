H004 fresh10: junction support repair and remaining gaps
======================================================

Scope
-----

Independent post-freeze review of H004_FRESH10_89. No new scientific execution,
reference comparison, image editing or feedback to an active analysis author.
Control root: /home/ts/wt/openhcs-issue-batch-20260929/next-h004-fresh10-89-20261005/H004_FRESH10_89/author-workspace/output.
Canonical payload root: /run/media/ts/hdd/openhcs-science/next-h004-fresh10-89-20261005/H004_FRESH10_89.

The original freeze has 6372 entries. Independent review found 6369 complete
size/hash matches and three growing outer journals whose declared original
byte prefixes still matched. Do not describe those three complete journals
as immutable. The original manifest is unchanged. Selected science artifacts
and screenshots below pass their complete hashes; the journal limitation does
not change their bytes. Original exact native/viewer closure receipts are
retained separately from the CLI's accumulated exit code 2.

Native sources
--------------

Four original PNGs, personally opened, are copied byte-identically under
paper/figures/slas/h004_junction_sources. Paths below are relative to the
canonical payload root:

* raw.png: qa/BIO04_central_crossing_raw/20261005T041213983021Z_napari_6023_OpenHCS_Napari_Visualization.png;
  SHA256 735e7f1d8a37f51e8a61304ddffa7dc60706ab2615dee8243350ff4bc650b5e6.
* before.png: qa/BIO04_central_crossing_result/20261005T041222930700Z_napari_6023_OpenHCS_Napari_Visualization.png;
  SHA256 4c4c44002486bb7cb32cc017fa56ee738cb32fba02eca68baa6a84bab3969214.
* final.png: qa/BIO06_central_native_result/20261005T042407584470Z_napari_6023_OpenHCS_Napari_Visualization.png;
  SHA256 becb75bdcf6775ff5b71720dd30e2e28c95b11a5475f9268f9f1e2626102da83.
* combined.png: qa/BIO06_central_native_combined/20261005T042419252776Z_napari_6023_OpenHCS_Napari_Visualization.png;
  SHA256 e4a9b45d4eb0cf247dc3d0ed165261398ce58bd96a55bd7ac9e6588fd05a3e75.

The BIO06 raw screenshot at qa/BIO06_central_native_raw/20261005T042356227019Z_napari_6023_OpenHCS_Napari_Visualization.png
has the identical hash to raw.png. State/snapshot receipt pairs 284/285,
287/288, 335/336 and 338/339 are copied unchanged alongside the two pipeline
documents and final metrics under paper/supplementary/task_only_analysis/h004-fresh10.
Snapshots report render_complete, 1440 x 944 widgets, 953 x 442 canvases,
Y/X displayed axes and camera angles (0,0,90). The author recorded centre
y365,x370, zoom3 and raw contrast 0-80, gamma1. Native dimension point
(0,0,0,0,0,399,399) is the slice state, not this camera centre. Source channel1
is the morphology-inferred Process role; stain and neuronal identity remain
unknown. No physical calibration is supplied.

FigureSheet records the same editorial XYXY crop (297,28,1250,430) for all
four screenshots. Original files remain intact, with no retouching or
recolouring. The crop omits the native footer and keeps the visible repair
and prematurely terminating upper branches.

Independent numerical check
---------------------------

Read only the original uint8 staged_input/field_w1.tif and original materialized
800 x 800 TIFFs, with the installed tifffile/NumPy stack, without reconstruction
or rerunning the pipeline:

* BIO04/staged_input_openhcs/qa_CandidateProcesses/A01_s001_w1_z001_t001_CandidateProcesses.tif.
* BIO06/staged_input_openhcs/qa_OutsideSomata/A01_s001_w1_z001_t001_OutsideSomata.tif.

On the exact junction tile y325:355,x325:365, raw>=20 contains 291 pixels.
Nineteen are outside the earlier nonzero support; zero are outside the final
support. The exact quiet tile y100:131,x650:681 contains zero support pixels
in both attempts. These recomputed values match the author's record.
They are selected raw-support checks, not ground-truth recall or a statement
that every faint track is recovered. Final metrics are original copied data,
not a second recomputed scientific authority.

Interpretation
--------------

The bright central junction is visibly connected in the final candidate.
BIO06 adds strong raw support to BIO04's enhanced sensitivity. BIO05 separately
added soma exclusion before medial axis; therefore the before/final figure
does not isolate the union as the cause of interior-loop removal. Full
pipeline documents preserve both changes. Final raw/skeleton views retain
weak incoming and short side branches that stop early. Quiet-tile agreement
does not exclude puncta, halos or all background nuisances elsewhere.

Eight prominent nucleus-associated soma labels have useful provisional
geometry. They are not a validated neuron census. Candidate support and
skeleton counts are descriptive algorithm outputs. Anatomical branch counts,
per-neuron lengths and crossing ownership remain unaccepted. No manual ground
truth, touching-pair validation or held-out analysis was performed here.

This example supports a reusable diagnosis: inspect raw, enhanced response
and candidate mask separately when ridge enhancement loses junction pixels;
test support recovery with nuisance and faint-path controls. It does not
provide dataset-specific settings for future fresh authors.
