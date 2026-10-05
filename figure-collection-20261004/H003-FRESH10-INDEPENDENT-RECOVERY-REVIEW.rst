H003 fresh10: recovery and claim-specific admission
=================================================

Scope
-----

Independent postfreeze review of H003_FRESH10_COVERAGE_89, a task-only author
working on the released paired 400 x 400 DNA/actin field A02/site1/Z1/time1.
No scientific rerun, reference scoring, parameter feedback or image retouching
was performed for this review. This is a separate author from Figure 6 and
the preceding fresh09 account, not a continuation of either analysis.

The author measured nuclear texture, a genuine neighbouring pair and actin
support before its first scientific method. Its first complete output followed
technical configuration and routing repairs and contained 57 nuclear and
associated-region labels. Intensity-marker revisions corrected sampled texture
splits but merged a bright/dim neighbour. Shape markers restored that neighbour;
reducing marker suppression then recovered dense-region objects that had been
lost when oversized merged basins were filtered. Final C06 contains 55 nuclear
instances, 55 seeded actin regions, 53 retained regions and two withheld regions.
This is useful within-run recovery, not a first-attempt accuracy percentage.

Personally inspected native evidence
-----------------------------------

Original PNGs were opened, rather than relying on the report or a contact sheet.
The final-QA index binds each screenshot to its original typed MCP receipt,
numeric raw window, visible producer route, camera and native dimensions.
The 953 x 464 canvas uses Y/X axes, site/Z/time indices zero and gamma one.
The full-field camera is (0,199.5,199.5), zoom1.092; the bright/dim pair camera
is (0,158,260), zoom4. Coordinates are native pixels, not physical distances.

Personally reviewed nine final captures under the canonical HDD qa/final_C06:

* full/DNA_raw_0_100, 20261005T124839320606Z;
* full/Actin_raw_0_80, 20261005T124845716192Z;
* full/Nuclei_result, 20261005T124852917523Z;
* full/DNAOutlineQA, 20261005T124919221681Z;
* full/ActinOutlineQA, 20261005T124925583551Z;
* top_pair/DNA_raw_0_100, 20261005T130003428231Z;
* top_pair/Actin_raw_0_80, 20261005T130010334260Z;
* top_pair/DNAOutlineQA, 20261005T125441208216Z;
* top_pair/Nuclei, 20261005T125932699102Z.

All filenames end _napari_6023_OpenHCS_Napari_Visualization.png. The linked
native-source proof retains their complete paths and original SHA256 identities.
The outline images contain the frozen gray analytical background with yellow
nuclear and cyan actin contours; they are not a raw-only display at the same
numeric upper limit. Raw-only windows remain complementary support witnesses,
not photometrically identical images. Result-only turbo colours are similar
for some adjacent IDs, so colour alone cannot establish a merge.

The bright and dim neighbours both have supported raw DNA signal and separate
final outlines. Integer masks, not hue differences, determine separation.
Ordinary nuclei and the dense group retain plausible nuclear localisation.
The cyan actin territories have useful support but crowded interfaces and
extension into weak signal remain uncertain. The elongated lower nuclear
support also remains an identity ambiguity. These limitations concern boundary
extent and selected identities; they do not negate all nuclear recovery.

Admission, provenance and units
------------------------------

Two weak associated regions were withheld using measured actin mean, not
deleted from the nuclear census. Their raw-codebook means are 3.6904 and
6.8758; one associated region equals its 281-pixel nuclear seed, while the
other grows from 355 to 459 pixels. The next supported mean was approximately
15.93 in the preceding measured candidate. This is local evidence for selective
admission, not a validated general cell classifier.

CellProfiler intensities use the uint8 codebook divided by255; the observed
actin maximum203 is not the normalization denominator. Final cell IDs are
renumbered: join Cells.Parent_SeededCells to SeededCells.object_label and then
SeededCells.Parent_Nuclei to Nuclei.object_label. Do not equate cell/nucleus IDs
directly. Eleven nuclei and sixteen admitted regions touch the image border.
Their areas are truncated observations. No manual census or exhaustive mask
accuracy, physical calibration or held-out performance was established.

The final complete PipelineDocument SHA256 is
d5d97e3253328718516191dd0f44ffc5a75c7de18122a7abc78058f8a31519ed.
The author retained all failed candidates and diagnostics, rather than replacing
them with the final method. The original client exit2 is preserved separately
from successful final numerical execution and acknowledged native/viewer exits.

Evidence roots
--------------

Control: /home/ts/wt/openhcs-issue-batch-20260929/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/H003_FRESH10_COVERAGE_89/author-workspace/output.

Canonical payloads: /run/media/ts/hdd/openhcs-science/next-h00488-h00389-bbbc03996-fresh10-after-capacity-20261005/H003_FRESH10_COVERAGE_89.

The accompanying paper/supplementary/task_only_analysis/h003-fresh10-source-proof.json
records current independent hash and integer-label checks plus the inspected
capture identities. These local paths identify retained originals, not a
self-contained image archive or an additional scientific execution.
