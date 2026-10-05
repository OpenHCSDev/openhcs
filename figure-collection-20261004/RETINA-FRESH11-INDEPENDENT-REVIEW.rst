Retina fresh11: supported repair, retained faint loss
===================================================

Source and verification
-----------------------

Independent post-freeze review of R0010_FRESH11_REV02_88. Control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-r0010-fresh11-88-20261005/revision02/R0010_FRESH11_REV02_88/author-workspace/output.
Canonical payload root:
/run/media/ts/hdd/openhcs-science/next-r0010-fresh11-88-20261005/revision02/R0010_FRESH11_REV02_88.

All 10 handoff entries, all 1147 payload entries and all 83 opened-capture
entries passed independent full byte-size/SHA256 checks. These sets overlap;
do not sum them as distinct files. The original manifests remain unchanged.
The handoff does not seal the harness's outer author history. Both exact
owned-process exits are recorded; client exit 2 remains a separate accumulated
CLI-error observation, not a failed scientific execution.

Input R0010.czi has SHA256
3609adc418bb772307804aac1fbecc40d7da54b16cd2a5e3ab8aedbb4d83a851.
This is the reused development field, not an unseen held-out image. Native
metadata identifies AF647/RBPMS, AF488 (unknown target) and Hoechst; the final
detector uses RBPMS. Physical channel identity is not inferred from a screenshot
colour. The complete final submitted pipeline has SHA256
2c4d959c64e583364ba68a0a59334e0185607b49242aaa16239205183acb09b1.

Counts and scope
----------------

Independent direct read of the original durable A07 Somata_step2.labels.tif
found a 2586 x 2586 int32 image, 73 positive label IDs and 439694 foreground
pixels. The original Somata.csv has 73 rows. This confirms the count and
label occupancy, not biological accuracy. The exported UINT16 SomaLabels image
is a separate presentation/output product; do not confuse its dtype with the
durable label artifact. ROI contour-member count is not object count.

The author measured distributed body/background and neighbour support before
the first proposal, then inspected actual corrected response values. A07 uses
Gaussian smoothing and top-hat correction before manual foreground admission
and intensity-based declumping. It excludes border-touching objects and objects
outside its configured 50-180 pixel equivalent-diameter range. A lower count
than an earlier 102-instance candidate is not proof of improvement or regression:
selection, processing and instance partitions differ. No reference mask or
independent manual count was released for this trial.

Personally inspected native witnesses
-------------------------------------

Original PNGs were opened without retouching, source reconstruction or new
scientific execution. Paths are relative to the canonical payload root:

* A06 center raw and combined: screenshots/A06-center-raw/20261005T044604245656Z_napari_6021_OpenHCS_Napari_Visualization.png
  and screenshots/A06-center-combined/20261005T044626826453Z_napari_6021_OpenHCS_Napari_Visualization.png.
* A07 center raw, labels and combined: screenshots/A07-center-raw/20261005T044843127199Z_napari_6021_OpenHCS_Napari_Visualization.png,
  screenshots/A07-center-labels/20261005T044858593142Z_napari_6021_OpenHCS_Napari_Visualization.png,
  screenshots/A07-center-combined/20261005T044913360825Z_napari_6021_OpenHCS_Napari_Visualization.png.
* A07 northwest raw, labels and combined: screenshots/A07-nw-raw/20261005T044937191851Z_napari_6021_OpenHCS_Napari_Visualization.png,
  screenshots/A07-nw-labels/20261005T044952771018Z_napari_6021_OpenHCS_Napari_Visualization.png,
  screenshots/A07-nw-combined/20261005T045006296359Z_napari_6021_OpenHCS_Napari_Visualization.png.
* A07 northeast raw and combined: screenshots/A07-ne-raw/20261005T045032614613Z_napari_6021_OpenHCS_Napari_Visualization.png
  and screenshots/A07-ne-combined/20261005T045059192456Z_napari_6021_OpenHCS_Napari_Visualization.png.
* A07 southwest faint raw, labels and combined: screenshots/A07-sw-faint-raw/20261005T045132908650Z_napari_6021_OpenHCS_Napari_Visualization.png,
  screenshots/A07-sw-faint-labels/20261005T045146605043Z_napari_6021_OpenHCS_Napari_Visualization.png,
  screenshots/A07-sw-faint-combined/20261005T045200929267Z_napari_6021_OpenHCS_Napari_Visualization.png.
* A07 whole-field raw and combined: screenshots/A07-overview-raw/20261005T045348894776Z_napari_6021_OpenHCS_Napari_Visualization.png
  and screenshots/A07-overview-combined/20261005T045425439292Z_napari_6021_OpenHCS_Napari_Visualization.png.

The original capture-provenance records retain full preceding native state.
The center views share camera centre (0,160,160), zoom8, raw window0-63,
gamma1 and 953 x 442 canvases. Northwest centre is (0,85,105), northeast
(0,70,270), southwest (0,265,95), all zoom8. Southwest raw window is0-42;
whole-field centre (0,160,160), zoom1.3 uses0-63. These camera centres use
native world coordinates with XY scale0.12353054911059548, not source-pixel
indices; source spacing is declared metadata, not independent calibration.
Result-only images use their integer label display range, not raw fluorescence
units. Combined views use the named original raw route and A07 shapes.

Quality judgement
-----------------

At the center, A06 cuts one continuous bright body into two labels; A07
represents it once. Nearby supported structures remain separately represented.
Northwest bright-body detections are useful and neighbouring raw-supported
bodies retain separate labels. The northeast C-shaped support still has
uncertain boundary/identity details. In the southwest faint window, a visible
weak structure remains unlabelled, consistent with the author's recorded
possible miss; a clear neighbouring bright pair is represented separately.
No independent annotation establishes that every weak feature is a target soma.

These views support useful local body detection and autonomous repair, not
a complete census or validated boundary accuracy. The author's population-level
abstention must not erase the positive local findings. Conversely, 73 consistent
table/label identities do not establish complete detection. Preserve the
successful repair and explicit faint/complex failures for the paper and later
development; do not use 73 or 102 as a target for blind tuning.

Skill audit and next learning decision
-------------------------------------

The current measurement-interpretation guide already distinguishes raw diameter,
actual consumed marker landscapes, within-body texture, genuine neighbours and
two-dimensional maxima from line profiles. Its processing-units section already
requires actual alias dtype/range rather than nominal API return types. The
preprocessing and viewer guides already require distributed faint/noise controls.
No duplicate rule or dataset-specific retinal setting was added by this review.

The author measured actual intensity seed separation after a split appeared,
rather than treating an earlier shape-profile lobe estimate as the same evidence.
This is a useful diagnostic performed late, not a new universal landscape rule.
Future frozen-skill evaluation should inspect whether that existing lesson
affects first-proposal reasoning, then judge the resulting outputs. Do not send
these parameters, masks or outcomes to an active blind author. Assisted repairs
remain a distinct development phase; a later unguided author tests transfer.
