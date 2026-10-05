BBBC007 rotation: complete exports, incomplete foreground recovery
================================================================

Source and independent checks
-----------------------------

The frozen independent author is BBBC007_FRESH10_ROTATION_89. Control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-h00296-bbbc00789-fresh10-20261005/BBBC007_FRESH10_ROTATION_89/author-workspace/output.
Canonical payload root:
/run/media/ts/hdd/openhcs-science/next-h00296-bbbc00789-fresh10-20261005/BBBC007_FRESH10_ROTATION_89.

All 1467 remaining payload files passed independent size/SHA256 checks,
totalling 399414459 file bytes. All 17 frozen source entries also passed;
frozen_pipeline.py is byte-identical to candidate03.py, SHA256
f7250bd459cdb9cb915dbe3e046c93c44bc18fa4c67a5f4204c5e0133c43c2bd.
The absolute-path source_bindings.py dependency remains at its original path.
These checks do not seal the outer harness journal. The original transient
scratch-file disappearance remains separately documented by the author.

Direct reads of the four durable per-well int32 nucleus/cell label stacks
covered 16 source planes. Each plane had matching positive nucleus/cell IDs
and zero nucleus pixels outside its corresponding cell. Site-local pair counts
were A01: 95/154/143/94; A02: 60; A03: 27/83/108/50/79; and
A04: 98/49/78/62/61/70, totalling 1311. IDs repeat between sites: counting
unique IDs across a whole multi-site stack would undercount these outputs.
This is an algorithmic population, not a biological census or accuracy score.
Native geometry-table agreement is recorded in the original author's audit;
this independent review did not recompute every geometry measurement.

Personally opened native evidence
---------------------------------

Six unmodified A02 site-1 PNGs were opened. Paths below are relative to the
canonical payload root:

* Earlier DNA raw: qa/pre-first/A02_1/DNA_p0_99/20261005T050646184301Z_napari_6023_OpenHCS_Napari_Visualization.png.
* Final DNA combined: qa/final-attempt/A02_1/DNA/combined-p0_99/20261005T055700696763Z_napari_6023_OpenHCS_Napari_Visualization.png.
* Final DNA result-only: qa/final-attempt/A02_1/DNA/result-only/20261005T055713302618Z_napari_6023_OpenHCS_Napari_Visualization.png.
* Earlier actin raw: qa/pre-first/A02_1/ACTIN_p0_99/20261005T050701617730Z_napari_6023_OpenHCS_Napari_Visualization.png.
* Final actin combined: qa/final-attempt/A02_1/ACTIN/combined-p0_99/20261005T055727832899Z_napari_6023_OpenHCS_Napari_Visualization.png.
* Final actin result-only: qa/final-attempt/A02_1/ACTIN/result-only/20261005T055740254809Z_napari_6023_OpenHCS_Napari_Visualization.png.

These are not exact same-canvas final triads. Earlier raw camera centre was
(0,256,256), zoom0.72, canvas962x442; final combined camera centre was
(0,256,256), zoom0.7, canvas953x398. Manual ROI loading changed the stacked
axes. The original qa-index.json records route-local source identity, channel
selection and p0-99 presentation requests; this review does not independently
authenticate every resolved numeric window from those requests. No captures
were recropped, remapped or reconstructed. Neither whole-field thumbnails nor
filled overlays establish precise cell boundaries.

Quality and next action
-----------------------

Ordinary labelled nuclear cores have useful raw support. Final DNA combined
views also retain uncovered dim groups and parts of a conspicuous bright
cluster. Cell masks are absent at corresponding unseeded regions; other
regions show growth beyond nuclear cores. This supports useful local detection
alongside material coverage defects, not rejection of every individual label.
Foreground admission, marker formation and later size filtering still need
discrimination through the persisted intermediate stages. The visual symptom
alone does not establish which stage caused each missing object.

Candidate03 completed all 16 source sets, but final A04 QA was absent and
A03 actin QA ran after the recorded 75-minute deadline. Those later captures
remain preserved and excluded from the original timed outcome. Earlier
candidate02 four-well QA cannot substitute for candidate03 review. No manual
references, held-out images or evaluator answers were opened for this review.

The original failed freeze remains immutable. Development continuation has
been assigned to the existing fleet owner, using the original author's context
and a separately recorded development phase when measured resources permit.
Its purpose is to finish distributed final QA, identify the earliest lost
support stage, repair it and retain positive/regression controls. This is an
assignment, not a claim that continuation is already running or repaired.
Any external correction remains an intervention, not a fresh autonomous pass.
No new skill recipe is promoted from an untested repair hypothesis.
