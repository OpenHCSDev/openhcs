H002 fresh15: independent centre review
=======================================

Reviewed 2026-10-05 from unchanged, closed original captures. The fresh author
used the task brief, packaged skill and MCP; no reference answer or corrective
scientific parameters were returned to it. One scientific method produced
26 fractional Z/Y/X candidate centres. A second technical execution changed
persistence/live streaming, not the detector. The original failed execution
and nonzero client exit remain recorded.

Control root:
``/home/ts/wt/openhcs-issue-batch-20260929/next-h002-fresh15-89-after-retina-20261005/H002_FRESH15_89/author-workspace/output``.
Payload root:
``/run/media/ts/hdd/openhcs-science/next-h002-fresh15-89-after-retina-20261005/H002_FRESH15_89``.
Read ``FIRST-METHOD.rst``, ``HANDOFF.rst``, ``QA-DECISION.rst`` and the
separate owner terminal custody. Detector parameters were tied before execution
to distributed body dimensions, intensity/background profiles and shape-marker
reasoning; this is demonstrated measurement-first authorship, not a default
justified after inspecting its labels. No new acquisition/reference was opened.

Personally inspected twelve original raw/Points/combined PNGs under ``qa``:

* ``v1-z34-raw-full``, ``v1-z34-points-corrected``,
  ``v1-z34-combined-corrected``: timestamps 174012352859,
  174038123818, 174038325557.
* ``full-xz157-raw``, ``full-xz157-points``, ``full-xz157-combined``:
  timestamps 175103269646, 175103607842, 175103967317.
* ``full-yz54-raw``, ``full-yz54-points``, ``full-yz54-combined``:
  timestamps 175104661336, 175104906472, 175105114647.
* ``full-yz80-raw``, ``full-yz80-points``, ``full-yz80-combined``:
  timestamps 175105718270, 175105946741, 175106194866.

All filenames use prefix ``20261005T`` and suffix
``Z_napari_6023_OpenHCS_Napari_Visualization.png``. Framing agrees visually
within each triplet. Z34 raw full-window readback is 711--58564, gamma1;
the lower-upper-limit alternative is 711--17498. Numeric contrast readback
for every orthogonal capture was not independently reconstructed in this review.

Positive findings: visible XY centres lie within ordinary bodies. The XZ Y157
triplet locates one centre inside an ordinary nuclear body, and YZ X80 likewise
places a centre in the left ordinary body. No duplicate centre is visible inside
those inspected bodies. These are real scoped successes, not evidence for all
26 identities or complete segmentation boundaries.

The YZ X54 bright chromatin complex has one candidate centre. Its lobed raw
support alone does not distinguish one mitotic/lobed nucleus from two identities.
Retain this uncertainty rather than demanding an unsupported split. Other raw
bodies on these planes without a visible point cannot be called misses from
one plane: Points have fractional 3-D coordinates and out-of-slice display is
disabled. The earlier incorrectly named label-only capture is not used as
Points evidence. No whole-volume ground-truth count is available.

Decision: useful autonomous candidate-centre localisation with biological limits,
not a rejected run solely because of the lobed complex. Broader exhaustive
counting accuracy and mask boundary quality are unmeasured. Retain 26 as the
algorithmic candidate count, not an exact biological census. No physical
calibration, held-out generalisation or per-cell fluorescence claim follows.
The owner verifies final job4 completion, exact native/viewer closure and
26-row reconciliation; those technical findings are separate from this visual
review. Original pipeline/custom callable and manifests remain authoritative.
