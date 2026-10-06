Retinal fresh15: useful localisation with residual ring fragmentation
==================================================================

This independent review concerns the released R0010.czi development plane,
not held-out scoring. The original author received no coordinator scientific
correction. Its final report retains126 algorithmic regions and rejects
quantitative whole-soma masks; neither that count nor the rejection is a
manual-reference accuracy score.

Original control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-retina-fresh15-89-after-h002-20261005/R0010_FRESH15_89/author-workspace/output

Original HDD root::

  /run/media/ts/hdd/openhcs-science/next-retina-fresh15-89-after-h002-20261005/R0010_FRESH15_89

The coordinator read REPORT.rst and frozen-manifest.json and independently
checked all223 payload and475 author-control whole-file SHA256 hashes on
2026-10-05: no mismatch. This excludes the three growing outer-journal prefixes
from a whole-file seal claim. The complete final PipelineDocument SHA256 is
``a7c72e0fbcb291eeddcb15d0ec9c164d7317285095e63aadf4737c6219034d1c``.
The manifest records2,196,558,624 payload bytes across all retained attempts,
not just the final label image. Source planes are2586x2586; metadata declares
XY0.1235305491um/pixel, not an independently verified calibration.

Personally opened original native views
--------------------------------------

The eight bitmaps below remain under HDD qa. Each timestamp has prefix
20261005T and suffix Z_napari_6023_OpenHCS_Napari_Visualization.png:

* final-pair-raw/result/combined:165704934293/165705729052/165706633244.
* final-edge-raw/result/combined:165710714942/165711617376/165712415988.
* final-edge-Hoechst:165932061458; final-edge-AF488:165934017408.

Each RBPMS triplet visually retains the same field structures and canvas.
The report records RBPMS0--55, AF4880--75 and Hoechst0--83, gamma1.
Those numeric windows and camera/transform consistency are author records;
this review does not independently reconstruct every state from the MCP journal.

In the pair view, two bright neighbouring bodies have separate supported
regions. An adjacent broad irregular mask occupies weaker diffuse signal;
its footprint is less convincing than the bright pair's localisation.
At the edge, a bright rounded body has a compact supported region, while a
weaker lower body is represented by complementary blue/pink fragments rather
than one full envelope. Small irregular peripheral masks also remain.
These are concrete extent/partition limitations, not evidence that every
localisation is wrong. No object-by-object whole-field census was performed.

The matched Hoechst view contains many nuclear structures. It does not turn
every nucleus into an RBPMS-positive soma. The AF488 target is unspecified,
so its morphology cannot establish that biological class either. Preserve
useful body-channel localisation separately from uncertain class and extent.

Learning and disposition
------------------------

The author reports a local ring-marker repair while preserving a genuine pair,
but the final edge witness still contains fragmentation elsewhere. A marker
spacing change can repair one ring without recovering disconnected support
in another: inspect foreground connectivity before choosing that next repair.
This distinction is already covered by the canonical segmentation diagnostics;
the present review records its application gap rather than a new universal
threshold or dataset-specific recipe. No findings were sent to a fresh author.

The report's broad biological-mask rejection is retained as its disposition.
Independent review also retains the demonstrated bright-body detections;
uncertain boundaries do not erase those supported findings. This is not a
claim of poorer or better accuracy than another retinal trial without matched
reference scoring. Exact viewer/native closure and client exit2 are recorded
in cleanup-status.json; final outer-writer sealing belongs to the harness.
