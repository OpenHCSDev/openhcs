H002: retained-result presentation review
========================================

This checkpoint prepares main Figure 9 to consume explicitly identified native
captures, crops and headings from its existing source card. The existing
``h002_measurement_first`` and ``FigureSheet`` remain the layout and saving
owners. The postfreeze matching panel and evaluation are unchanged. PR1018's
single H002 supplementary composite is not modified or duplicated.

Working checkpoint
------------------

The XY panel now shows the saved same-run nuclear ROI polygons over raw signal,
at zero-based Z34 (source Z35). Their native categorical fills and edges make
the admitted nuclear extents legible; no enlarged-marker or edge-only style is
claimed. The XZ and YZ panels retain the original native centre captures.
The original source card is
retained as ``h002_firstmethod_sources/original-source-receipt.json`` and all
three original PNGs remain unchanged. The updated source card explicitly names
each local asset, its original capture hash, native crop and truthful heading;
the renderer checks capture bytes and crop geometry before placing it.

Raw, feature-bearing Points, the 26-row table and same-run nuclear Labels were
independently rehashed against the frozen original inventory. Paths and hashes
are in ``source-receipt.json`` under ``frozen_scientific_inputs``. Source is
scalar ZYX60x256x256, channel1, with unverified physical calibration. Labels
represent nuclear bodies, not verified whole-cell borders. The scientific
method, saved arrays and fractional point coordinates are unchanged.

Native capture acceptance
-------------------------

One recorded MCP client on the corrected fresh15 review lane reopened all 60
raw source planes, the saved 26-centre ROI ZIP, and the saved per-slice polygon
ZIP ``image.ome.tif_s001_w1_z035_t001_h002_labels_step0_rois.roi.zip``.
The latter is a saved label projection, not a new segmentation or fabricated
contour. Its native transform reports Z translation34 and unit XY scale.
The 3-D Labels TIFF was independently rehashed but was not reopened as a native
categorical volume; this checkpoint does not claim orthogonal mask rendering.

Nine native PNGs were personally opened: raw-only, result-only and combined at
XY Z34, XZ Y157 and YZ X80. XY polygons cover visible nuclear support, including
one orange bright/lobed chromatin complex whose biological identity remains
ambiguous. The fixed raw window was [2513,31882.274999999863], gamma1. XY camera
center was [0,127.5,127.5], zoom1.6625, canvas953x448. Raw and result visibility
changes retained the same slice, camera and source domain. Journal and exact
accepted capture identities are in the source card. The new publication PNG
``xy-review28.png`` is distinct from every historical image.

The new XZ/YZ controls correctly use actual native spatial axes with planar
Shapes hidden. Their result-only views are effectively blank because Points
are tiny and slice-restricted; combined views do not demonstrate readable mask
overlays or improved centre visibility. These controls remain on disk but are
not publication panels. The original same-run XZ/YZ centre panels are retained,
not relabelled as outlines. No compatible MCP Points/Shapes style setter was
exposed in the current105-tool surface. This gap does not hold the useful XY
checkpoint behind an engineering detour.

Caption scope: XY shows retained nuclear ROI extents over raw; XZ/YZ show the
original retained centres. This is presentation of one frozen scientific
method, not a new analysis. Out-of-plane Points remain hidden. Localisation
agreement does not establish boundary accuracy, complete instance separation,
or an exhaustive biological census. Nuclear masks are not cellular boundaries.

Reproduce the current panel with the existing matplotlib-capable interpreter:
``PYTHONPATH=paper/figures python -c 'from build_slas_visual_story import h002_measurement_first; h002_measurement_first()'``.
Only this dependent figure is regenerated; no other figure generator is run.
