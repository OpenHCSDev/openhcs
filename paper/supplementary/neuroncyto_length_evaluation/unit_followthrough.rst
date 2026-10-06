Bounded primary-source unit follow-through
=========================================

6 October 2026. The earlier conclusion and aggregate CSV are unchanged.
No prediction was rerun or retuned, and no numerical accuracy was computed.

Primary material inspected
--------------------------

* Original NeuronCyto II article, publisher HTML and Europe PMC full-text XML:
  https://onlinelibrary.wiley.com/doi/full/10.1002/cyto.a.22872
  and https://www.ebi.ac.uk/europepmc/webservices/rest/PMC5089663/fullTextXML.
  The tracing description follows skeletons from soma-boundary root points
  and measures branches. The results describe manual NeuronJ annotations and
  image-level primary/secondary/tertiary comparisons. No explicit length
  unit for Supplement 8 was established in the retrieved article text.
* Official download page and linked user guide:
  https://sites.google.com/site/neuroncyto/resourcesdownload
  and https://drive.google.com/file/d/1MKrREhl0IHdWs5U_s7EHntZ6lcCRQd8r/view.
  The guide PDF was read through an in-memory text extraction, without a new
  dataset or software installation. Although named UserGuide_NeuronCyto_Ver3_1.pdf,
  its extracted closing text identifies VERSION 1.0, 2015. Its export section
  (printed page 38) describes a CellImageName.txt output; pages 39--40 describe
  the Result Inspector and dendrite measurements. It does not declare an
  export length unit in the extracted text. The initially unresolved embedded
  screenshots were subsequently inspected visually, as recorded below.
* Original Supplement 8 DOCX was requested through the publisher and PMC/
  Europe PMC direct file routes. Publisher and Europe PMC file routes returned
  HTTP 403; PMC returned a browser-challenge HTML response (HTTP 203), not a
  DOCX. Thus there was no fresh supplementary-header verification. The
  previously retained extraction and hashes remain the only local table
  evidence, qualified as described in conclusion.rst.
* The predecessor NeuronCyto article (2009),
  https://doi.org/10.1002/cyto.a.20664, describes a different acquisition with
  0.31 micrometers per pixel. That cannot establish the units or calibration
  used for the 2016 image-1 manual reference. Descriptions of pixel skeletons
  or pixel-valued morphology parameters likewise do not prove export units.

Determination and stop condition
--------------------------------

This bounded search did not establish that the published manual lengths are
pixels. The remaining requirement for a field-total numerical comparison is
an explicit source declaration tying Supplement 8's image-1 manual values to
pixel lengths (or a documented conversion), plus a compatible definition of
the summed soma-excluded neurite population. A verified supplementary header,
original manual measurement export/calibration record, or original export
algorithm with provenance to this reference could establish that fact.

Spatial manual traces are not intrinsically necessary for a compatible
field-total comparison, but remain necessary for spatial coverage/endpoint
assessment and defensible per-cell correspondence. A principal-shaft-only
comparison additionally requires an agreed branch-order/endpoint definition
and a matching prediction measurement, not the current all-rooted-path total.

No first-versus-final error score is reported while reference units remain
unresolved. The first illustrated candidate must not be selected as the final
candidate or chosen by closeness to the reference. No sorted or ordinal
per-cell matching is permitted by the retained evidence. The search stops
here; no installer, full supplementary movie archive or microscopy dataset
was acquired.

Visual closure of guide screenshots, 6 October 2026
--------------------------------------------------

The original official guide PDF was obtained (3537667 bytes, SHA-256
``ee7e7f71f8cc1842c6756f504558a343bb620201b86072c2a04b11fd303e3d09``).
PDF metadata identifies Version 1.0, 2015, 44 pages. Only PDF pages 39--41
(printed pages 38--40) were rendered to PNG at a 2200-pixel maximum dimension
and personally opened. No scientific images or measurements were processed.

* Printed page 38: the example text export shows ``Cell length:22``,
  ``Cell Area:216``, ``Absolute Length of Dendrite:88`` and
  ``Relative Length of Dendrite: 4.00``; another absolute/relative pair is
  41 and 1.86. There is no explicit pixel, micrometer or calibration label
  in this visible export excerpt.
* Printed page 39: the Result Inspector tables label ``Cell length``,
  ``Cell Area``, ``Abs. Length``, ``Rel. Length``, ``Level`` and
  ``Complexity``. The selected dendrite shows absolute lengths 118 and 32
  with relative lengths 4.3704 and 1.1852. The image axes show numeric
  positions, but no length-unit or calibration label is visible.
* Printed page 40: zoomed and selected-dendrite views repeat those headers
  and values. They add no explicit unit or calibration declaration.

The relative values are consistent with division by the displayed cell
length; that relationship is not evidence that either absolute value is
expressed in pixels. The screenshots depict the guide's ``test_seg_W2``
example, not an identified Supplement 8 image-1 manual export. Even an
established guide default would not prove the supplement's actual calibration.
Thus this visual check does not change the unscored determination above.

Render SHA-256 identifiers, in printed-page order 38, 39, 40:

* ``3c265a0af95ff42b09b12716df3b5fb6481d4c0573eee55fa9188647f18de05a``.
* ``d9970e27c181d61ce0041ba58639b208145f90c1399b4d8b2c1a4881a5abb225``.
* ``5ce4c6ea74e322199f22fa723e2ea62a43bdd38a2d14bb81a0bc9276795a4e9e``.

The owned temporary PDF and three renders (4531003 file bytes total) were
removed after inspection. Their source URL and hashes remain recorded here;
no original reference, prediction or parent paper asset was deleted.
