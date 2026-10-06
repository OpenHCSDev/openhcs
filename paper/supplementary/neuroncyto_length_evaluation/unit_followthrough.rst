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
  export length unit in the extracted text. Embedded screenshot labels were
  not independently resolved by this text extraction and are not asserted
  to lack units.
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
