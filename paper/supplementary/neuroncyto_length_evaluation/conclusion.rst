NeuronCyto II image-1 length-reference qualification
==================================================

Recorded 6 October 2026. This is a read-only comparison of frozen artifacts
and retained published reference measurements, not a scientific rerun or an
accuracy score. No author received reference measurements or settings.

Conclusion
----------

The prediction inputs match the official NeuronCyto II image-1 field
byte-for-byte. The illustrated frozen first prediction reports total rooted
outgrowth of 4085.1924932857874 pixels. The published manual reference reports
primary length 3633.672, secondary length 198.929, tertiary length 0 and total
length 3832.601, but its table does not specify units. Spatial manual traces
and cell correspondences are unavailable in the retained reference material.
Consequently, no defensible manual-length accuracy or percentage error is
reported.

The numerical prediction is the FIRST candidate illustrated in the
main-shaft panel, not the final candidate, a retuned best-score selection,
or a principal-shaft-only measurement. Its total covers the final rooted-path
partition (25 processes and 12 branches). The manual branch-order category
``primary`` has not been demonstrated equivalent to the principal-shaft
endpoint requested for this comparison. The descriptive aggregates in
``aggregate_lengths.csv`` must not be subtracted or ratioed as an accuracy
metric without compatible units and endpoint definitions.

The target was clarified after the run as thick soma-connected neurite shafts,
including their faint stretches, not exhaustive filopodial tracing. The final
chronological repair expanded beyond that target and is not an accepted final
shaft result. Main Figure 5 now shows only the retained initial candidate and
labels it accordingly. This editorial selection does not retroactively change
the original brief, its frozen outputs or its autonomous outcome.

Input identity
--------------

Official cached archive:
``/home/ts/.cache/openhcs/datasets/neuroncyto_ii/Testing image.zip``
(SHA-256 ``4fe906a9dc2852b91181a28cbeae1781afe22ba2d77d1442c302a27bea6c9afd``).
Its retained inventory contains 60 TIFF files and Thumbs.db, with no manual
spatial tracing files. This does not establish that the original authors
never retained tracing files elsewhere.

Prediction input root:
``/run/media/ts/hdd/openhcs-science/next-h004-retina-fresh20-95-96-20261005/H004_FRESH20_95/paired_input``.

The staged inputs and original ZIP members were independently SHA-256 checked
again for this record:

* ``field_w1.tif`` = ``Testing image/CrossOvers_Images/1_w1.tif``:
  ``2fdef90d08c132fb8de02a03071b03caed38cdd8d41cd048371dc17592b574e7``.
* ``field_w2.tif`` = ``Testing image/CrossOvers_Images/1_w2.tif``:
  ``ddd9f8a9edd0837275d6967fd746bdd424bb7a642139073e443a07eca0271847``.

Frozen prediction provenance
----------------------------

Original source:
``/home/ts/wt/openhcs-issue-batch-20260929/next-h004-retina-fresh20-95-96-20261005/H004_FRESH20_95/author-workspace/output/attempts/first/pipeline.py``.
SHA-256:
``11ad2a8c3a4587bc5cf1736e6b2b4388980e945875e9db132f7b644d5bd330d8``.
The adjacent ``FIRST-FREEZE.sha256`` preserves the original source freeze;
the final report and later repair attempts remain distinct and unchanged.

Persisted artifact root:
``/run/media/ts/hdd/openhcs-science/next-h004-retina-fresh20-95-96-20261005/H004_FRESH20_95/first/paired_input_openhcs/results``.

* Summary ``paired_site-1_z_index-1_timepoint-1_neurite_outgrowth_summary_step0_details.csv``:
  SHA-256 ``cb2d8a7df8cc89ac72ad90db839f5a6ee94e15acc720f150dcf3fb94eaa709fe``.
* Per-cell table ``paired_site-1_z_index-1_timepoint-1_neurite_outgrowth_cells_step0_details.csv``:
  SHA-256 ``256a91d908e228a00c59e5e7ff8856239f1ef6f32439bc837bb10b3c819ebfc1``.
* Graph ``paired_s001_w1_z001_t001_neurite_morphology_step0.graph.roi.zip``:
  SHA-256 ``504187b118797febeff738bdc6731c685db7a16dd5798312bb759a85fc71e189``.

The summary declares ``coordinate_unit=pixels``. All graph ROI metadata
records declare pixels, with source spacing ``unit=pixels`` and
``values_zyx=[1.0, 1.0]``. This is a pixel-coordinate declaration, not an
invented micrometer calibration. The summary and graph hashes were rechecked;
no prediction artifact was modified or regenerated.

Published reference provenance
-------------------------------

Ong et al., 2016, NeuronCyto II:
https://doi.org/10.1002/cyto.a.22872
and https://pmc.ncbi.nlm.nih.gov/articles/PMC5089663/.
The article describes manual NeuronJ annotation followed by quantitative
branch-level measurements. It does not supply spatial correspondence for
this frozen prediction in the retained tables.

The existing ``paper/supplementary/neuroncyto_reference_audit.md`` records
the original supplementary DOCX extraction on 15 September 2026. The DOCX
files were read in memory and are not locally retained. Their hashes below
are inherited source provenance from that audit, not claims of a fresh
DOCX download or byte check:

* Supplement 8, Europe PMC ``CYTO-89-747-s008.docx``, publisher
  ``cytoa22872-sup-0008-suppinfo08.docx``:
  ``038c28102a467eb56ec30d9c4404a8301b2889629dfb6b16c35a359c0ed645c0``.
* Supplement 9, Europe PMC ``CYTO-89-747-s009.docx``, publisher
  ``cytoa22872-sup-0009-suppinfo09.docx``:
  ``8062f1e9b9cf8bba021b877ba48d0b8dff0cd9b6434991d26f011e444b847c0b``.

Supplement 9 lists eight per-cell total lengths for image sequence 1:
426.82, 172.375, 751.962, 395.04, 669.783, 343.629, 587.841 and 485.152.
It gives no spatial cell identifiers or separate exhaustive-annotation
assertion. These values were not paired to prediction labels by order,
count, sorting or closeness. Supplement 8's total is retained as printed,
not replaced by a sum of rounded per-cell entries.

Remaining scoring requirements
-------------------------------

An accuracy comparison requires documented reference units compatible with
the pixel-coordinate prediction and compatible length definitions. Spatial
traces or independently reviewed, provenance-bearing correspondence are
additionally needed for principal-shaft endpoint/coverage errors and per-cell
comparisons. No such correspondence is invented here. User acceptance of
the visible main-shaft illustration is separate from this unavailable
quantitative reference score.
