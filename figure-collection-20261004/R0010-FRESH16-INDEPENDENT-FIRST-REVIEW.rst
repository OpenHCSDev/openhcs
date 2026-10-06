R0010 fresh16: independent FIRST-candidate visual review
======================================================

Scope
-----

The parent reviewed nine original native captures: matched raw-only,
result-only and combined views in northwest, southeast and border regions.
This is a development checkpoint, not a frozen final assessment or a fresh
autonomous repeat. The original author continued after an interrupted CLI
session. No reference masks or manual counts were consulted, and this review
was not sent to the scientific author as parameter coaching.

The original captures are under::

  /run/media/ts/hdd/openhcs-science/next-p00189-retina88-fresh16-20261005/R0010_FRESH16_88/qa/continuation01/FIRST

Presentation and selection are retained in ``QA-CAPTURE-INDEX.json`` in the
author's continuation output. These triplets use the same XY camera within
each region, raw contrast 0--42 and gamma 1; Shapes are translucent at 0.7.
The source declares 0.12353054911059548 micrometres per pixel. Camera centres
correspond to native coordinates (600, 600), (2100, 2100), and (120, 1293).
Camera centre is not the viewer's current-step coordinate.

What the images support
-----------------------

* Northwest: conspicuous bodies are localised, including two distinct bright
  neighbouring bodies. Their separate footprints are useful positive evidence.
  Ragged boundaries and diffuse unlabelled flecks do not establish either a
  complete body census or a false-negative count.
* Southeast: some weak and diffuse signals are covered, while much of the
  punctate background remains unlabelled. A long lobed region near the lower
  right has ambiguous biological extent; it is not proof of a correctly
  separated pair. Localisation is better supported than complete envelopes.
* Border: a continuous ring-like raw envelope at the upper border has adjacent
  blue and purple fragments. This is a plausible false split, not confirmation
  of two biological cells. A lower green footprint retains a lace-like interior
  and excludes part of the broad raw envelope. These are concrete weaknesses
  in area/shape support even though the detections lie on positive signal.

The useful bright-body detections should not be discarded because some
boundaries fail. Conversely, a displayed label count cannot establish accuracy.
This review provides neither an accuracy percentage nor a claim that this
attempt reproduces or improves the earlier accepted retinal result. The
scientific author retains responsibility for its ongoing diagnostic and repair.

Original witnesses
------------------

The filename stem below is followed by
``Z_napari_6021_OpenHCS_Napari_Visualization.png``. SHA256 is over each original
PNG; no cropped or contrast-modified derivative was used for this review.

.. list-table:: Matched original captures
   :header-rows: 1

   * - Region/view
     - Stem
     - SHA256
   * - nw/raw
     - 20261005T192440386839
     - d38ca5c3901a95fad0e4006859d7a374f4a048b9f320648d875717900202bf4b
   * - nw/result
     - 20261005T192442122937
     - 6d37c4a238d16016086fa86d6606d039b520ca810dc8d3e70c84626ffbdbf980
   * - nw/combined
     - 20261005T192444028215
     - 1112cafcd58ae2e09e15d409b7233dd9987177801a915cd91d287f0061f75666
   * - se/raw
     - 20261005T192507419855
     - 0847a130b957b4036f1623e45804f6cc71addb07cf664b09f57c1aafeb78a13a
   * - se/result
     - 20261005T192508227217
     - 67c9151b38af39446314f7dd9e5a954d693d9be95d440c0fd515b4112d2f6bef
   * - se/combined
     - 20261005T192508863880
     - 236d7841bdccc0a7ee697ae0b650730d2a51e5aaba5ccd797ccec1d21ee1495f
   * - edge/raw
     - 20261005T192511854489
     - 02d93495f1d2f1203057d80a070fccf56401b0555ae287c3aadb2d2574b1aedd
   * - edge/result
     - 20261005T192512580905
     - ff8168bc120bec422f4bedac5ad3474f19f92679efa40129b067227ec5284021
   * - edge/combined
     - 20261005T192513221760
     - 4f362d4e21101729331ca72299d3443463f0a729a9f9294c1cd40eb105e5b21b

Technical context, separate from biology
---------------------------------------

``FIRST-RATIONALE.md`` records that catalogue discovery initially selected an
unrelated version-0.8.6 endpoint and rejected it before a catalogue RPC was
delivered. Explicit preparation on the original port 6020 succeeded with the
same process identity. A region request missing singleton route axes was also
rejected before correction. Neither event changed scientific settings; neither
is biological acceptance evidence. The existing foreign-endpoint rejection
fix (#464/PR465) must not be confused with choosing the intended default owner.

Post-freeze final comparison
----------------------------

This later section preserves the FIRST assessment above. The parent personally
opened the final raw-only/result-only/combined triplets at the same northwest,
southeast and border locations. The capture index confirms the same canvas,
XY scale/translation, raw 0--42 window, gamma 1 and zoom 8.095, with matched
camera centres (apart from floating-point roundoff). More strongly, each final
raw PNG has the same SHA256 as the corresponding FIRST raw PNG above. Changes
in mask appearance therefore do not depend on a changed raw presentation.

* Northwest: final footprints are more coherent and less ragged. The two
  conspicuous neighbouring bodies remain separate; the repair did not simply
  trade that useful separation for fewer labels.
* Southeast: diffuse body-like positives retain smoother footprints and much
  of the punctate background stays unlabelled. The long lobed right-hand
  footprint remains ambiguous, and the small bright profile above it is still
  omitted. Smoother geometry is not a completeness score.
* Border: the lower lace-like footprint becomes a more coherent supported
  region. The upper ring-like envelope still has adjacent separate footprints;
  the possible false split has not been demonstrated resolved. Broad raw
  extent and weak-body coverage remain uncertain.

Accept useful regional body localisation and the visible reduction in
fragmented geometry. Keep missed-object, instance-identity and full-envelope
limitations separate rather than rejecting every detection or claiming a
complete retinal census. This is a self-directed repair of a retained run,
not evidence of improved first-attempt accuracy, a new fresh autonomous trial
or agreement with manual counts. No reference answer was opened and no
dataset-specific correction was supplied to the scientific author.

The author's final report identifies 110 image-level candidate instances
(FIRST had 130), including eleven source-edge labels. Those counts are
algorithm outputs, not a biological accuracy estimate. It records a threshold
smoothing change from 4 to 12 pixels and a separate photometry-routing repair;
the latter retained the repaired label TIFF byte-identically. This review
corroborates the local visual change, not an independent causal re-execution
or exhaustive check of fluorescence tables.

The parent independently verified all 170 SHA256 entries in the original
``continuation01/FINAL-MANIFEST.json``. The final candidate remains frozen at
``attempts/REPAIR01/technical02/pipeline.py`` in the author's continuation
control directory. Original source, failed attempts, captures and journals
were not modified or copied into another payload tree.

Final witness stems below use the same filename suffix as the FIRST table,
under ``qa/continuation01/FINAL/REGION/VIEW``. Their individual hashes remain in
the verified original manifest.

.. list-table:: Personally opened final native captures
   :header-rows: 1

   * - Region
     - Raw stem
     - Result stem
     - Combined stem
   * - nw
     - 20261005T193315651262
     - 20261005T193317642846
     - 20261005T193318936057
   * - se
     - 20261005T193324784587
     - 20261005T193326185394
     - 20261005T193327597963
   * - edge
     - 20261005T193333270792
     - 20261005T193334622202
     - 20261005T193335942373
