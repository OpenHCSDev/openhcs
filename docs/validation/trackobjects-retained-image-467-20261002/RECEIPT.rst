TrackObjects retained image: partial correctness repair (#467)
============================================================

TrackObjects previously discarded ``save_color_coded_image`` and returned its
original grayscale primary image. Its module declaration also ignored the
authored Color / Color and Number display choice. This change implements those
choices using the native stable track-ID palette and optional centroid labels.
The existing TrackObjectsResult assembles the image and unchanged measurement
ABI. Completed TrackingFrameResult values retain the exact centroid domain
used for measurement arithmetic and rendering. No tracking kernel changed.
Authored display values use the existing setting binding and canonical callable
enum coercion; the module does not read and coerce the same setting again.

The renderer uses the current declared Matplotlib dependency. It reads the Agg
RGBA buffer directly and copies RGB pixels into the owned output; it does not
encode and decode a temporary PNG. The image is normalized to float32 with the
existing source-normalization owner, retains the declared timepoint axis and
source context, and declares a trailing RGB channel axis and intensity proof.

Gates and limits
---------------

* The focused module has 18 passing tests. These cover the original measurement
  and relationship controls, both display choices, retained-image shape/dtype,
  channel/axis/intensity metadata, input isolation, empty-frame measurement
  scale, malformed ID/center domains, and centroid ownership reuse.
* The original frozen 9aa capture admitted 44 actual typed graphs covering all
  21 frames. Its original OpenHCS output has two CSVs / 86 rows and 21 PNGs,
  exactly unchanged by capture. No PNG-derived segmentation or track IDs were
  supplied as inputs.
* Pure row replay on 42 actual before/after frame graphs is exact for all row
  fields, centroid values, label arrays and intended trajectory-state mutation.
  Linkage, centroid, transition-count and count-reduction kernels are unchanged
  by AST comparison against main142. Full old source/result graph transport into
  clean main is separately RED: that PR394 graph requires DurableSourceMetadata,
  which does not exist on the clean-main branch. No compatibility class was
  introduced to conceal this source mismatch.
* All 21 committed renderer frames match the latest native-algorithm prototype
  exactly. The direct Agg buffer also matches the previous PNG encode/decode
  path under four bounded default/font/DPI/background/interpolation controls.
  Primitive NPZ views are source-hashed views of the admitted original arrays;
  they do not establish a new metadata or alias transport contract.
* Native CellProfiler's original draw function, run on the same true labels,
  IDs and centroids, matches both original native repetitions' 21 panels exactly.
  This verifies the retained rendering inputs independently of the PNG outputs.

The full native PNG gate remains RED: current Matplotlib 3.11.2 / FreeType
2.14.3 differs from native CellProfiler's Matplotlib 3.7.5 / FreeType 2.6.1 at
3,340 antialiased number-text pixels over the 21 panels. Both environments use
the same hashed DejaVuSans font. Palette regions match. The strict comparator
has not been relaxed, text pixels are not excluded, and the native environment
is not invoked by production rendering. This is a draft partial correctness
repair; it must not close #467 or claim complete saved-image parity yet.

Matplotlib documents its 3.11 font rendering overhaul and the inability to
reproduce previous releases' exact pixel values:
https://matplotlib.org/stable/release/prev_whats_new/whats_new_3.11.0.html

No end-to-end runtime gain is claimed. No new public pipeline was run for this
patch. The dominant performance investigation remains separate.

Retained evidence
-----------------

The JSON receipts adjacent to this file retain source/input/output hashes and
frame-by-frame scopes. Original failed controls and renderer experiments remain
at their recorded /var/tmp paths. Main142's implementation census is recorded
at /var/tmp/openhcs-trackobjects-main142-nra-owner-census-20261002.json using the
original NRA owner tooling; the tracked display behavior is independent of the
existing cv2 measurement display renderer's different palette/blending/font
contract. Original architectural R0/R1 qualification remains a separate gate.
