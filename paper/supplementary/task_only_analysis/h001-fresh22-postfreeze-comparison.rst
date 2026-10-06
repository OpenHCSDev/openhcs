Fresh bright-object repeat: reference agreement and visual selection
==================================================================

H001_FRESH22_96 used its task brief, receiving22 packaged skill and MCP on
isolated display96. All supplied pixels were development data; there was no
independent held-out field. Reference labels were opened by the coordinator
only after the original author completed and exited. No reference feedback
was supplied to a blind author, and no scientific pipeline was rerun for scoring.

The retained first method uses affine raw8--248 to0--1 conversion, global
Otsu admission, shape markers and shape watershed, suppression7pixels and
equivalent-diameter limits8--50pixels. An intensity-marker alternative was
rejected from distributed native raw/result/combined review because it merged
a lobed region and introduced an extra split/gap in a compact southwest body.
The final document restores the first method and adds a registered residual
audit; it does not change the accepted segmentation.

.. csv-table:: Existing instance matcher, one-to-one maximum-IoU assignment
   :header: "Candidate", "Predictions", "Matches at IoU >= 0.5", "Reference-relative excess", "Reference-relative misses", "Object F1", "Foreground IoU", "Mean matched IoU", "Mean matched area error (pixels)"

   First,64,58,6,6,0.90625,0.9798042428805527,0.9478913546181872,25.93103448275862
   Rejected intensity markers,61,58,3,6,0.928,0.9776330941624590,0.9614207307864892,17.224137931034484
   Retained final,64,58,6,6,0.90625,0.9798042428805527,0.9478913546181872,25.93103448275862

The reference contains64 partitions in a254x256image and derives from a pinned
notebook, not manual biological annotation. Object F1 is2*matches divided by
the sum of reference and prediction counts. Equal totals do not imply equal
partitions. Neither candidate is partition-exact up to label IDs. First/final
foreground XOR is456pixels; the rejected revision's is505pixels. The author's
visual preference and the computational reference rank candidates differently:
the rejected revision has higher object agreement but slightly lower foreground
agreement. This repeat does not improve on the earlier0.939 first-attempt or
0.944 final score; different independently chosen settings and software bundles
preclude attributing these differences to the skill alone.

Independent source and output checks
------------------------------------

The coordinator checked all863files in the frozen manifest:47,948,665bytes,
all hashes matching. It separately checked all six terminal journal seals,
the inactive/dead author scope and absence of the exact native/viewer/MCP PIDs.
The original author completed with exit0. The recorded persistent MCP shell's
aggregate exit2 is retained separately from successful scientific executions
and acknowledged runtime closure; it is not a scientific failure receipt.

All64per-object area rows independently equal their saved integer-label pixel
counts: total22,459pixels, minimum56, maximum868. First and final label TIFFs
are byte-identical. The coordinator personally opened first/rejected northeast
triplets and the final whole-field triplet; it does not claim to have opened
all authored captures. The author's final39captures cover the whole field,
four distributed regions under two windows, and four residual components.

The residual diagnostic reports102raw>128pixels outside labels, with101pixels
in four ranked components. Three ranked components are clipped edge fragments;
the fourth is a small interior spot below the admitted object scale. This
signal-threshold audit does not establish completeness below128 or resolve
connected-body identity. Its component IDs are separate from object IDs, and
repeated image-context values must not be summed into a segmentation count.

Provenance and reproduction
---------------------------

Evaluation completed2026-10-06T01:53:15Z using the existing interpreter
``/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/bin/python``
and unmodified scorer ``/home/ts/code/projects/openhcs/benchmark/score_instance_labels.py``.
For each candidate, the scorer receives ``--reference`` and ``--prediction``;
it does not filter, rescale or alter labels. Reference SHA256:
``f051ee7663f34fa9093e0d62afd409524408c9074582f95320a605c932245cb0``.
Scorer SHA256:
``19576ade67dd1a00775bd780cbcdee9d4c9d7a136c25e54bf1bdc282c764f97d``.

Reference path:
``/home/ts/.local/share/openhcs-blind-evaluation/haase_otsu_20260927/blobs_labels_skimage.tif``.
Prediction root:
``/run/media/ts/hdd/openhcs-science/next-h001-fresh22-96-20261006/H001_FRESH22_96``.
Candidate directories are ``attempt01``, ``attempt02`` and ``attempt03-qa``;
each prediction is
``staged-input_openhcs/results/image.tif_channel-1_z_index-1_timepoint-1_BrightObjects_step1.labels.tif``.
First/final label SHA256:
``117171cc83dfce1818c3963791343132abaf9dee86035119267a69ef03528497``.
Rejected label SHA256:
``d80266283eff9ad506225638b43c7484556c6a88fb4bec2e33b88e556806656d``.

Final source and custom-callable SHA256 are respectively
``da1b9cdd9afbf8332cf70b1994550148c1b303fffe87a924759cb85c5b32c54f`` and
``c57d24cc2a31de389a2146c63d41eb4d34529d6f8fa1c0377e61431539f78b8e``.
The frozen manifest under the author's ``output/final/frozen-manifest.json``
has SHA256
``873924d0c500f321164257b83282f8f3565cdd4416d06bb8b017a05b2a94df80``.
Author-history prefixes in that manifest are explicitly distinct from complete
terminal journals; the enclosing ``OWNER-TERMINAL-CLOSED-JOURNALS.sha256``
seals the six completed journals after author exit. Neither scientific
payloads nor acquisition files were copied into this manuscript change.
