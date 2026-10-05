H004 retained development: independent final image review
========================================================

Reviewed 2026-10-05. This is assisted continuation of H004_FRESH13_96,
not a fresh autonomous success. The original frozen acquisition and final
candidate remain unchanged. No reference tracing was exposed to the author.

Source identity
---------------

Both staged acquisition hashes match the existing NeuronCyto II archive
``/home/ts/.cache/openhcs/datasets/neuroncyto_ii/Testing image.zip``:

* ``Testing image/CrossOvers_Images/1_w1.tif``:
  ``2fdef90d08c132fb8de02a03071b03caed38cdd8d41cd048371dc17592b574e7``.
* ``Testing image/CrossOvers_Images/1_w2.tif``:
  ``ddd9f8a9edd0837275d6967fd746bdd424bb7a642139073e443a07eca0271847``.

Identity was established by streaming archive members into SHA256, without
extracting or changing images. The cached testing archive contains paired
images, not annotation files. This does not establish that separate reference
annotations are unavailable from the original dataset provider. Current
evaluation is visual and measurement-supported, not reference-scored accuracy.
Curator identity is not additional coaching for fresh blind authors.

Retained witnesses
------------------

Evidence root is
``/run/media/ts/hdd/openhcs-science/next-h004-retained-dev15-94-after-p001-20261005/H004_RETAINED_DEV15_94``.
Control root is
``/home/ts/wt/openhcs-issue-batch-20260929/next-h004-retained-dev15-94-after-p001-20261005/H004_RETAINED_DEV15_94/author-workspace/output``.
The complete ``analysis/artifact-manifest.json`` checksum check passed again
on 2026-10-05. No frozen payload was edited.

The reviewer personally opened all nine original ``qa/c08g`` PNGs, comprising
raw-only, result-only and combined captures at each of these positions:

* ``skeleton_upper_trunk_p98``: camera y220/x300, zoom3.
  Capture timestamps 173848657351, 173851345220, 173854766802.
* ``skeleton_mid_p98``: camera y440/x500, zoom1.5.
  Capture timestamps 173927503263, 173928850965, 173930118490.
* ``skeleton_lower_p98``: camera y660/x440, zoom1.5.
  Capture timestamps 173829621305, 173831702749, 173833039371.

All timestamps have prefix ``20261005T``, suffix
``Z_napari_6013_OpenHCS_Napari_Visualization.png``. The author records raw
window 0--62, gamma1 and binary thinning presentation. Within each displayed
triplet, framing agrees visually; saturated somas deliberately reveal faint
processes. This retained-image review did not perform fresh live navigation
or independently reread numeric camera/contrast state.

Independent interpretation
--------------------------

The upper bright southeast trunk is captured continuously into its visible
junction. The middle and lower major trunks also have useful aligned support.
Those are demonstrated positives, not a blanket rejection of the pipeline.

The lower raw view nevertheless contains a faint continuation below the
upper-right descending branch which is absent from the thinning result.
Other faint lower transverse/descending paths stop before their raw support
ends. In the middle, weak transverse connections visible between bright
structures are absent or shortened in the result-only view. Body-associated
loops remain conspicuous in the middle and lower thinning images. Combined
white-on-white display obscures these discrepancies; the raw-only and
result-only comparison makes them clear.

Decision: retain bright-trunk support as useful partial segmentation. Do not
call this complete-arbor recovery, automatic per-neuron outgrowth, or a
ground-truth accuracy result. These nine views corroborate the final author's
coverage failure; they do not independently establish a quantified improvement
over candidate07g, which was not reopened in this final review.

The author's eight nuclear-associated provisional envelopes and manually
placed local 131.150386-pixel polyline are separate evidence. Neither is an
independent ground-truth count or an automatically traced whole arbor. Source
spacing is RELATIVE, so the local length must not be reported in micrometres.

Transfer and continuation
-------------------------

Merged PR836 teaches response-trough sampling along continuous faint paths,
near-track and far-background controls, and conditional connected weak support
around strong seeds. Choosing a threshold below sampled peaks alone did not
preserve these connections. Its custom-function route uses the existing MCP
authoring owner rather than processing saved images outside that route.

This is a reusable conditional lesson, not H004-specific parameters. Ordinary
package integration carries it to subsequent fresh authors; active older runs
are not silently patched or given the curator's review. Pixel-space rooted
graph work remains with the existing PR541 owner. A new fresh run must show
whether the general lesson improves autonomous recovery.
