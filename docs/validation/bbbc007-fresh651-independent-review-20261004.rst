BBBC007 fresh651: independent frozen-result review
=================================================

This is coordinator postfreeze review, not feedback to an active blind author.
The original BBBC007_FRESH651_88 trial remains immutable. No reference outlines
were opened or scored, no scientific execution was repeated, and no active
viewer was attached for this review.

Verified evidence
-----------------

The author output is retained at
``/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc00788-after651-20261004/BBBC007_FRESH651_88/author-workspace/output``.
The durable science root is
``/run/media/ts/hdd/openhcs-science/next-bbbc00788-after651-20261004/BBBC007_FRESH651_88``.

Every entry in the original manifest's ``attempt_sources`` and ``payloads``
arrays passed ``sha256sum --check --quiet``. This verifies those arrays, not an
outer recorder seal or every mutable runtime file. Native and viewer processes
were independently absent and their 6020/6021 listeners closed before review.

The final candidate completed all 16 DNA/ACTIN pairs. The author reports 1,335
nuclear identities and 1,335 seed-associated cell labels. Its A02 site 1 table
contains 38 nuclei, no absent corresponding cell IDs, no extra cell IDs and no
lost seed pixels. These are internal consistency checks, NOT detection recall:
``missing=0`` in this diagnostic means missing corresponding secondary IDs,
not zero missed biological nuclei.

The coordinator opened these unchanged native PNGs:

* ``qa/raw-A02-1-dna/20261004T193330589667Z_napari_6021_OpenHCS_Napari_Visualization.png``:
  black initial capture; rejected as a biological witness.
* ``qa/raw-A02-corrected/20261004T193443815282Z_napari_6021_OpenHCS_Napari_Visualization.png``:
  visible A02 site 1 DNA field, including a bright dense right-middle cluster.
* ``qa/candidate05QA_A02_1_dnaCombined/20261004T202719055543Z_napari_6021_OpenHCS_Napari_Visualization.png``:
  final DNA field with cyan nuclear boundaries. Many bright nuclei in the dense
  right-middle cluster have no outlines; isolated objects elsewhere do.

The corrected raw and final combined screenshots have different screen
footprints. They support the field-level missing-cluster finding, but are not
claimed as a pixel-matched crop or quantitative intensity comparison. The final
capture receipt identifies A02 site 1, native y/x display, point
``[0, 0, 0, 1, 224, 224]`` and resource SHA-256
``ec5c89db21b23f6b79615bcf1cfd93060af9c6b384a779418f9f5c52caef5df2``.

What improved and what did not
-----------------------------

The first completed scientific candidate had 1,417 nuclei. Later secondary
growth changes recovered seed containment but did not establish physical
whole-cell boundaries. The last nuclear change replaced shape markers with
intensity markers and increased suppression from 6 to 8 pixels. A02 site 1
detections fell from 46 to 38 and the visibly missing dense cluster remained.
Neither count decrease nor matching primary/secondary IDs proves improvement.

The author rejected full-field population/phenotype use, while retaining useful
isolated-object diagnostic findings. This is evidence of autonomous failure
detection, not successful task-wide segmentation. Its recorded client exit
overran the 75-minute deadline by about eight seconds; that operational result
is separate from the scientific rejection.

Transferable learning and next diagnostic
-----------------------------------------

The existing canonical ``segmentation-diagnostics.md`` already instructs an
author to follow a missed object through support, components, seeds, unfiltered
labels and retained labels before changing a downstream stage. The frozen
candidate05 rationale hypothesises a marker failure from final outlines; the
reviewed rationale and aggregate tables do not establish where the dense
objects first disappeared. A marker-only change therefore remains a hypothesis,
not a demonstrated repair of the earliest loss.

For a separately recorded development continuation, inspect that dense witness
at these intermediate stages and preserve a genuine close-pair and isolated
positive as controls. In particular, distinguish absent support from a merged
component subsequently removed by size filtering; neither is established by
this final screenshot alone. This is a general stage-diagnosis lesson, not a
dataset-specific accepted parameter recipe. Do not send this diagnosis to an
ongoing fresh author or rewrite the frozen trial as assisted success.

No new duplicate skill rule was added: the stage-tracing instruction already
exists. The actionable gap is establishing whether an author obtained the
relevant intermediate evidence before its repair, then testing fresh authors
against the packaged procedure rather than repeatedly adding warnings.
