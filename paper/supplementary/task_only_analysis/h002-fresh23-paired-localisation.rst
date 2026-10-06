Fresh volume repeat: paired first and final annotation localisation
==================================================================

H002_FRESH23_ROTATION_89 independently selected REPAIR05 before evaluation.
This record compares its immutable FIRST and final tables; it does not select
the highest-scoring intermediate candidate. No scores or reference coordinates
were returned to the author or any subsequent blind author. Frozen source,
ordinary-body repair witnesses and biological limits are recorded in
``docs/validation/final-self-repair-h002-h004-20261006.rst``.

All fractional zero-based Z/Y/X predictions are evaluated without filtering,
rounding, rescaling or offsets. The existing one-to-one Euclidean matcher and
its retained thresholds are unchanged: 30 voxels primary, 10/20/40 sensitivity.
These are unscaled voxel distances, not micrometres or boundary scores.

.. csv-table:: Independent post-freeze table comparison
   :header: "Attempt", "Distance", "Matched of15", "Unmatched predictions", "Mean error", "Maximum error", "Ambiguous reference points"

   FIRST,10,14,17,4.9934271476,7.8198125690,0
   FIRST,20,15,16,5.3655843658,10.5757854208,2
   FIRST,30,15,16,5.3655843658,10.5757854208,3
   FIRST,40,15,16,5.3655843658,10.5757854208,3
   FINAL,10,14,12,4.4496411478,7.2148904488,0
   FINAL,20,15,11,4.8580507660,10.5757854208,0
   FINAL,30,15,11,4.8580507660,10.5757854208,1
   FINAL,40,15,11,4.8580507660,10.5757854208,2

At30, reference-relative F1 is0.6521739130 FIRST and0.7317073171 FINAL.
Both recall all15 annotations; FINAL retains26 predictions versus FIRST31.
The reference has not been established as exhaustive. The scorer's
``false_positives`` field therefore means unmatched predictions, not
demonstrated biological false detections. This supports within-run localization
repair, not a complete census, segmentation-boundary accuracy or superiority
to the preceding fresh22 repeat (whose mean error was4.8205338250).

Custody and reproduction
-----------------------

Before reference access, the author froze its choice at2026-10-06T03:19:24Z,
and its original terminal cleanup recorded exact native/viewer closure and
client exit2. The coordinator independently found native2819223, viewer2829329
and MCP2811321 absent, verified seven final control hashes and all439 scientific
manifest entries, and read the complete original scorer before evaluation.
No pipeline, viewer, environment or scientific array was rerun or created.
Original table-only evaluator command exited0.

Read ``read_csv_points`` and ``score_points`` from::

  /home/ts/code/projects/openhcs/benchmark/score_point_centres.py

Scorer SHA256:
``a80eecefc791dd755444892cde5816df8c6a6bad15b9dd350fadfd23d6156af8``.
Reference CSV, columns ``axis-0/axis-1/axis-2``::

  /home/ts/.local/share/openhcs-blind-evaluation/haase_cells3d_20260927/cells3d_annotations.csv

Reference SHA256:
``572f71b8770b4190cc6806000bde6a4e118f0c17d758faef0a7a5d0e4fbaa81f``.
Prediction root::

  /run/media/ts/hdd/openhcs-science/next-h002-h004-fresh23-rotation-20261006/H002_FRESH23_ROTATION_89

Read the FIRST ``attempt01`` and FINAL ``attempt05`` paths beneath that root:
``staged-input_centres/results/image.ome.tif_site-1_channel-1_timepoint-1_h002_centres_step0_details.csv``,
columns ``center_z/center_y/center_x``. Their SHA256 values are respectively
``cd3c61d90b72875c8ade56085c380de3334ef846eb425bde772d5752a706155e``
and ``45f81e0f0b9c22f22d7ab5347beb7117314979aa7f6ad6fd50ccc6efd95aaf27``.
Call ``score_points(reference, prediction, threshold)`` for10,20,30,40 using
the existing paired-raw installed interpreter. Do not send these annotations
or metrics into an authoring context.
