H002 fresh15: postfreeze manual-centre comparison
================================================

The original author was terminal, its pipeline and 208-file payload frozen,
and its owned viewer/runtime closed before this comparison. Reference answers
were not returned to the author or any other active blind author. No scientific
pipeline, acquisition array or new scorer was executed. The source volume's
OME wrapper hash agrees with the retained evaluator's exact input identity.

The original ``benchmark/score_point_centres.py`` was read before invocation.
The existing evaluator declares primary30 and sensitivity10/20/40-voxel
Euclidean one-to-one matching. Reference CSV columns axis-0/axis-1/axis-2
are Z/Y/X; prediction columns center_z/center_y/center_x are fractional Z/Y/X.
No rounding, rescaling, offset correction, dropped rows or new distance threshold
was introduced. Readback verified original scorer, reference and prediction
hashes. The existing numerical interpreter completed the table-only evaluation
in 0.52 seconds, exit0; no environment or dependency was installed.

The retained receipt is
``paper/supplementary/task_only_analysis/h002-fresh15-postfreeze-evaluation.json``.
Reproduce by importing ``read_csv_points`` and ``score_points`` from the
receipt's exact scorer path with the two recorded column tuples; call
``score_points(reference, prediction, t)`` for t in (10,20,30,40).
All paths, hashes, counts, distance errors and neighbour ambiguities are retained.

All15 annotated centres match at30 voxels, with mean error4.795057 and maximum
10.463856 voxels. At10 voxels14 match and one remains unmatched; at20 and40
all15 match. Eleven of the26 predictions are unmatched at the primary distance.
One annotated centre has more than one candidate within30; the matching itself
remains one-to-one. At20 there is no such ambiguity, at40 there are two.

These are useful annotation-localisation results. Reference coverage has not
been established as exhaustive. Thus the scorer's eleven ``false_positives``
are unmatched predictions, not eleven demonstrated false biological detections;
its precision/F1 are reference-relative rather than a global biological verdict.
No physical-distance or segmentation-boundary score is inferred.

The earlier independently authored H002_FRESH651_95 result also matched15/15
at30 and14/15 at10. Fresh15 therefore reproduces that annotated-centre recall,
not an improvement in it. It adds independently reviewed measurement-first
authorship and native orthogonal Points evidence. The broader blind programme
still requires its own dataset coverage and reference/visual evidence.
