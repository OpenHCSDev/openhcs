Fixed-recipe neurite cohort replay: 14 October 2026
=================================================

Result
------

The updated engine recovers additional image-supported paths and preserves
both positive treatment responses, but only slightly increases their effect
sizes. It does not explain the large response-magnitude difference from
MetaXpress. MetaXpress is an algorithm comparator, not manual ground truth.

All 20 coded wells / 180 sites completed through a fresh source-backed OpenHCS
0.8.7 MCP pipeline on detector commit ``09a808015``. All 360 staged input TIFFs
matched frozen Blind 2 / author115 inputs byte-for-byte. The Gaussian 0.8,
FITC-body, local-background-100, enhancement-disabled recipe was unchanged.
The new engine includes crossing changes since the frozen ``2b404bdf`` engine
as well as the latest repair fix: this is not an isolated whole-cohort estimate
of that final commit alone. This assisted replay does not replace any frozen
blind trial or constitute a new autonomous author. No manuscript figure changed.

Across fields, cell counts were identical in all 180. Median changes relative
to frozen Blind 2 were +3.23985% total length, +4.54294% total branches and
+0.53715% primary processes. Length changes ranged from +0.47590% to +6.63522%;
branch changes ranged from -0.58577% to +10.28571%. These are measurement changes,
not recall or accuracy estimates. Both original A25s7 and A34s8 corrected
witnesses reproduced exactly in cell count, length, branches and processes.

Treatment effects
-----------------

Use the original unweighted mean of nine site endpoints per well, two technical
wells per dose, and each drug curve's own zero-dose DMSO controls. These are not
independent biological replicates. Missing measurements are not converted to zero.
The existing paper comparison decoder reproduced all nine original endpoints
on all 180 frozen sites before evaluating the new result. It then verified
exact matched coverage and exported 90 endpoint/dose rows.

Illustrative 20 micromolar effects, percent change from own DMSO controls:

.. csv-table:: Fixed-recipe response comparison
   :header: "Treatment", "Endpoint", "Frozen Blind 2", "Updated engine", "MetaXpress"

   "Y27", "Length per cell", "+38.26", "+39.16", "+90.52"
   "Y27", "Total field length", "+48.13", "+49.08", "+99.14"
   "Y27", "Branches per cell", "+37.37", "+38.11", "+197.90"
   "Y27", "Branches per primary process", "+35.08", "+35.92", "+116.81"
   "FC-A", "Length per cell", "+30.59", "+32.28", "+85.86"
   "FC-A", "Total field length", "+21.96", "+23.47", "+73.35"
   "FC-A", "Branches per cell", "+20.35", "+22.64", "+141.62"
   "FC-A", "Branches per primary process", "+20.29", "+22.36", "+107.86"

Across all eight nonzero treatment/dose combinations, length-per-cell effects
increased by 0.192--1.685 percentage points, total-length effects by
0.139--1.502 points, branches-per-cell effects by 0.442--2.287 points, and
branches-per-primary-process effects by 0.807--2.282 points. Directions stayed
positive and agreed with MetaXpress for all these endpoints at every dose.

Control total lengths also increased by 2.736% (Y27) and 2.919% (FC-A), explaining
why absolute recovery largely cancels in control-normalized responses. The
magnitude gap remains when branching is normalized by primary processes instead
of cells; it is not resolved by changing that denominator. This does not establish
the remaining gap's anatomical or algorithmic cause.

Image review and limits
-----------------------

Personally inspected persisted raw DAPI, raw FITC at moderate and dim windows,
frozen graph overlays, new graph overlays and new graph-only views at four
preselected source crops: A02s8, A34s2, A49s3 and A60s5. Exact source coordinates
and numeric windows are saved in ``qa/display-windows.csv`` and the PNG headings.
Matched overlays use the same dim raw window for each old/new comparison.
The A60 crop includes a recovered supported lower-left continuation around
x=450--470, y=520--550. The A25s7 long-shaft witness remains the clearest
previously established repair example. Most ordinary paths are retained in
both versions. Faint distal misses, short perisomatic spurs, and crowded-body
ownership ambiguity remain; no manual tracing accuracy was measured.

The native Napari review route remains unavailable because its Image object
lacks ``_slicing_state``. These reviews use saved artifact coordinates, not a
claim of native-viewer acceptance. Installed packages were not changed.

Evidence and reproduction
-------------------------

Durable output root:
``/run/media/ts/hdd/openhcs-science/neurite-detector-development-20261014``
(also reached through the named ``agent-scratch/neurite-detector-20261014`` link).

* ``cohort-repaired/cohort-input_openhcs/results``: 180 field summaries, cell
  tables, calibrated graphs and labels; diagnostic planes are under ``images``.
* ``cohort-evaluation/treatment_effects.csv``: all doses and all nine endpoints.
* ``cohort-evaluation/joined_wells.csv`` and ``paired_sites.csv``: exact paired
  measurements; ``source_evidence.json`` records source hashes and aggregation.
* ``cohort-evaluation/per-cell-effects.png`` and ``total-effects.png`` (also PDF):
  three-method curves with individual technical-well values.
* ``cohort-evaluation/qa``: four matched saved-artifact reviews.

Pipeline: ``plans/neurite-cohort-repair-comparison-20261014.py``;
frozen pre-execution SHA256
``cb292fa8e6d903b461042281206cab19308a9e877f9f06279684437d7c999150``.
Evaluation and review scripts are alongside it and use the existing paper
comparison implementation, not a new endpoint decoder. Re-evaluation requires
no image-processing rerun. All owned runtime/worker processes exited after
completion. Lossless TIFF compression kept the full scientific output bounded
on the science drive; only disposable pip download cache (77.7 MB) was removed
from home after verifying no process references. Frozen inputs/results and
other agents' work were not removed.
