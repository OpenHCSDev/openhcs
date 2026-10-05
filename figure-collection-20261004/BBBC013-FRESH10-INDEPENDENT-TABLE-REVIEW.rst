BBBC013 fresh10: useful bounded tables, incomplete whole-plate inference
=====================================================================

Independent parent readback, 2026-10-05. The frozen author report and QA review
were read completely. No reference answers, image processing, scientific
execution or assay-statistic recalculation was performed for this review.

The completed REPAIR01_BOUND4 output has 1,015 cell-table rows and four well
rows: A01 (312), A02 (249), C06 (190), H12 (264). Of these cell rows, 871 have
finite nuclear/cytoplasmic GFP ratios and 144 have undefined ratios. Undefined
values remain explicit; they are not zeros or substituted denominators.
The two assay-summary rows declare insufficient_replicates_or_range, with
undefined Z-prime and V-factor. A02 is measured but metadata marks its assay
role empty; its cells do not establish a negative-control replicate.

These are delivered provisional measurements, not accepted comprehensive
segmentation or a manual-reference score. The author reports useful isolated
body outlines alongside merged neighbours and missing dim cytoplasm in
distributed A01, C06 and H12 native reviews. Parent did not independently open
those bitmaps for this table-only review. Four-well success is not whole-plate
success, and output counts do not establish biological accuracy.

The separate whole96 execution failed its nucleus/cell containment check.
The report records retained nucleus/cell/cytoplasm labels across 96 wells,
but its runtime GFP intensity rows were not exported before closure. No
whole96 cell, well, dose-response or assay-statistics table was produced.
Labels alone cannot reconstruct the missing photometry evidence in this
review. The containment and preservation boundaries remain separate from the
biological segmentation defects; Singer owns source diagnosis, and Dewey owns
any later retained-context development after a lane is available. No finding
was fed to an active fresh science author.

Original report/pipeline root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-fresh10-95-20261005/BBBC013_FRESH10_95/author-workspace/output

Original completed-table root::

  /run/media/ts/hdd/openhcs-science/next-bbbc013-fresh10-95-20261005/BBBC013_FRESH10_95/attempts/REPAIR01_BOUND4/source-workspace_openhcs/results

Original table SHA256, checked against current bytes::

  3d40b9d5ff4070ddadb21f58cd9ff9a7ab9bea396d76434261416b30d5e691a9  A01_cell_table_step5_details.csv
  688254e9df5ef99c81d3afd611fc5fea039e6ed664c024050b30d94d8bd73d2e  A01_well_table_step6_details.csv
  24495f400ac337ec31044bf007e7f0ed52bb3d8da7561174d4d8ff7a81513b99  A01_dose_response_table_step7_details.csv
  b939c6b39b3932459f3b12d1de08e53ecbe287c4ef9a1654351c8f54d15017c0  A01_assay_statistics_step8_details.csv

The original candidate, report, failure receipts and journals remain unchanged.
This record preserves the useful completed scope and the precise remaining
failure for paper assembly and subsequent repair; it is not a new autonomous
pass, a portable scientific archive or an acceptance of the failed plate.
