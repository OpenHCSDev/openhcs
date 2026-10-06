Independent full-plate translocation: conditional endpoint coverage
==================================================================

BBBC013_FRESH20_88 completed the paired DNA/GFP analysis of all 96 wells,
one site per well, through its original recorded MCP/native owner. Six
development wells informed scientific candidates; candidate6 was frozen before
the final plate execution. Earlier failed and revised candidates remain
separate. A prior full-plate attempt failed at E02 because nuclear and cell
label sets differed. That operational witness informed nullable membership
handling, not reserve-image segmentation tuning. This is not a new unseen
dataset or a first-candidate success.

The exact terminal job24 receipt0931 reports complete, no execution error,
and well_count96. Its execution identity is
2cd5a51b-9492-4d07-bc92-ec828465bede. The final PipelineDocument SHA256 is
d50d560b2c6e91c7bf034414fdd9e2c9a15e7dc7f14a69fbdf9333a4356900f6;
the coordinator independently recomputed that hash.

Saved endpoint and qualification
--------------------------------

Independent reading of all 96 well tables and every corresponding nuclear
object row reproduced 19732 detected nuclei and 8655 qualified ratio rows
(43.8628 percent). The cell-label tables report 19729 cell labels, three
missing cell labels, no orphan labels and three containment failures.
Unsupported cytoplasm affects9661 nuclear rows. Flags overlap:2354 border,
894 nuclear-size exclusions and three missing-cell flags cannot be summed
as mutually exclusive categories.

All detected nuclei remain in the object tables. Unsupported cytoplasmic
means and ratios are empty, not measured zero. Every qualified ratio has a
positive cytoplasmic mean; independent arithmetic reproduced each well's
qualified-row mean. Original GFP region means use acquisition uint8 values,
not display colours or normalized label identities. Cytoplasm is the propagated
cell region outside all nuclear labels. Qualification includes cytoplasmic
area/support, nuclear area and border checks; it does not validate the whole
cell boundary.

.. csv-table:: Native conditional-cohort assay statistics
   :header: "Block", "Wells", "Control wells per group", "Z-prime", "V-factor"

   Wortmannin,48,4,0.8847276461,0.6257845067
   LY294002,48,4,0.2621303920,0.4971985422

The coordinator independently recomputed Z-prime and V-factor from the saved
control means, sample standard deviations, dose dynamic range and mean dose
replicate standard deviation. Equal-well and equal-dose weights are the
declared definitions; fields and objects are not independent biological
replicates. These statistics describe the contributing GFP-supported cohort,
not unbiased all-cell translocation, potency or segmentation accuracy.

Review and retained originals
------------------------------

The author records distributed candidate6 review and four post-freeze reserve
triplets at E02/G08 for nuclear and cell results. The coordinator personally
opened G08 raw and combined cell views: reporter signal is nuclear-dominant,
and many cell estimates have little visible extranuclear extent. This supports
retaining the population-selection limitation, not accepting every body mask.
The coordinator has not yet independently reviewed every reserve screenshot,
sealed all payloads or verified terminal native/viewer closure. Those are not
claimed by this result receipt.

Original control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-fresh20-88-after-retina19-20261005/BBBC013_FRESH20_88/author-workspace/output.
Canonical final output root:
/run/media/ts/hdd/openhcs-science/next-bbbc013-fresh20-88-after-retina19-20261005/BBBC013_FRESH20_88/analysis06_final/source_workspace_openhcs.
The final tables are under checkpoints/photometry_results and results.
Original freeze-006/post-freeze-qa.json retains twelve capture identities,
numeric windows, layer visibility and camera receipts. report-context.rst
retains method, cohort eligibility, source custody and operational failures.
No source pixels, active runtime, uncertain input or scientific execution
were changed or replayed for this independent table review.
