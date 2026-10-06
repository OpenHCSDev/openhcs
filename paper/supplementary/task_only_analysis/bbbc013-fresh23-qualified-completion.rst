Completed task-only translocation analysis with self-directed repair
===================================================================

BBBC013_FRESH23_96 completed all 96 paired DNA/GFP wells through its recorded
MCP/native workflow. The author used public treatment metadata, task, MCP and
packaged skill; this repeat is distinct from the prospective held-out study.
Its own image review changed nuclear division/marker settings, lowered the
GFP foreground threshold and disabled secondary-object hole filling after a
seed-containment failure. Failed predecessors remain separate. No independent
segmentation ground truth or held-out reference scoring was used to tune it.

The final FULL_S08 execution is 0872a0a5-b835-4e7a-87d4-f528a06ed171.
The final PipelineDocument SHA256 is
ec06ed414aabaadc8fdd813b2da4a57c8db8167023a97d92e477d5178029171b.

Measured endpoint
-----------------
All 17,320 detected nuclear identities remain in cell tables: 14,631 are
eligible, 1,998 lack cytoplasm and 691 have insufficient cytoplasmic area.
Ratios use nuclear and cytoplasmic GFP means; cytoplasm excludes every nuclear
label. Excluded ratios remain undefined. The reported well endpoint is the
median eligible-cell log2 nuclear/cytoplasmic ratio. Wells, not cells, supply
the independent replicate unit; each dose and control group has four wells.
The coordinator independently checked all 96 well tables and corresponding
cell rows, unique identities, counts, ratio/log2 arithmetic and medians.

.. csv-table:: Independently recomputed conditional assay statistics
   :header: "Drug", "Z-prime", "V-factor"

   LY294002,0.8492030596152456,0.5356823774780264
   Wortmannin,0.7260146836787047,0.7259910403659129

Both series contain nine doses. The mean well-median log2 ratio rises from
0.1536 at 0.31 uM LY294002 to 2.1194 at 10 uM, then broadly plateaus.
For Wortmannin it rises from 0.00236 at 0.98 nM to 2.1193 at 31.25 nM,
then broadly plateaus. These measurements recover an assay response within
the eligible cohort. Eligibility decreases with treatment response; the
minimum per-well fraction is about 0.68. Population selection and ambiguous
whole-cell interfaces must accompany the result. Z-prime is not a mask-accuracy
score, and this analysis does not establish calibrated potency.

Image review and file custody
-----------------------------
The author's retained QA covers 12 distributed wells and final A01 nuclear
pair, isolated-body and faint-positive crops. The coordinator independently
opened final C01 and H11 GFP raw-only/result-only/combined full-field sets.
C01 has broad cytoplasmic support around nuclear holes; masks retain large
dark inter-cluster gaps. H11 has mostly nuclear-bright GFP with small or
elongated supported expansions. Some faint extensions are omitted and dense
internal interfaces are algorithmic. This supports useful fluorescence
compartments, with remaining misses stated rather than a zero-error requirement.
These two coordinator sets alone do not establish exhaustive mask accuracy.

The six reviewed native captures retain matching centre319.5/319.5, native
scale1/translation0, site/Z/time point0/0/0 and gamma1. C01 GFP limits are
0..0.48235294222831726; H11 limits are 0..0.3333333432674408, unchanged
within each matched triple. Result-only hides every image route. Source and
Cells producers refer to the same submission_7f9bb5c1e4c0.

Independent SHA256/size checks matched all 8,467 scientific payloads
(6,561,942,918 bytes), 34 authored sources and the final pipeline. All three
closed MCP journals match their final manifest. Three outer recording files
append closing records while preserving their earlier snapshot bytes exactly;
their final full-file seal remains the launcher owner's custody. No uncertain
operation or scientific execution was replayed for this review.

Original control root:
/home/ts/wt/openhcs-issue-batch-20260929/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96/author-workspace/output.
Canonical payload root:
/run/media/ts/hdd/openhcs-science/next-bbbc013-retina-fresh23-after-terminals-20261006/BBBC013_FRESH23_96.
Final results: FULL_S08/input-workspace_openhcs/results. Original report.rst,
qa-review.rst, qa-evidence-manifest.json, final-freeze.json and
journal-final-freeze.json retain the pipeline, native captures and custody.
