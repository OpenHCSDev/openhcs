P001 pooled analytical-input development comparison
===================================================

Disposition and scope
---------------------

P001_POOLED_STACK_DEV25_88 is an explicitly requested same-author development
comparison, not a fresh task-only autonomous trial. All nine 1024-square fields
are development evidence. There is no independent reference segmentation,
untouched validation set or supplied biological count. Reviewed principal
process geometry is useful; complete arbors, fine branches and ownership at
crossings remain unvalidated. Fields overlap and are not independent replicates
or a deduplicated whole-well census.

The source workspace is
``/home/ts/wt/openhcs-issue-batch-20260929/next-p001-pooled-stack-dev23-88-20261006/P001_POOLED_STACK_DEV25_88/author-workspace/output``.
The canonical scientific payload root is
``/run/media/ts/hdd/openhcs-science/next-p001-pooled-stack-dev25-88-20261006/P001_POOLED_STACK_DEV25_88``.

Input fit and actual pipeline chain
----------------------------------

The registered ``stack_percentile_normalize`` fitted physical FITC channel 2
over all 9,437,184 pixels with SITE variable and CHANNEL grouping. Its fixed
0.1/99.9 percentiles mapped raw bounds 126/49305 to uint16 0/65535. The same
mapping was used for every field; there was no selected-crop or per-field refit.
The gain was 1.3325809796864516. Raw-unit local-difference settings 200 and 50
became 266.5161959372903 and 66.62904898432258. Clipping and integer quantization
prevent exact pixelwise equivalence. Nuclear DAPI inputs remained byte-identical
raw acquisitions; this is not an all-channel normalization experiment.

The first complete document saved all nine fitted FITC checkpoints, then failed
because its disabled DAPI dispatch was pruned and the following analysis lacked
the required nuclear channel. That failed execution was retained, not replayed.
A declared reload consumed the saved FITC checkpoints and byte-identical raw
DAPI with the acquisition calibration and positions. The separate final analysis
completed all nine fields in 119.158859 seconds.

``pipelines/FINAL_ATTEMPTED.py`` is byte-identical to the submitted
``pipelines/POOLED01_RELOAD_ANALYSIS.py``. Its SHA-256 is
``db530a09e0b8338a3a5112144cfc6b02522dfb03c1c588d006d864a0080a79ad``.
The original fit document is ``pipelines/POOLED01.py``, SHA-256
``778a4301411c0e1fe5cf9979da96ec6c066514b243b58e55bf23dee2fbf5a1c2``.
``evidence/final-pipeline-chain.json`` records both jobs and exact checkpoint
inputs; its SHA-256 is
``fc474094f08467df4ab28dd3b50597b763d588085dfdf107fcad16738015f210``.
FITC measurements in this candidate use analytical units despite inherited
``source_image_name=raw_w2`` ancestry. They are not raw acquisition photometry.

Nine-field software endpoint comparison
--------------------------------------

Prior values below are the retained author's predecessor comparison. The parent
independently reopened every current per-cell and summary CSV, verified unique
IDs and row counts, and reproduced every current length sum. This proves table
consistency, not biological completeness or an independent prior re-score.
Counts describe software body labels; lengths use declared micrometres.

====== ============ ============ ================= ================= ==========
Site   Prior labels Pooled labels Prior length um   Pooled length um  Change %
====== ============ ============ ================= ================= ==========
1      188          188          16448.715         16400.475         -0.2933
2      243          243          14550.272         14514.970         -0.2426
3      222          221          13291.466         13396.698          0.7917
4      179          179          13688.058         13659.840         -0.2062
5      261          261          18337.413         18504.321          0.9102
6      266          266          20095.887         20458.251          1.8032
7      121          121          10825.968         11069.072          2.2456
8      244          244          17649.231         18141.533          2.7894
9      350          350          22801.244         23610.237          3.5480
====== ============ ============ ================= ================= ==========

Matched review and causal interpretation
---------------------------------------

The parent opened ten retained native MCP PNGs: predecessor-soma39 and
pooled-settled-soma39 raw/result/combined triplets, the regression-s3-pooled-small
triplet, and mosaic-settled-NE dual-channel view. Their exact snapshot hashes,
isolation and applied viewport receipts are in ``evidence/capture-index.json``.
The soma comparison retains the same world camera centre
``[0, 691.356, 778.1144]``, zoom 3, with raw FITC window 71..1200 and gamma 1.
Result-only acknowledgements contain only body/graph routes; combined views add
the same raw route. Principal soma-supported paths remain aligned in both
candidates, while faint/outer tips remain incompletely followed. A small bright
site-3 punctum is visible without a retained pooled body outline; the parent did
not independently establish its cell identity or inspect its prior triplet.
The one assembled dual-channel view shows locally continuous process/nuclear
signal, not a numerical registration or all-seam validation.

Author-retained native profiles at a site-7 crossing show changed enhanced and
local-response amplitudes but unchanged threshold/candidate samples on that
profile. Quiet-control candidate samples remain zero. Gain-converted local
differences therefore explain limited local admission change; the pooled
transform is not globally erased, since field masks and lengths differ.
This is evidence of local stability, not a demonstrated broad accuracy gain.
The author inspected 106 captures; the parent's ten-image review is narrower.
The raw 2868-square mosaics were reused and reviewed, not reassembled or
segmented with this pooled candidate. No cross-field deduplication is claimed.

Freeze, recovered report and terminal custody
--------------------------------------------

``evidence/scientific-freeze-manifest.json`` names 627 static files and separate
live-writer prefixes. Its SHA-256 is
``534fe0a08d3751c03ccf88a86e7b4f671fa009064e2375adb7799045d98b919b``.
Independent complete-file checks found 626 matches and one mismatch: after the
author froze its 20,477-byte report, the enclosing launcher's final-answer
destination overwrote ``output/FINAL.rst`` with a 447-byte summary. The original
manifest and overwritten path remain unchanged. OpenHCS issue 991 and PR 992
track the existing launch owner's correction.

The report was separately recovered from the retained native journal
``rollout-2026-10-05T23-42-02-01a10f4d-d7be-7100-822b-99bd4ee47d25.jsonl``:
authored addition at line 951 and two authored line-break corrections at line
967. Recovered size and SHA-256 exactly match the original frozen entry:
20,477 bytes,
``093473c7583c51087d4fea59b76f0dacdd0684f1fe4cd038a61cf754517b1a42``.
The separately identified recovery is retained at
``/home/ts/.cache/agent-scratch/p001-report-recovery-20261006/RECOVERED-AUTHORED-REPORT.rst``
with ``RECOVERY-RECEIPT.json``; this is not a rewritten freeze or new analysis.

The outer author journal ends with ``turn.completed`` and actual exit 0.
The one retained MCP client's actual exit was 1, independently preserved in
``evidence/terminal-disposition.json``. Typed closure receipts identify the
native and viewer incarnations and report ``process_exited=true``; inherited
display helpers were not stopped. The released brief also contained a literal
missing-file diagnostic, recorded in ``released-bounds.json``. Retained scope
came from the authorized same-author predecessor, not sibling analysis answers.
These operational defects remain distinct from qualified process geometry.
