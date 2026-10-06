Fresh paired-field neurite analysis: useful local recovery
========================================================

H004_FRESH20_95 independently completed four scientific candidates on one
released 800-by-800 paired uint8 field through the packaged skill and recorded
MCP client. There was no reference-answer feedback, held-out image or separate
whole no-object acquisition. The soma/process-rich and nuclear-like channel
assignments were inferred from matched morphology; stain identity and physical
calibration were not independently established. All measurements below use
pixels, not micrometres. This is development evidence, not unseen generalization.

The author traced missing faint paths to the adaptive candidate gate despite
measured local support. Three repairs reduced that gate while retaining the
soma, nuclear, local-contrast and width settings. The final bottom-path witness
retained support through all 20 sampled rows. Major trunks followed raw signal,
but increasing sensitivity also added uncertain short twigs and changed
ownership near crossings. Thus soma localization and reviewed local geometry
are useful; complete extent and neuron-specific branch totals are unsupported.

Threshold sensitivity, not biological branch counts
---------------------------------------------------

The saved tables contain eight distinct soma IDs in every candidate, with
summed approximate mask area 8692 pixels squared. Algorithm-defined graph
length and branch counts are retained to expose sensitivity, not as accepted
biological endpoints.

.. csv-table:: Original completed candidates on the same paired field
   :header: "Candidate", "Candidate factor", "Somas", "Area (px2)", "Graph length (px)", "Processes", "Branches"

   FIRST,0.35,8,8692,4085.1925,25,12
   repair01,0.20,8,8692,4789.8758,28,43
   repair02,0.08,8,8692,6077.4801,35,129
   repair03,0.04,8,8692,7787.9098,50,234

The final attempted pipeline is repair03; repair01 is separately retained as
the author's preferred conservative major-trunk predecessor. These are not
interchangeable selections. No manual matching score, sensitivity, specificity
or confidence interval is inferred from eight visible soma-like structures.
The graph diagnostics also retain representation differences: 118 dropped
trace pixels and 6479 published versus 6473 final-owned trace pixels. Counts
from different representations must not be silently equated.

Freeze, review and reproduction
------------------------------

Final pipeline SHA256:
d927ff7cde9b55b1757583906a24639598b95b3855b56b4787c5d1ec0fb3e72a.
The receiving20 installation is OpenHCS 0.8.7, with its recorded earlier skill
baseline; later merged skill lessons are not credited to this author.
The complete PipelineDocument retains explicit source ordering, source aliases,
pixel geometry and each destination. Reproduction requires a new owned runtime,
ordinary compile/execute observations and the original recorded source inputs;
closed or uncertain operations must not be replayed.

Canonical payload root:
/run/media/ts/hdd/openhcs-science/next-h004-retina-fresh20-95-96-20261005/H004_FRESH20_95.
Author source and original control records:
/home/ts/wt/openhcs-issue-batch-20260929/next-h004-retina-fresh20-95-96-20261005/H004_FRESH20_95/author-workspace/output.
REPORT.rst, REPRODUCE.rst, FINAL-ATTEMPT.json and each original proposal/review
remain retained there; runtime exports are ordinary typed observations, not an
alternate analysis engine.

The coordinator independently verified all 181 payload sizes/hashes
(144627936 bytes) and all 61 indexed screenshot sizes/hashes (9349589 bytes).
PAYLOAD-MANIFEST SHA256:
5aec49033aa112a958d6fc431b3734b98b9e10f6cdbc308d424495f05367fdb8.
QA-INDEX SHA256:
be4368ce33df338f7791587e2f3b7427594516d0e299f21394ba1d50310d6964.
Independent summing of the eight final cell rows reproduced area 8692,
graph length 7787.909806465099, 50 processes and 234 branches. This verifies
persisted computational outputs, not independently remeasured biological truth.

The coordinator personally opened final full-field and bottom-detail
raw/result-only/combined triplets, in addition to predecessor triplets. The
final views support ordinary soma localization, raw-aligned major trunks and
some recovered side paths; short near-track branches remain ambiguous.
Capture identities and declared windows are in QA-INDEX. The final full set
uses center 399.5,399.5, zoom 0.49875 and raw window 0..100; the bottom set
uses center 680,365, zoom 2 and raw window 0..12. Those index declarations
were not separately reconciled with every capture-time viewer-state receipt.

Exact viewer, native and MCP exits were independently verified. Original
client exit 2 remains distinct from the four completed scientific executions.
The author's original CONTROL-MANIFEST labelled its native rollout complete
before the final message was appended. All 324 recorded byte-prefix hashes
match, but that grown entry is prefix evidence, not an immutable full-file
seal. The original manifest is unchanged; the separate owner-published
OWNER-H00495-TERMINAL-CLOSED-JOURNALS.sha256 passes all six true post-writer
files. No original input or scientific execution was replayed.
