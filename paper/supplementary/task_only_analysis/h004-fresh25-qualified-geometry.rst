Fresh public-neurite repeat: support recovery versus rooted geometry
===================================================================

H004_FRESH25_ROTATION_89 completed task-only analysis of a released paired
800-by-800 uint8 field using receiving25, MCP and isolated display :89.
W1 has the provisional ProcessBody role and W2 NuclearAnchor; stain identity
and phenotype are not independently established. This is not the personal
DAPI/FITC acquisition, and relative spacing does not supply physical calibration.
No reference labels or held-out images were accessed.

Attempted trajectory and endpoint
--------------------------------

The first scientific attempt retained 25 objects and 3,552.6807 pixels of
conditional trace length. Matched nuclear inspection identified false splits.
An incompatible physical-calibration-dependent inspector was refused before
execution; no spacing was invented. Increasing nuclear minimum width to 16
pixels then retained eight soma-supported objects and 3,914.0138 pixels of
trace geometry. These revisions are autonomous within-run repairs, not
independent replicates.

Selected attempt04 retains eight soma envelopes totalling 8,475 square pixels,
with 95 graph edges summing to 4,432.0991 pixels. The final attempted pipeline
is attempt05, separately frozen and rejected as an overall improvement: it
retains the same eight soma masks but 212 edges and 4,715.6748 pixels of trace.
Selected04 must not be substituted for last05 when reporting a last-attempt
endpoint. Its useful geometry is a qualified checkpoint, not complete arbors
or known biological ownership at overlaps.

Selected PipelineDocument SHA256::

  1229aa71edcb3d67a80339d090e66a588be8f1c7c12044a1b0ca12e44dbdf058

Last-attempt PipelineDocument SHA256::

  71d6b3a7121d9de4a720e3017e3080b5d79813262d9700a4e5e0234a8663c09d

The registered pixel MetaXpress function consumes the paired raw inputs.
Selected parameters include nuclear widths 16--40 pixels and contrast 15,
soma maximum width 50, minimum area 60, contrast 12 and inscribed diameter 6;
process maximum width 6, contrast 3, candidate correction 0.2 and high-seed
correction 0.5. There is no separate input-normalisation or smoothing producer.
The engine's rescaled enhanced response is not evidence that a separate
requested input-normalisation operation occurred.

Independent review and stage-local explanation
---------------------------------------------

A separate reviewer personally opened 24 original MCP PNGs: matched raw/result/
combined triplets at full-field, faint, crossing and background viewports for
both04 and05, using upper display limit 100. This is not independent review of
all 78 author captures for these candidates. The viewport called background
contains genuine processes and is not a wholly empty negative control.
The review supports useful soma coverage and partial raw-supported processes
in04, with remaining weak-path omissions.05 recovers some faint endpoints but
loses a long visible branch and shortens a crossing-region branch.

Only candidate correction changes04 to05, from 0.2 to 0.1. Saved enhanced and
local responses, nuclear/body labels and secondary ownership are identical.
Threshold, retained and candidate supports are supersets. At native (y,x)
coordinates (182,478), (204,452) and (220,432), the lost branch survives both
enhanced/local response and admission, but becomes unrooted in05. This observed
loss is downstream of preprocessing and threshold admission. At (250,530),
by contrast,05 admits a faint point rejected by04: both mechanisms coexist.

The retained04 owner6 graph chain extends from (262,379) through (230,405),
(220,432), (204,452) to (182,478).05 has no corresponding distal chain; an
owner4 edge ends near (230,404). Owner6 length falls from 771.23 to 554.03 pixels
despite unchanged soma area. Thus the higher total trace length does not prove
better coverage. Rooted-geometry decisions require investigation under issue
1001; these artifacts do not establish a particular routine defect, physical
disconnection or true neuron ownership. Nonzero feature response at these
witnesses does not prove feature preservation everywhere.

A subsequent engineering reconstruction called the original medial-axis,
topology, secondary-adoption, repair and publication owners on saved candidate,
local-response, secondary and body stages. It reproduced both complete saved
thin-trace arrays with zero differing pixels, without rerunning enhancement,
thresholding, body/nuclear detection or a scientific pipeline. Both medial
axes retain the branch. Initial topology assigns it owner6 in04 and owner4
in05; secondary adoption leaves these positive assignments unchanged. Signal
repair then removes the distal05 chain before final graph publication.
This identifies the loss stage, not a justified biological owner or a proven
defective routine: saved secondary support assigns owner2 and connects to soma2,
whereas the05 candidate component connects somas4/6/8. Restoring owner6 solely
because04 used it would therefore not establish correctness. The root/transition
and recovery investigation remains separate from this frozen scientific result.
The reconstruction source SHA256 is
``761dc03bf62da8dd2dd533f48bfae6c6551994bd959f8d50244c9b5c4a894204``;
its ownership receipt, probe and original logs are retained under
``/home/ts/wt/openhcs-issue-batch-20260929/engineering1001`` and issue1001.

Custody and operational limits
------------------------------

The parent rechecked all four source/staging records, 266 canonical payloads,
773 control records and 150 captures: 1,193 records covering 203,727,681 bytes,
with no size/hash failures. Both exact pipeline hashes and all four declared
journal prefixes also matched. Counts include overlapping manifest scopes,
not exclusive disk usage; prefix matches do not establish later full-journal
identity. The reviewer separately reconciled eight-row tables and edge sums
and found identical04/05 body/nuclear TIFFs. Original freezes were not rewritten.

The author's MCP saved-label reopening failed because it lacked an exact
source receipt. Independent offline TIFF reading does not repair that failed
live receipt. Reopening graph/body/nuclear ROI archives succeeded. Simultaneous
paired-channel colour display showed only W1; both channels were inspected
separately, without claiming successful paired composition. Exact owned native
and viewer shutdown receipts report exit and endpoint termination; client
exit code 2 remains a separate operational limitation.

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h004-fresh25-89-after-h003-20261006/H004_FRESH25_ROTATION_89/author-workspace/output

Canonical payload root::

  /run/media/ts/hdd/openhcs-science/next-h004-fresh25-89-after-h003-20261006/H004_FRESH25_ROTATION_89

The independent stage review is retained in H004-FRESH25-FINAL-QA.md under
/home/ts/.cache/agent-scratch/regression-cause-audit-20261006. The original
report.md, freeze-manifest.json, qa-index.json and attempt04/05 records retain
the trajectory, original capture custody and selected-versus-last distinction.
