Fresh H001 repeat: qualified bright-object segmentation
======================================================

H001_FRESH25_ROTATION_94 completed a task-only autonomous analysis using the
receiving25 package and MCP on isolated display :94. Its final selected and
attempted candidate is REPAIR02. No reference answer or held-out image was
used. Acceptance is for useful bright-object segmentation, not verified cell
identity, an exact biological census or calibrated morphology.

Method and attempted trajectory
-------------------------------

The released image is one 254-by-256 float32 plane with range 8--248. Its SHA256
is ``26403a7c2a11921535499ff86798b73e09b8ac5786329bce8fa4a57fd9933fee``.
The complete final PipelineDocument SHA256 is
``ec599bef414f12d068dfc3f727219cfc69568a9f88213d2fe02a3aeb3e73a3b2``.
Detection uses raw/248, global two-class Otsu, threshold smoothing 1, SHAPE
markers and watershed, marker suppression 15 pixels, diameter admission
6--40 pixels, border inclusion and post-declump hole filling. The effective
threshold is 0.4839969753 in the detection image, approximately 120.03 raw
units. Dividing by 248 is an analytical transform, not an acquisition bit-depth
claim. Object size/shape measurements and native instance labels are exported.

Two known binding/axis compile failures precede the first scientific execution.
FIRST retains 66 objects. REPAIR01 changes to intensity markers with smoothing
5; the author rejects wedge-like fragmentation and support loss. REPAIR02
returns to shape markers with higher suppression and retains 62 objects.
The parent independently established byte-identical positive foreground between
FIRST and REPAIR02: this repair changes partitions, not total admitted area.
The count change is neither a biological confidence interval nor evidence of
ground-truth accuracy.

Independent review and remaining uncertainty
-------------------------------------------

The parent personally opened 14 original native MCP PNGs: final raw/result/
combined triplets at NW (y,x)=(65,65), centre (163,133), SW (213,40) and the
full field (126.5,127.5), with window 8--176 and gamma 1; plus NW and centre
raw-only views at 8--248. Local zoom is 4 and full-field zoom 1.72.
The saved QA manifest associates these images with the declared visible routes,
camera and numeric display windows. This is selected distributed review, not
independent inspection of all 72 author trial captures.

Ordinary bright compact bodies have useful coverage, and inter-body background
is largely excluded. The centre contains a long lobed region represented by one
label, which may merge two biological objects; other lobed forms retain two
partitions and may be false splits. Small unlabelled foci remain plausible
misses or debris. The wider raw window retains internal texture obscured by
saturated highlights in the narrower display. Neither view independently
resolves every touching object's identity in this single-channel acquisition.
The parent did not independently review FIRST's border partition in a matched
bitmap; its reported repair remains author evidence rather than a separately
confirmed visual benefit.

The saved uint16 label TIFF has IDs 1--62 and 62 unique CSV rows with matching
identity sets. The parent independently reconciled every exported area with its
label pixel count: 22,539 foreground pixels, individual areas 30--912 pixels.
No verified spacing, manual cell count or physical-area claim is available.

Freeze and runtime disposition
------------------------------

All 135 declared scientific artifacts matched their recorded sizes and hashes,
covering 19,718,634 manifest bytes. All 480 control files also matched, covering
12,754,006 bytes. The scientific freeze's MCP journal entry is an exact
12,518,286-byte prefix; its match is not a whole-journal identity claim. The
three closed MCP journals in CLEANUP.json independently matched their full
recorded sizes and hashes. These scopes overlap and are not exclusive storage
accounting. Original reports and manifests were preserved.

Typed native/viewer shutdown receipts report process_exited and endpoint
termination; independent process checks found the original author, MCP, native
and viewer handles absent. Client exit code 2 is retained separately from
completed scientific execution and qualified biological review. No uncertain
operation was replayed. This repeat does not establish effectiveness of later
skill changes that were absent from its pinned package.

Control root::

  /home/ts/wt/openhcs-issue-batch-20260929/next-h001-fresh25-94-after-retina-20261006/H001_FRESH25_ROTATION_94/author-workspace/output

Canonical payload root::

  /run/media/ts/hdd/openhcs-science/next-h001-fresh25-94-after-retina-20261006/H001_FRESH25_ROTATION_94

REPORT.md, FROZEN_MANIFEST.json, CONTROL_MANIFEST.json, qa-manifest.json,
label-reconciliation.json and CLEANUP.json retain the original declarations,
trial trajectory, capture custody, quantitative reconciliation and closure.
