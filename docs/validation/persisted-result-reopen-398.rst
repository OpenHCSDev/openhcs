Persisted result reopening: issue 398
====================================

Owner and boundary
------------------

Singer owns this source-only investigation on
``fix/persisted-result-reopen-20261001``, based on main ``49a95d8fb``.
Dalton owns the scientific pipeline; the parent owns installed acceptance.
No native process, installation, scientific array, or failed job is modified
or replayed by this investigation.

Original witness
----------------

The retained witness is
``neurite-development-skill383-20261001/output/ASSISTED-2-FAINT-PROCESS-QA-CHECKPOINT.rst``
under the parent's persistent issue-batch worktree. Candidate 1b intentionally
did not open a viewer after its original finalization failure. Consequently
there is no historical window-state receipt for these persisted images.

The native ``input_openhcs/openhcs_metadata.json`` nevertheless declares exact
workspace references, selected w2 source provenance, spatial metadata, and
source-artifact projections for the candidate mask and unrooted residual.
The public explicit-result inventory returns null source paths; explicit
image streaming refuses the absent historical receipt; sampling cannot find
the physical artifact in the inventory. Graph reopening separately refuses
missing native ROI source metadata. Those failures must not be bypassed with
invented snapshots, file-name inference, or a relaxed provenance guard.

Supported read-only control
---------------------------

A serial guarded source invocation of the real ``PlateInspectionService``
queried the native output root using ordinary automatic microscope detection,
image inventory, no previews, and a read-only path policy. It returned zero
images and ``plate_image_file_listing_failed``: multiple metadata
subdirectories exist but none is marked main. Runtime was 3.72 s, peak RSS
233288 KiB, exit 0, within a one-CPU/512 MiB/60 s scope. No viewer or subprocess
was allowed. This is source evidence, not installed acceptance.

Earlier import/constructor/wrong-microscope harness failures are retained
separately; they do not establish product defects. Original raw logs remain
in the owned ``persisted-result-reopen-20261001`` scratch directory pending
byte-exact archival with the completed source suite.

Ownership crossings
-------------------

PR394 owns runtime payload and materialization files. Its graph ROI renderer
currently constructs ROI content without the existing archive source-metadata
binding. This investigation has not edited that shared file. PR397 owns
selected-plane output declarations; no consumer axis workaround is permitted
here. Neither PR claims inspection/streaming services or native read-only
metadata projection. Issue398 links the original broader issue134.

Architecture and acceptance
---------------------------

Reuse the native metadata handler, virtual source-workspace projection,
inventory, original image loader/sampler, and ROI metadata codec. Shared
behavior stays with those owners; no parallel receipt schema, registry,
projection store, path-guessing loader, or consumer type roster is allowed.
Applicable audit patterns are BOUND-1/2, IDEN-1, and IMPL-4/12/13.

Required source acceptance is an ordinary public inventory/sample/reopen
journey from declared persisted metadata with a misleading image name and
more than one output branch, with no historical viewer receipt. Unbound
images and ROI archives must remain rejected. A new declaration must work
without changing generic consumers. Live installed acceptance remains with
the parent. This initial diagnostic receipt makes no readiness claim.
