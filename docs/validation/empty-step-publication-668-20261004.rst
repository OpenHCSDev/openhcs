Empty step publication and completed-directory reconciliation
============================================================

Singer owns issue668's publication lifecycle correction. Frozen receiving03 and
the original BBBC007 jobs remain unchanged. Root658's active provider/graph work
and661's consumed-output recording are separate; their published file rosters do
not claim function_outputs.py or virtual_workspace_metadata.py. Precise shared
hunk coordination is public at658 comment5984001511; no shared-file release is
claimed by this initial checkpoint.

Determining source
------------------

Base/main7e7e9f44afb1f683dbe87c39727f8899a94ed5cf contains the same atomic metadata
writer as the frozen receiving03 target (SHA256
1a40a500e40e848496405b274675a7977809078f6069f00b731d3e0f09c0686d).
The original log at next-bbbc00788-after651-20261004/BBBC007_FRESH651_88/
author-workspace/output/runtime/data/openhcs/logs/
openhcs_zmq_server_port_6020_1791141656418933168.log2395-2430 reports missing typed
address results/A04_wDNA_nucleus_labels_step0.labels.tif during the Nuclear
geometry measurement step. This is not626's repaired storage-extension conflict.

The ancestor OpenHCSMetadataTarget.produced_projection_entries returnsNone for
both a real step with zero image projections and completed-plate reconciliation
with planNone. AtomicMetadataWriter interprets thatNone as final directory
reconciliation and enforces its strict complete-inventory guard too early.
The original per-step caller supplies produced_plan=plan. Main retains this
decision chain. Whether the absent A04 address is temporary or permanent is
separate and remains unproved by this source trace.

Owner correction and acceptance
------------------------------

The existing typed VirtualWorkspaceSourceProjectionEntries already represents
an empty producer update. A real step must retain that typed update even when
its projection sequence is empty; only actual final reconciliation may select
the no-step state. Derive phase from the existing target's publication lifecycle,
not file count, filename guesses, an extra flag/store or consumer type switches.
Keep completed-plate missing-address validation and pruning unchanged.

Before edits, trace all inherited target declarations, step/final writers,
projection admission/serialization, registry discovery and atomic update users
through existing audit AST tooling. Applicable catalog lead: IDEN-1 (None
answers two different lifecycle questions); BOUND-2 (reuse the original typed
projection owner). This initial trace is not global NRA/R1 or executed behavior.

Final controls must cover image producer updates, empty measurement-only step
updates while a different saved image is not yet published, later publication,
strict completed reconciliation and genuinely missing producer rejection.
Exercise an independent declaration/cooperative hook through generic discovery,
without adding consumer edits. Then qualify ordinary installed registered and
public parallel multiwell saved-label/measurement execution on a NEW synthetic
input, preserving exact pixels/addresses/calibration and all original negatives.
No source/installed/public acceptance is claimed by this initial checkpoint.

Original detailed receiving triage is retained at engineering620/
BBBC007-EMPTY-STEP-PUBLICATION-TRIAGE-20261004.rst under the issue-batch root.
The independent aggregate viewer checkpoint failure remains Dewey's routing
scope. This PR does not change a viewer, frozen author bundle or science result.
