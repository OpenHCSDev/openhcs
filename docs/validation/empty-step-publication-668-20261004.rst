Empty step publication and completed-directory reconciliation
============================================================

Singer owns issue668's publication lifecycle correction. Frozen receiving03 and
the original BBBC007 jobs remain unchanged. Shared-hunk coordination is public
at658 comment5984001511; parent checked the same current rosters and explicitly
released this scoped writer correction without an acknowledgement hold.
Root658/661 subsequently merged into main9b6e69fb52165fcaea2f4b390202f4046f332932;
both writer files are unchanged across that integration. This branch received
that main normally, preserving eight foreign gitlinks and all retained evidence.

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
projection owner). This trace is not global NRA/R1 or executed behavior.

Implemented owner and complete migration
---------------------------------------

Only OpenHCSMetadataTarget in function_outputs.py changes in production.
produced_projection_entries now takes a real CompiledStepPlan and returns a
typed VirtualWorkspaceSourceProjectionEntries for every step, including an empty
non-image update. The owning write lifecycle selectsNone ONLY when its actual
produced_plan isNone. Thus step cardinality no longer decides publication phase.
write_for_step's merge-only path checks the typed entries directly and retains
its existing no-write behavior for an empty update. All inherited target leaves
use this ancestor; no consumer roster, new state store, wrapper or type switch
was added. Both production projection callers are migrated in the same batch.
The obsolete nullable step projection and its empty=None decision are deleted.

AtomicMetadataWriter and VirtualWorkspaceSourceProjectionEntries are unchanged,
including strict final missing-address admission, pruning and retained record
validation. SourceProjectionSet's separate nonempty workspace invariant remains
unchanged: empty updates use the existing entries value, not an empty dataset.
No dependency, installed package or scientific declaration is modified.

Original audit Package admission at pre-edit integration7aecc7ed05c5c39141c056ef2b17e81fb374a195
parsed700 production,705 tests,89 scripts,156 benchmark modules. Exact declared
PolyStore89deeef3662eabb11bc520fad9acd976698636bd and
metaclass-registry393a7e03003cdc56df9013f932ed4f26e632d77a source keepers add63/6
modules. Parse omissions0. Selected full ASTs include12 production publication,
projection, inventory and orchestrator owners;25 test modules;1 script;2
benchmark modules. All dependency ASTs were retained, not product-imported.
Original publication668-family-before01.jsonl/stderr are in engineering620.
Terminal0,37.90s,559536KiB RSS,Swap0; no512MiB compliance claim is made for this
actual AST pass. Its original source facts show declarations, imports, fields,
calls, conditions, registry hooks and target inheritance. Dynamic registry
resolution is tested separately; this is static family evidence, not global R1.

Final behavioral controls are added only after this source decision: a saved
measurement CSV sharing a directory with an as-yet-unpublished image must publish
an empty step update, preserve bytes, still fail actual final reconciliation,
then reconcile after the original typed producer publication. The existing
independent target declaration composes its real cooperative audit/image/result
capabilities, exercises repeated step publication with a pending image and the
strict final error, without generic consumer changes. Its original public
result-inventory assertion is retained. The old internal empty=None expectation
is migrated to the newly explicit empty typed update, not silently dropped.

Final controls must cover image producer updates, empty measurement-only step
updates while a different saved image is not yet published, later publication,
strict completed reconciliation and genuinely missing producer rejection.
Exercise an independent declaration/cooperative hook through generic discovery,
without adding consumer edits. Then qualify ordinary installed registered and
public parallel multiwell saved-label/measurement execution on a NEW synthetic
input, preserving exact pixels/addresses/calibration and all original negatives.
Source controls have not yet run at this implementation checkpoint. Ordinary
whole installed/public multiwell acceptance remains separate and required.

Original detailed receiving triage is retained at engineering620/
BBBC007-EMPTY-STEP-PUBLICATION-TRIAGE-20261004.rst under the issue-batch root.
The independent aggregate viewer checkpoint failure remains Dewey's routing
scope. This PR does not change a viewer, frozen author bundle or science result.
