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

Before this correction, OpenHCSMetadataTarget.produced_projection_entries returnsNone for
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

The owning OpenHCSMetadataTarget in function_outputs.py carries the phase fix.
produced_projection_entries now takes a real CompiledStepPlan and returns a
typed VirtualWorkspaceSourceProjectionEntries for every step, including an empty
non-image update. The owning write lifecycle selectsNone ONLY when its actual
produced_plan isNone. Thus step cardinality no longer decides publication phase.
write_for_step's merge-only path asks the original admitted entries owner's
derived is_empty property and retains its existing no-write behavior for an
empty update. The property adds no state or alternative projection authority.
All inherited target leaves
use this ancestor; no consumer roster, new state store, wrapper or type switch
was added. Both production projection callers are migrated in the same batch.
The obsolete nullable step projection and its empty=None decision are deleted.

AtomicMetadataWriter is unchanged, including strict final missing-address
admission, pruning and retained record validation. The entries owner only adds
the cardinality query above. SourceProjectionSet's separate nonempty workspace invariant remains
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
Source qualification and receiving packet
----------------------------------------

Original plugin-free/provider-free source bootstrap, unchanged existing paired
interpreter and read-only tabular ABI: publication668-source-controls01 passed85
controls with33 explicit unrelated deselections, terminal0,11.35s,368572KiB RSS,
Swap0. This batch is pinned to production924605638; source metadata module origin
and the original borrowed native path are asserted. The tabular C++ source is
byte-identical to the already qualified626 build (SHA256
15acc82b8ab64268bd1ea4f83fa7a68f527bf317f002e9f39e15be321e03b28e).
No build/install, registry startup, native server, viewer or scientist ran.

The original R0 at924605638 measured all changed production files against main9b6
and found foreign_absence_probe+1 at the merge-only raw entries read. That receipt
is retained, not waived. The owning admitted entries type now exposes its own
derived cardinality; the caller asks that type rather than probing its raw map.
Production9327f3c096b2f990aac38d33adeb8f23c175bd25 changes exactly TWO production
files. Original R0-02 includes both: parse omissions0, all positive deltas0,
none_identity-1. The7 affected owner/strict-final/cooperative/late-plate controls
after this owner change pass, terminal0,4.72s,304788KiB RSS,Swap0;77 unrelated
tests are explicitly deselected. The unchanged85-case batch is not rerun.
Both raw warning receipts retain plugin-free pytest's two unknown asyncio
configuration-option warnings; these are not missing or failed controls.

Changed-owner AST after02 admits all176 core modules, omissions0, and retains the
two changed owners' complete trees,3.10s/155732KiB/Swap0. Other production and
declared dependency source closure is byte-unchanged and retains before01's
evidence. No global NRA/R1 or installed readiness is inferred.

Normal integration aa0079db8d8443cf32fbfe8b94f525e2de960f30 receives maina3d9a24d0
(including666's config schema/default separation). Both production files and
both affected test files are byte-unchanged from qualified9327f3c09. That new
upstream declaration/default change is separately qualified by its owner; this
receipt does not claim its new branch was tested here. Eight foreign gitlinks
remain unmodified in the commits.

Archive empty-step-publication-668-source01.tar.gz retains the original complete
ASTs, commands' stdout/stderr, both R0 receipts (including the positive first
result), source-only triage and receiving packet, byte-exact. SHA256
4741b9f721744f2b18e0ce724203eced28dbbf44b6089bcea7868cdb482acf88 (2.0MiB).
Loose original files remain under engineering620; no raw failures or evidence
were rewritten. Archived pytest whitespace does not pollute production/docs
diff checks.

The prepared distinct packet is engineering620/public668/{pipeline.py,
labels-and-measurements.cppipe,prepare_fixture.py,RECEIVING.rst}. It reuses the
accepted503 scalar04 nominal primary-image PLUS categorical-object-source
declarations, then registered UINT16 image publication and size/shape measurement
on wellsA01/A04 with two declared worker lanes. Default automatic publication
stays enabled. It has no invented source receipts, callable, alias or algorithm.
The source-only packet uses literal declared paths valid for normal public source
decoding, not a guessed __file__ namespace. Source data generation has not run.

Planck explicitly receives the NEXT complete candidate bundle before669 merge,
with now-published official ObjectState1.2. Target05/main9b6 lacks669 and is not
its installed acceptance; it remains the separate663 recipe receiving. Actual
installed registered and public parallel multiwell image/table/typed-address
acceptance remains pending through the existing sole builder/native lane owner.
No second client, overlay or scientific hotpatch has been started here.

Original detailed receiving triage is retained at engineering620/
BBBC007-EMPTY-STEP-PUBLICATION-TRIAGE-20261004.rst under the issue-batch root.
The independent aggregate viewer checkpoint failure remains Dewey's routing
scope. This PR does not change a viewer, frozen author bundle or science result.
