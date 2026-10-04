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
decoding, not a guessed __file__ namespace. The receiving owner subsequently
generated distinct synthetic inputs and exercised this packet as recorded below.

Planck received the complete candidate before669 merge with published official
ObjectState1.2. Target05/main9b6 lacks669 and is not its installed acceptance;
it remains the separate663 recipe receiving. No second client, overlay or
scientific hotpatch was started here.

Whole installed and public receiving: PASS
----------------------------------------

Original ordinary receiving06 wheel/target source is exactly
cf10bb670a3c0e0e264e3d0641872669e38beaa8. Wheel SHA256
d6a28b462348ad685db128dfa42cfca8e72a3979952d5e96d520df0eee980ff3;
original byte qualification admits912 RECORD members,812 tracked source members,
789 Python files and13 skill files. Official ObjectState1.2.0 and existing
qualified dependencies were reused; no selective installed overlay.

Original public client73939/MCP575160 and native600635/create1791148433.08 at
TCP6012/ACK7012 used normal preparation, original CPPipe import and two worker
threads. Compilation job1 and execution job2
498531a7-5b1b-4e2c-8d88-b8203ee5a34a completed/errors[]; native execution elapsed
.5599097s. Default automatic publication remained ON, viewer streaming OFF.

Both public saved12x15 uint16 label images match every original input pixel
(360 total). Both canonical measurement tables and public CSV previews join
object_label2 to Area6 and7 to Area20. Each well's public site/channel/Z/time,
source provenance and .5/.5micrometer calibration are preserved. Original
values01.json require_valid_observation passes. The exact installed-origin
verifier completed terminal0,3.91s/298120KiB/Swap0. This proves the registered
parallel multiwell saved-result path, not biological accuracy or exact race
overlap; the source lifecycle control separately exercises pending publication.

Typed close of the original native handle returned request_attempted,
acknowledged, endpoint_terminated, process_exited and succeeded TRUE/errors[].
Native/MCP independently absent; ports6012/7012/6013/7013 down and original scope
inactive/dead. Client EOF terminal2 retains two known pre-dispatch CLI
argument/discovery negatives, not shutdown failure or UNKNOWN recovery. Original
journals remain unchanged;94 was returned to Dewey with helpers untouched.

Durable original receiving root:
engineering-pre-first-routing-20261004/receiving06/public94-attempt01 under the
issue-batch root. ACTUAL-RECEIVING.rst, verify-public01.py/log,
RECEIVING-FREEZE.sha256 and original ENGINEERING669_94/author-workspace/output/
runtime/mcp.stdin/stdout/timing retain the entire public journey. Canonical
VALUES remains output/values01.json, not a fabricated JSON mirror. A separate
public receiving archive empty-step-publication-668-public01.tar.gz preserves
original reply/verifier/closure and whole qualification bytes alongside the
unchanged source archive. SHA256
c8a1b0e08b49fd605f6d1cf477e4f679980e1e6c50c34faf26bac46b08f9866e.

Fresh main18886f2000a0b47a30dadc7446267a50786fab2f has no changes in either
writer owner or either affected test relative to integrated maina3d. Its
separately qualified compiler/source-domain changes are not claimed as receiving06
bytes.669 production remains byte-identical to source-qualified9327 and actual
receivingcf10bb.676's aggregate-plane fix is separate and was NOT installed here;
663's representative3D compile remains separate and unverified. No scientist
bundle, report or biological claim is changed by this receiving.

Original detailed receiving triage is retained at engineering620/
BBBC007-EMPTY-STEP-PUBLICATION-TRIAGE-20261004.rst under the issue-batch root.
The independent aggregate viewer checkpoint failure remains Dewey's routing
scope. This PR does not change a viewer, frozen author bundle or science result.
