Issue308 viewer reset transition ownership
=========================================

Owner: independent issue308 contributor; parent owns integration and live MCP
acceptance after Russell's terminal release of validation.lock. Base production
d1c6ab72ca252ea93656eeaaf84d34b81abd8317. Frozen issue302 tree is read-only.

Scratch owner/purpose/path: issue308 contributor, bounded pytest caches only,
/home/ts/.cache/agent-scratch/viewer-reset-lifecycle-308-20260930, maximum256MiB.
Retained failing and successful logs live alongside this receipt, not scratch.
Single CPU/thread, existing Python3.12, offscreen Qt; estimated runtime512MiB.
No scientific inputs, server, catalog, JVM, GPU, display91 or provider calls.

Resource preflight: available RAM14.6GiB; check reports warnings for home free
13.9GiB and swap8.7GiB. User's actual-footprint policy is warning-only20GiB.
No parallel agents or tests. Measure actual maximum RSS with time -v.

Baseline-valid-transitions.log confirms all three target failures on unchanged
production. Initial original-reproducer.log and baseline-transitions.log retain
harness mistakes (wrong route suffix, zero ROI label, inconsistent config),
not product failures. The valid combined baseline reached570560KiB (557MiB),
above512MiB. Stopped tests and reconciled: disable optional Numba JIT for tiny
native model inputs and shard transitions in separate processes. No assertions
or native layer implementation are replaced. Resume only within the budget.

Ownership and source witnesses
------------------------------

Base NapariComponentAwareDisplayCoordinator.display/_upsert_item overwrites
component_groups before schedule_layer_update renders. Base
NapariShapesLayerDisplayWork.advance registers its first hidden chunk via
NapariLayerUpdateAuthority.create_or_update. Base clear_accumulated_stream_state
prunes component_values without reconcile_mounted_axis_projections. See the
three native assertion failures in baseline-valid-transitions.log.

IDEN-1: mounted presence incorrectly meant a completed native generation.
IDEN-5: retained item provenance and native pixels could describe different
generations. IMPL-12/13: clear bypassed existing shared-axis reconciliation.
AGENT-4/6: extend pending-update, display-request, native mount and domain
declarations; do not add behavior to another server coordinator or move it to a
new facade. Pending updates now carry accepted items. Component groups contain
only completed mounted payloads. Shapes work owns an unmounted native candidate;
the existing layer update authority mounts it on completion. Pure pending
projection does not alter mounted domains. Mounted dimension state retains the
original display policy needed for source-backed rematerialization after prune.

New-case edit comparison: a new chunked native handler previously needed its
own rollback bookkeeping plus changes to clear and native route retention.
Now it implements existing handler-owned work and publishes completion via
the existing display request (one handler declaration); clear has no handler
or origin roster. Another component axis already belonged to the component
declaration/projector; before this fix reset additionally needed a repair path.
Now pruning uses existing projection for every mounted route, with no new
axis-specific edits. This is lifecycle factoring, not module relocation.

No durable format changed. Pending items/native candidates are runtime residue
discarded at reset; mounted payloads/domains and component names survive. No
metadata/runtime217/microscope files or selection policy are changed. Production
scope: napari_viewer_server.py, napari_streaming_handlers.py,
viewer_component_system.py. Parent owns integration; contributor owns fixes.

Source proof checkpoint: six Qt/native-model transitions pass in5.03s,
448260KiB peak. Shapes continuation tests exercise actual native layer classes
and native selection binding, not a canvas or ROI dock. Image/clear owner shard
seven pass; original broader owner run exceeds memory and is not a pass. Owner
test migration and original packaged ratchet/R1 evidence remain in progress.
The full application/installed/MCP journey is deliberately not claimed.
Live dependency remains Russell terminal release of validation.lock, then
parent-owned affected acceptance; Refs #308, not a closure claim.

Final source checkpoint
-----------------------

Eight native Qt/model transitions passed: queued image replacement with both
replace policies, initial partial Shapes cancellation, Shapes replacement
cancellation, full Shapes completion/publication, shared-axis translation
prune, interior-axis extent prune/rematerialization, deleted queued route
non-resurrection. Settled item-list identity and physical scale survive reset;
prune rematerialization preserves the original display policy and native layer
selection through the existing native mount owner. No extra classifier/store.

Focused owner shards passed: image/clear7, native mount/shared-axis7,
coordinator/debounce/settlement9, Shapes/Points/mount/chunks5, native4097-member
Shapes1 (three work units, full features/colors). These counts overlap and do
not imply a full-suite pass. Largest successful shard463428KiB, below512MiB.
The former fake Shapes-chunk implementation is deleted from the test; its
behavioral assertions now exercise a real unmounted native candidate, exact
chunk sizes, feature/color completion, registration before binding and reveal.

Full owner-file attempts are not passes: the unsharded run exceeded512MiB;
the later Qt-enabled run exited nonzero in pre-existing entrypoint/window tests
after73 test indicators, maximum526752KiB. No more broad UI runs were attempted.
Native-presentation test collection is independently blocked by the absent
openhcs.core._tabular_native compiled extension. No build, install, native
server, GL canvas or download was used to work around it. Its direct-handler
fixture now supplies the actual display pipeline required by publication.

Full R1/NRA dependency context is not certified: recorded arraybridge object
409b1e0831f815fa9ef91d4ecc04989f9fbb89c5 is absent from the frozen tree's
shared Git object store. The source bootstrap uses only the four required
initialized own dependencies cloned with shared/read-only object references:
PolyStore dc341739, metaclass-registry448cdf07, zmqruntime9e11f6f,
pyqt-reactive3437d1c6. No other submodule or other worktree was modified.
Parent must supply the recorded dependency context for its full R1 gate.

Original structural ratchet source is authenticated from Git archive of CI pin
3b03785f45df2ef5dc62ba6aed99294192ecbb01; no detector definitions are altered.
Python3.12 cannot load that original package because InputDocument is an
unevaluated-forward annotation under its Python3.14 semantics. The original
guard therefore uses the already-present Python3.14.2, separate from all
Python3.12 source tests. First measurement at0b56212d7:5140 actual metrics;
sole positive StringSubscript+2. Both witnesses were unnecessary quotes on
future-deferred NapariPendingLayerUpdate item annotations, now removed.
Original before/after metrics and resource reports are retained.

No installed/live readiness claim. Parent owns affected MCP acceptance after
Russell releases validation.lock, plus its full R1/source environment gate.
Draft PR309 remains Refs #308 and must not close it before that acceptance.

Final authenticated structural guard: production4fae0e4c31c1ab13b0845766757d44e4a41ef1e4
against pinned merged main;5140 actual original metrics, zero positive deltas,
exit0, peak86988KiB. Scope is the three changed production paths plus original
complete class inventories. This is a structural guard pass, not
full NRA/R1 or runtime proof. Final matrix:8 passed in5.14s, peak453108KiB.
Source/data/layout declarations remain with their original typed owners.

Retained raw original/final metric reports are losslessly compressed as
ratchet-first-314.json.gz and ratchet-final.json.gz. Plaintext duplicates are
removed; both the compressed artifacts and original Git history retain them.
Owned disposable scratch (5MiB pytest/formatter caches and authenticated audit
source extraction) is cleared after validation. All failure/success receipts,
inputs and originals remain in this persistent worktree and PR history.
