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
