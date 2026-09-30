## Working source checkpoint for #251

Adds explicit typed owned-runtime bootstrap and read-only handle observation
through existing declaration-derived MCP/CLI and RuntimeServerService. Extends
the canonical native client startup owner, never `connect()` attach/replacement.
Native launch plan path admission precedes spawn; returned PID+creation-time
handle survives pending/uncertain observation. Startup does not warm catalogues
or submit source. First-use/custom guidance is coherent and QA/bounds preserved.

Paired dependency drafts: [ZMQRuntime9](https://github.com/OpenHCSDev/ZMQRuntime/pull/9)
exclusive startup/process identity, and [metaclass-registry1](https://github.com/OpenHCSDev/metaclass-registry/pull/1)
non-creating cache path projection at448cdf0. Exact gitlinks are committed.
Parent remains integration/install/live owner; frozen source/skill/runtime untouched.

Current source evidence: **136 passed, 2 actual MCP cases deselected, 10.64s, exit0**,
whole process14.18s/432464KiB RSS. Dependency rollback/close shard:45 passed,
0.40s, process3.68s/362564KiB RSS. Earlier123-pass and fixture failures retained.
Verified source imports and focused nested handle/path/foreign/uncertainty/native
readiness/declaration projection plus unchanged complete QA/context bounds.
No native/MCP/GUI/JVM was launched. No installed/live/performance proof claimed.
Receipt, actual pattern review and focused census:
[runtime_bootstrap_20260930.md](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930.md).

Source hardening includes both-address pre-bind reservations, post-spawn
uncertainty handles, expired-deadline no-spawn, real offline CLI projection and
authoring/core exposure. Normally integrated current main295e0ee81.
Exact dependency pins: ZMQ28d9ed6a0121ebb524ae37fd97de5355308bda7f and metaclass-registry448cdf07.
Earlier startup scoped census: no string/type dispatch/arms, raw-key, codec or foreign
absence-probe growth. Native reservation JSON decode/uncertainty catch/long
startup method are reviewed leads, not a global clean claim. Close continuation
also has no growth in those candidate classes; its native optional-state checks
and one genuine raw identity shape check are inspected boundaries, not zero debt.

### Reviewed no-child reservation leak correction

Parent's9a93bbe reproducer proved expiry immediately after both provisional
invoker reservations: zero spawn calls, but fresh independent startup remained
blocked by the live invoker. Original reproducer/receipt preserved, not replayed.
The canonical client now rolls back only publication/deadline/cancellation before
spawn, while both original locks are held. The transport owner decodes through
startup_owner and releases only exact ProcessIdentity matches by truncating the
existing inode. Unknown/changed/child records remain; spawn exceptions and failed
child publication do not roll back or automatically replay any operation.
Thirteen new provider-free cases cover that boundary, both locks/inodes,
partial records, second publication failure and post-spawn uncertainty.
[Actual receipt](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/pre-spawn-rollback/checkpoint.md).
Focused IMPL-13/IDEN-8/BOUND-2 owner review; no new launcher/store/codec/timeout.
No native/MCP/GUI/Java was launched and installed source/skill remain immutable.

Prior packaged R0 ratchet at78b5f9 vsbd1 failed (exit1,14.27s/86092KiB) on
GodClassExcess RuntimeServerService +15 and ZMQExecutionClient +32. Original JSON
and resource receipt retained. This source correction does not claim a passing
own-PR ratchet/global audit or fix that separate structural remainder.

### Exact owned close (parent-reported5993 lifecycle defect)

Adds typed `openhcs_close_owned_runtime` on the existing RuntimeServerService
and capability declaration owners. Actual native lock/socket write admission
precedes lifecycle dispatch. Both existing endpoint reservations must prove the
retained bootstrap child. FORCE sends at most one incarnation-bound request;
the native handler admits its identity before worker mutation, then the canonical
ProcessIdentity owner performs bounded TERM/KILL/wait within the original budget.
GRACEFUL clears workers and intentionally retains the server.

EndpointShutdownResult separates wire attempt/acknowledgement, listener cessation,
and exact process exit: FORCE cannot claim local identified completion from
lost listeners alone. Unknown/missing outcomes preserve the original handle;
read-only reconciliation uses existing observation, never shutdown replay.
Stale IPC material is removed only through its existing declaration-owned proof.
No new lifecycle registry, supervisor, string action bag or timeout expansion.
Bundled how-to and declaration-derived first-use pointer are updated; installed
managed skill remains frozen. Parent retains the original PID2052959 /
creation-time1790731598.48 cleanup and its ledger; worker did not contact/replay it.

Remaining: paired review, cross-process native endpoint-pair/uncertainty evidence,
released serial slot for full synthetic startup -> prep -> registration ->
compile/execute -> supported owned cleanup, then parent installed entrypoint
acceptance. References #251; **not Closes** pending actual acceptance.
