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

**Current paired-pin checkpoint:** normally integrated OpenHCS main5a56ee5d5
(merged viewer159) at8bf3e2e0c; native67d41b6 contains recorded viewer2c68 and
native main2aa6d21c (viewer7, includes ACK3374). Records published nativePR9
**67d41b6**, production84b93a0, plus ArrayBridge409. Tests at source8bf3e2e0c:
**187 source casesPASS5.46s**, zero skips/deselections; process6.29s/259448KiB/exit0.
Includes original181 plus6 merged viewer-state controls. One corrected own stale
docstring: reservation publisher accepts provisional invoker OR child; no behavior
change. Native ratchet currentmain2aa->84b **PASS188 metrics/no positive deltas**,
client-3,4.48s/48772KiB/exit0. No native run/install/ABI copy. Parent installed
viewer-live/native2c68 authority remains separate and untouched. Ready for parent
source integration review, not bootstrap live activation or whole ZIP completion.
Dirac shared TransportEndpoint acknowledgement remains unverified; valid-volume
and installed/native acceptance still pending, resource helper WARNING/exit2.
[Exact pair, current tests, catalog owner review and gates](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/paired-pin-handoff.md).

Earlier source evidence: **136 passed, 2 actual MCP cases deselected, 10.64s, exit0**,
whole process14.18s/432464KiB RSS. Dependency rollback/close shard:45 passed,
0.40s, process3.68s/362564KiB RSS. Earlier123-pass and fixture failures retained.
Verified source imports and focused nested handle/path/foreign/uncertainty/native
readiness/declaration projection plus unchanged complete QA/context bounds.
Those provider-free suites do not establish installed/live/performance proof.
Two subsequent source-native MCP journeys are recorded separately below.
Receipt, actual pattern review and focused census:
[runtime_bootstrap_20260930.md](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930.md).

Source hardening includes both-address pre-bind reservations, post-spawn
uncertainty handles, expired-deadline no-spawn, real offline CLI projection and
authoring/core exposure. Normally integrated main94070f5f4 before native dispatch.
Earlier dependency pins: ZMQ28d9ed6a0121ebb524ae37fd97de5355308bda7f and metaclass-registry448cdf07;
current reviewed native pin2b3d821 is recorded in the handoff above.
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
The rollback source suites launched no native/MCP/GUI/Java. Installed source
and managed skill remain unchanged throughout subsequent source-native validation.

Prior packaged R0 ratchet at78b5f9 vsbd1 failed (exit1,14.27s/86092KiB) on
GodClassExcess RuntimeServerService +15 and ZMQExecutionClient +32. Original JSON
and resource receipt retained. This source correction does not claim a passing
own-PR ratchet/global audit or fix that separate structural remainder.

Source-only continuation normally integrates merged275/273 at main546edd57.
At1f332d161, destination resolution moves onto the EXISTING
ExecutionRuntimeLaunchPlan declaration; client caching, admission-before-spawn,
native lifecycle, transport declarations and wire fields stay unchanged.
Focused bootstrap suite:25 passed/3.16s, process3.72s/246212KiB/exit0.
Original failed scratch-parent setup XML is retained separately.
Original packaged GodClassExcess measure, authenticated against pinned3b03785,
scoped to these two owner modules: client growth +32 -> +9; service remains +15.
This is NOT a passing complete ratchet/NRA or full class decomposition.
New-case witnesses use both existing transports with nondefault namespace,
IPC naming and control-port topology, prove noncreating projection, and retain
the exact cached/admitted plan. Current write set only client, bootstrap tests
and receipts; no parent experimental-analysis/R0/L0 or Dirac ACK/viewer edits.
[Owner move, evidence and remaining scope](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/launch-plan-factoring/checkpoint.md).

### Effective transport defect correction (parent943898 witness)

Normally integrated mainc50f42c before correction at3b78eb1fd. The original
OpenHCSZMQConfig.client_endpoint now owns host/port/mode default/override policy
for both connection projection and actual native client construction. Deleted
the client-side copied defaults. Source locality checks the ACTUAL effective
client endpoint before plan/writes/spawn; produced typed handles retain the
resolved nominal connection. Observe/close and URL/control projections derive
that same route. The catalog projection supplies its injected config too.
No duplicate endpoint/config store, global mode mutation, new launcher or mode
switch. Native ZMQ/Dirac/viewer declarations unchanged; paired pins unchanged.

**48 source testsPASS4.05s**, process4.65s/255392KiB/exit0: omitted/configured
TCP/IPC and explicit overrides, locality no-write rejection, nested handle
round-trip and start->observe->close route sameness with changed observer defaults.
Spawn/network/shutdown intercepted; not a new native/installed acceptance.
Unmodified parent3-case witness: actual observe route and explicitIPC nowPASS;
raw no-config comparison stillFAIL/exit1 because it never supplies the different
config used by its client. `transport_endpoint(config)` or `resolved(config)`
fixes that caller-context omission without changing its expected native endpoint;
six cases prove both. Original diagnostic/output retained, not made green by
fabricating TCP defaults or cached hidden state. Parent owns its diagnostic.
Scoped original GodClass measure now client+8/service+15, NOT full guard pass.
[Exact review, tests and original witness limitation](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/effective-transport/checkpoint.md).

### Existing-owner closure of the structural growth remainder

At9cb7703d2, normally integrated main7d0ce5e68, the EXISTING admitted
ExecutionRuntimeLaunchPlan owns path materialization and process-policy invocation;
deleted that command/directory/log procedure from the client. Canonical native
reservations/incarnation/uncertainty remain unchanged. The EXISTING
RuntimeBootstrapState owns pure derivation from typed native journal/heartbeat
observations; the service retains admission and bounded I/O and its decision
body is deleted. No new forwarding service/mixin/registry, mirror or launcher.
Owner/new-case witnesses and IMPL-13/IDEN-8/BOUND-2/AGENT-6 review in the receipt.

**100 source testsPASS4.74s**, process5.39s/257852KiB/exit0,0skips/deselections;
all-phase readiness/identity, exact admitted-plan materialization, child config,
failure/no-retry/log closure and original route/admission/uncertainty controls.
Popen/network/shutdown intercepted; no native/installed/scientific proof claim.
Original packaged structural ratchet against main7d0ce5e68 **PASS5,159metrics,
zero positive deltas,15.83s/87520KiB/exit0**. Client excess181->139 (-42),
service0->0. This closes the recorded own-PR +8/+15 growth, not existing debt,
full class decomposition or R1/all-detector NRA. Earlier failed receipts retained.
No native allocation under criticalswap16.3, no dependency-pin/ACK/viewer changes.
[Exact owner decisions, tests, ratchet and limits](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/owner-factoring-checkpoint.md).

### Paired native ownership correction and current source integration

Normally integrated OpenHCS main4a9c9b3e at0ac6157e7. Paired native source
implementation4434b11 normally merged ACK main3374aa8; published native receipt
head2b3d821. Existing TransportEndpoint owns pair locks/admission/publication/
provisional rollback, used by startup, ordinary connect and owned close. Existing
shutdown operation owns one dispatch plus completion; existing mode owns close
admission; discovery uses existing endpoint typed ping/projection. Deleted
client procedures, no new size-only helper/mixin/store/codec/launcher.

**181 paired source testsPASS5.00s**, process5.63s/257380KiB/exit0,0skips/deselections;
native-only81PASS0.44s/44776KiB. No native/MCP/JVM/GUI allocation. Original
packaged WHOLE native-root structural comparison3374aa8->4434b11 **PASS186 metrics,
zero positive deltas,4.42s/48180KiB/exit0**, client excess127->124 (-3).
Parent's original +142 failure retained. Existing debt remains; no global NRA,
R1/all-detector or live proof. OpenHCS5159-metric pass remains its earlier exact
7d0ce5 baseline, not a freshly run4a9 comparison.

Recorded parent gitlink remains28d9ed6; explicit PYTHONPATH exercised candidate
child4434b11. Parent owns reviewed paired-pin cutover/install/live. Additional
shared TransportEndpoint extension communicated directly to Dirac in
[PR11](https://github.com/OpenHCSDev/ZMQRuntime/pull/11#issuecomment-5910632999);
acknowledgement is NOT verified, no prior agreement claimed. No ACK-private/
config/return-route/viewer edits. Full archive author unknown; S1 stays blocked.
[Actual paired evidence and remaining gates](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/paired-native-owner-checkpoint.md).

Subsequently normally integrated main65b2ed101 at17c22731a (PR208 memory source
checkpoint), initialized exact ArrayBridge409 in this own tree. Native candidate
still2b3d821 with verified ACK3374 ancestry; parent recorded pin still28d9ed6.
Explicit source-path resolution verifies root+all eight children here without
importing package bodies. No source suite rerun or new native/installed proof;
181-case/ratchet evidence retains its exact earlier baseline. Parent's installed
main65/ArrayBridge409/native0f9 authority remains separate and untouched.

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

### Actual source-native workflow: partial success, whole journey failed

Normally integrated main94070f5f4 before dispatch. Attempt01 retained a returned
path-policy refusal on immutable prepared input, after successful registration;
no compile/execution was submitted. Its original owned runtime closed successfully.
One explicitly authorized distinct attempt02 used a byte-identical tiny scalar
OME copy in its own writable input directory at frozen304f5d30.

Actual exposed MCP bootstrap0.052s, responsive typed catalogue preparation
(92.206s job, ordinary10s observations), one reviewed registration0.257s,
real BioFormats artifact-plan inspection6.568s, and successful compile6.840s.
Execution4084d670-c3fd-420b-9405-1da41462ed15 FAILED at reduced VolumeFixture1:
two derived image names against three runtime provenance planes. Full step0
and its partial files are retained; readback checker was not reached. Subsequent
source tracing corrected the initial diagnosis: that fixture promised complete
MainFlowStackOutputSpec lineage while reducing the stack. This is NOT yet evidence
of a runtime product defect. Parent merged test-only PR272 using existing explicit
projection declarations; no production count/provenance guard weakened.
No input fallback or source-bearing request replay.

Supported exact-owned close0.587s proved process exit, not just lost listeners.
Original driver/MCP/native PIDs are absent;5964/6964 vacant; shared lock released.
[Original attempt02 receipt and scope](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/native-attempt02/checkpoint.md).
No installed-source/skill mutation. Wildcard ACK7555 remains an independent
configuration boundary; no foreign owner contacted and no collision fix claim.

Normally integrated main642821c before any new dispatch. Diagnostic preparation
now passes17 focused tests/1.49s: original manager accepts each single-declaration
source, exact primary+named-image inventory and all five CSV coordinates guarded.
Distinct12-step native workflow was prepared for full/reordered/reduced/singleton,
first/chained inspectors, two registrations once each after READY. Attempt03
started at a6c0fa448 before the parent's new critical-swap stop. Its older diagnostic
guard admitted swap-only reasons even at critical level: NOT a passing guard claim.
Original progression was interrupted with ZERO registration/compile/execution
calls. Same-handle preparation cancellation returned already READY; exact-owned
close233ms proved process exit. Driver/MCP/native absent,5965/6965 vacant,
shared lock released; accepted=false. No fourth attempt or installed change.
After terminal cleanup the diagnostic consumes the original resource owner's
critical level, without copying thresholds. Focused tests20pass/1.45s/exit0.
Original stopped receipt unchanged; a later warning/exit2 resource observation
does not authorize another native allocation, and no attempt04 has started.
[Attempt03 disposition](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/native-attempt03/checkpoint.md).
[Preparation and review](https://github.com/OpenHCSDev/openhcs/blob/feat/owned-runtime-bootstrap-20260930/docs/validation/runtime_bootstrap_20260930/projection-attempt03-preparation.md).

Remaining: #257 successful full execution/publication and actual strict readback,
additional cross-process uncertainty shard, Dirac shared-surface acknowledgement,
then parent reviewed merge/install and installed entrypoint acceptance. The paired
pin mismatch is now resolved. Prior failed
god-class receipts remain; both original structural comparisons now pass at the
documented exact sources/baselines, without a global NRA claim. References #251
and #257; **not Closes** pending actual acceptance. Parent owns integration/live.
