# Paired existing-owner source checkpoint

OpenHCS source normally integrated main4a9c9b3e at merge0ac6157e7.
Its bootstrap owner correction9cb7703d2 is unchanged. Native source implementation
4434b11ed769cbc6a15d13754b06529ea6494428 normally integrated ACK main3374aa8;
published native receipt checkpoint2b3d821 follows that implementation.
Recorded OpenHCS gitlink remains28d9ed6. The source test used the reviewed
candidate child explicitly; parent owns reviewed gitlink cutover/install/live.
No implicit dependency adoption or installed-source readiness claim.

## Native behavior ownership and source closure

Existing TransportEndpoint now owns both-address lock acquisition, original
record admission/publication, provisional rollback and exact-pair proof. Explicit
startup, ordinary connect and owned close consume that owner; their repeated
client procedures are deleted. Original TransportDeclaration remains the sole
record decoder/writer/release owner. Existing ProcessIdentity remains the exact
incarnation/process cleanup owner. Both locks, canonical order, inodes and
unknown/changed/post-spawn claim dispositions are preserved.

Existing shutdown operation now owns one source procedure for request admission,
single dispatch, acknowledgement uncertainty and selected-mode completion. Its
mode owns close admission. Existing endpoint ping/projection owns discovery;
the old client scan closure/raw projection is deleted. No new controller/mixin,
reservation store, parser, launcher or compatibility path.

New-case tests cover TCP/IPC with different pair topology, actual file locks and
inodes, all provisional rollback faults, pending control-owner exclusion during
ordinary connect, inherited endpoint discovery, ordering/absent/pending results,
and original exact-close/unknown/single-send cases. Complete native owner decisions
and applicable IMPL-12/13, IDEN-8, BOUND-2, AGENT-6 review:
[native receipt](https://github.com/OpenHCSDev/ZMQRuntime/blob/feat/exclusive-endpoint-bootstrap-20260930/docs/validation/issue251_owner_factoring_20260930.md).
This is not all-detector/global NRA proof or zero existing structural debt.

## Actual tests and original measures

Existing shared Python3.12, -B, explicit isolated root and all eight child src
directories, CPU/thread1, downloadfalse and existing shared Fiji bundle path.
Imports were verified under this tree before the checks. No environment/package
change. Original tests use controlled process/socket calls and synchronous
discovery futures; native lock/record behavior is real. No native/MCP/JVM/GUI,
executor fleet, provider or scientific input launch.

Native81 cases: **81 passed,0 skips/deselections,0.44s**, process0.63s,
44776KiB RSS/exit0. Initial79-case checkpoint retained separately.
XML: native-owner-tests-b.xml, predecessor native-owner-tests.xml.

Paired command, within30s shell bound:

```sh
python -B -m pytest --noconftest -o addopts= -q \
 tests/unit/agent/test_owned_runtime_bootstrap.py \
 tests/unit/test_zmq_execution_server_process.py \
 tests/unit/agent/test_agent_services.py::test_execution_connection_spec_owns_zmq_endpoint_projection \
 external/zmqruntime/tests/test_owned_startup.py \
 external/zmqruntime/tests/test_owned_close.py \
 external/zmqruntime/tests/test_endpoint_ownership.py \
 external/zmqruntime/tests/test_startup.py \
 --basetemp=docs/validation/runtime_bootstrap_20260930/paired-owner-pytest \
 --junitxml=docs/validation/runtime_bootstrap_20260930/paired-owner-source-tests.xml
```

**181 passed,0 skips/deselections,5.00s; process5.63s/257380KiB RSS/exit0.**
100 OpenHCS controls plus81 native; two disabled-asyncio-plugin config warnings.
No new native/installed acceptance claim from this source suite.

Original packaged agent-comms ratchet, native root against ACK main3374aa8:
**PASS186 metrics, zero positive deltas,4.42s/48180KiB/exit0**.
ZMQClient GodClassExcess127->124 (-3). Whole native-root inventory and all five
changed native source paths; not a selected-class-only comparison. Original
parent0f9e840->28d9ed6 +142 failure remains preserved, not relabeled passed.
Native JSON/resources published with the native receipt.

Earlier original OpenHCS root comparison7d0ce5e->9cb7703d2: **PASS5159 metrics,
zero positive deltas**, client181->139 (-42). That is the recorded exact earlier
baseline, not a newly run main4a9c9b3e comparison. No OpenHCS bootstrap production
change since that correction. Neither original structural comparison is global
semantic proof or an R1/all-detector scan. Existing client debt remains.

## Claims, crossing and disposition

Own OpenHCS production claim remains runtime/zmq_execution_client.py,
agent/services/runtime_server_service.py, agent/dto/execution.py, capability/
service declarations and bootstrap guidance/tests. Own native PR9 claim is
client.py, execution/server.py, messages.py, transport_modes.py, plus the new
TransportEndpoint crossing in transport.py. No ACK-private, config.py, viewer159,
waiter6 or viewer-state7 changes. Parent R0/L0/fixture and other named owners'
files untouched; main integrations are ordinary merges, not recreated repairs.

Additional shared TransportEndpoint extension communicated directly to Dirac:
[PR11 comment](https://github.com/OpenHCSDev/ZMQRuntime/pull/11#issuecomment-5910632999).
Published open-PR claims are disjoint, but direct acknowledgement/unpublished
claim clearance is NOT verified. Extension already exists in this candidate;
do not claim prior agreement or proceed to shared-surface adoption on that
assumption. The separate full sept2026refact archive owner is still unknown.
BLOCKED S1 remains blocked; no goal restart/resume.

Actual guard warning/exit2, swap14.6GiB/RAM18.4GiB/home22.0GiB. Only bounded serial
lightweight checks; no native slot, large scan, parallel agent, installation or
managed-skill change. Historical attempts01/02/03 and registered sources remain
unaltered. All three original runtime handles are terminal. No fourth attempt,
retry, foreign kill/close or scientific-data inspection.

After source test processes were terminal and lsof found no open handles, removed
only owned rebuildable native-owner-pytest (788KiB), native-owner-pytest-b (816KiB)
and paired-owner-pytest (2.3MiB) generated directories. All three XML receipts,
native JSON/resources and original attempt artifacts are retained.

Remaining: Dirac shared-surface acknowledgement, parent reviewed dependency-pin
cutover, admitted finite valid-volume compile/execute/strict full durable readback
and installed affected-entrypoint acceptance. Original attempts remain partial/
failed/stopped, not acceptance. References251/257; no issue closure or global
clean claim. Parent retains integration/install/live ownership.

## Subsequent main65 integration (no new runtime allocation)

Normally merged current main65b2ed101 at17c22731a27faec7102321a462dd0c2bb0a0ce58.
That incoming delta is PR208 memory diagnostics/history controls/receipts plus
the ArrayBridge gitlink, not bootstrap production ownership changes. Initialized
own clean ArrayBridge worktree at recorded409b1e0831f815fa9ef91d4ecc04989f9fbb89c5.
Initial submodule fetch was refused because its existing origin is a local file
repository; preserved that failure and fetched only the exact recorded object
read-only from the reviewed memory-integration tree with per-command file
transport admission. Then no-fetch submodule checkout succeeded. No foreign
source edits, persistent Git configuration change, install or package download.

Native working child remains2b3d821; ACK3374 ancestry verified. Recorded parent
native pin remains28d9ed6, awaiting parent reviewed cutover. Other child pins are
unchanged. Existing interpreter with explicit own root+eight child src paths
find_spec-resolves all nine top-level packages within this isolated tree. This
is import-path authority verification without importing the package bodies,
not an additional execution/import smoke or a freshly rerun181-case suite.
Earlier181-case/XML and ratchet retain their exact prior source/base limits.

Parent's ordinary installed import authority is now memory-integration main65
with ArrayBridge409 and native0f9, not this PR256 candidate. No installed/managed
skill mutation, native/MCP launch, validation-slot allocation or S1 resume by this
worker. Resource warning/exit2 is not a new native waiver. No fourth attempt.
