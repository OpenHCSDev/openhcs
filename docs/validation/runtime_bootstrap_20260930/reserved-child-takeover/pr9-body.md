## Canonical exclusive bootstrap and exact-owned lifecycle for OpenHCS251

Paired [OpenHCS PR256](https://github.com/OpenHCSDev/openhcs/pull/256), references
[OpenHCS issue251](https://github.com/OpenHCSDev/openhcs/issues/251) and
[unfinished volume acceptance257](https://github.com/OpenHCSDev/openhcs/issues/257).
Working draft; no Closes claim.

Current published source/receipt **112c240464df6e81c25b0f97d2b1376d43bbbbc8**,
production0ca331a, normally contains native main2aa6d21c, viewer7 and ACK3374.
Parent owns coherent integration/install/affected live proof. No installed change.

### New occupied-endpoint ownership correction

Ordinary TCP connect could kill both port owners after failed attachment before
checking canonical startup reservations. Existing occupancy-false tests missed
bind-before-ready. Production0ca331a now consumes the ORIGINAL
`TransportEndpoint.has_live_startup_owner(config)` under both held locks BEFORE
takeover; healthy attachment stays earlier/allowed. Final unoccupied pre-spawn
guard stays. No other production file changed in this correction.

Six pre-fix intercepted-kill failures retained: both reserved addresses, known/
unknown liveness and malformed records. Real original records/locks/inodes;
only process/network effects controlled. Initial mis-cased root-path assertion
preserved; corrected all-nine-package path authority confirmed before reproducing
the same failures. **197 paired source casesPASS5.39s**, zero skips/deselections;
process6.20s/264612KiB/exit0 under30s shell bound. Existing Python3.12-B/thread1,
explicit own OpenHCS root+all eight src children, Fiji shared cache/downloadfalse.
No native/MCP/JVM/GUI/science/provider or validation-slot use.

Original authenticated packaged ratchet, WHOLE src/zmqruntime main2aa6d21c ->
production0ca331a: **PASS188 metrics/no positive deltas/client excess delta-1**,
4.79s/47992KiB/exit0. Existing debt remains, not full NRA/R1/global audit.
[Current owner/reproducer/receipt](https://github.com/OpenHCSDev/ZMQRuntime/blob/feat/exclusive-endpoint-bootstrap-20260930/docs/validation/issue251_reserved_child_takeover_20260930.rst).

### Full working feature ownership

Existing ZMQClient owns explicit exclusive empty local pair startup; original
TransportEndpoint owns canonical pair locks/admission/publication/provisional
rollback/discovery. Original TransportDeclaration alone decodes/releases native
records, retaining inode and exact PID+creation-time ProcessIdentity.
No-child publication/deadline failure rolls back only that provisional invoker;
unknown/changed/child/post-spawn failures retain uncertainty, never replay.

Existing shutdown operation owns one request and completion; existing mode owns
close admission. Exact-owned FORCE requires both native reservation identities
and incarnation-bound handler admission BEFORE worker mutation. Listener loss
alone is not identified process exit. Original ProcessIdentity owns one bounded
TERM/KILL/wait budget; GRACEFUL clears workers/keeps server. Original5993 cleanup
was parent-owned, not replayed. No forked launcher/registry/controller/store,
compatibility route, arbitrary helper/mixin or increased timeout.

Replaced client procedures deleted in-place. IMPL-12/13, IDEN-8, BOUND-2,
AGENT-6 review includes concrete existing-owner/new-case witnesses.
[Earlier ownership correction](https://github.com/OpenHCSDev/ZMQRuntime/blob/feat/exclusive-endpoint-bootstrap-20260930/docs/validation/issue251_owner_factoring_20260930.md).
Parent's original +142 whole-native growth failure remains retained, not
relabeled; current source comparison closes introduced growth, not existing debt.

Current full-feature native production claim remains client.py, execution/server.py,
messages.py, transport_modes.py and TransportEndpoint in transport.py.
Correction touches only client.py/test_owned_startup.py. No ACK-private/config/
return-route/viewer-state7/waiter6 edit. Parent now owns ACK issue10 integration;
older shared-surface acknowledgement was unverified, not fabricated. Broader
archive author unknown, BLOCKED S1 unchanged; R0/L0 are not full S1-S8 coverage.

Historical native attempts01/02 had successful bootstrap/preparation/registration/
exact close but no successful whole valid-volume readback. Attempt02 used a
malformed complete-stack declaration, not proof of a product metadata defect.
Attempt03 interrupted in preparation with zero registration/compile/execution;
same-handle exact close terminal. All originals preserved; no attempt04/replay.

Remaining: actual valid-volume full/reorder/reduced/singleton first/chained
compile/execute with complete durable image/label/CSV/source-address/ROI/declared
projection inventory, cross-process uncertainty, then parent paired merge/offline
install and installed entrypoint acceptance. Science slot and current resource
warning forbid fresh worker native allocation; no optional hosted-CI wait.
