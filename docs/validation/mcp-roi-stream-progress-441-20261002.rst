MCP saved-ROI streaming progress: issue441
========================================

Owner Dewey; parent integrates and qualifies the installed viewer entrypoint.
Base main8551a48644b5a9cd054ca1c738ffef2295c5266f (merged439). This patch owns
only the MCP capability declarations and agent PlateStreamingService progress
boundary. Root394 retains core materialization/runtime ownership; Singer404/440
retains reopening/publication work; Planck's active scientific viewer is untouched.

Failure and stage trace
-----------------------

Issue441 records two original saved-ROI requests with an ordinary10s timeout and
later mounted side effects, plus a subsequent queued UI-dispatch timeout. Neither
UNKNOWN request is replayed or declared successful. Original journals stay at
``/home/ts/wt/openhcs-issue-batch-20260929/rbpms-r0010-development-434-20261002/output/``:
CONTINUATION02-QA-RECEIPT.rst and mcp-continuation02/03 stdin/stdout/timing.
The continuation03 log retains compatibility-handshake/stale-viewer warnings
and source CZI reader initialization, not an established single-stage timing.

The service resolves the viewer context and physical plate context, admits the
inventory and original source binding, awaits managed-viewer readiness30s,
loads/publishes ROIs through StreamingService, then awaits authoritative viewer
settlement. Original readiness can itself wait15s; original settlement has a
30s no-progress bound and forward-work renewal. These are existing stage limits,
not new limits. Native mounting does not establish that MCP returned its receipt.
The retained logs do not isolate which stage dominated the original request.

Source change and ownership closure
-----------------------------------

The two stream leaves now compose existing MainThreadProgressCapability with
their original plate/UI-selection capabilities. Original generated binding and
dispatcher keep Qt/process-main affinity, off-main SDK I/O, request-local
callback propagation and authoritative completion after dispatch starts.
No compiler/catalog/core placement, client timeout, timer, poller or status store
is added. Original pre-start queue cancellation remains intact.

PlateStreamingService relays its context/inventory/viewer-readiness stages and
original core status callbacks through EndpointStartupStatus.callback_scope.
Its existing result status_messages list remains the receipt owner. The shared
recording method appends that original receipt and publishes to the original
relay; no second status roster/decoder or mirrored registry is created. Stage
arrival/heartbeat times in the next installed journal can locate actual latency;
this is not a claim that source decoding or native mounting became faster.

Applicable authoritative catalog patterns: MEMB-2 independent capability MI;
IMPL-4 close the original execution family; IMPL-12 reuse the existing relay and
dispatcher rather than copy them; BOUND-2 use original native ROI metadata and
viewer projection owners. No generic consumer gains a tool-name/type switch.
The independent new stream declaration adds a cooperative audit hook through
super() and runs the real generated binding without changing generic consumers.

Original pinned R0 at4565562f6 found GodClassExcess +20 for the streaming service
(160300KiB/15.385s, returncode1). The full RED is retained, not waived. The
correction removes three repeated common PlateFileStreamResult projections:
the original service builds its original DTO once, then uses dataclasses.replace
for no-stream/error/success terminal facts. It deletes40 lines and adds19 in
that same owner; no result factory/facade, schema or authority store is added.
Exact corrected-head R0 and terminal contract controls are pending below.

Finite source controls and retained attempts
-------------------------------------------

Tests use the original saved-source declaration fixture, original disk ROI
writer/decoder, real inventory/PlateStreamingService/StreamingService, generated
MCP binding and resident SDK transport. Only viewer acquisition/receiver/native
settlement are controlled; a12s settlement occurs AFTER publication. Same-session
success, strict unsigned-ROI rejection and warm reuse use original dev-client
10s idle/token renewal. Matching tokens, early acknowledgement, progress beyond
10s, exact original geometry/calibration/native source metadata and affine
callbacks are asserted. This is a source-wire guard, not an installed viewer.

Four distinct focused source cases now PASS across retained shards: fifth
attempt3PASS/1 harness hook failure (333088KiB/19.844s), then the one corrected
new-case control PASS (329392KiB/6.745s). The continuous real service/SDK journey
returned success12.074561s, strict missing-source error0.024237s, reuse0.028338s,
with unchanged10s idle and matching tokens2/3/4. The incorrect new-case hook
overrode execute_request, but the connection-bound family actually owns
execute_connection_request. The corrected before/after MI leaves cooperate
through that original hook, preserve direct request ContextVar propagation,
and exercise the generated consumer without changing it. The12s PASS was not
rerun to correct the independent hook. Further original controls are pending.
Shards enforce
one CPU,512MiB aggregate RSS,60s through the existing cgroup monitor. The readonly
paired-parent Python and declaration-derived native ABI loader are reused;
no downloads, environment changes or dependency/gitlink changes occurred.

Retained harness REDs (validation/stream441-*-source-controls.log): first missing
test-support import path; second overlong Unix socket and incomplete agent
context; third assumed cross-wire ContextVar value and over-wide viewer metadata
assertion; fourth displayed the canonical projection mismatch explicitly.
The corrected harness uses the real OpenHCSAgentContext, a bounded local socket,
and separately checks persisted full provenance and declaration-owned viewer
metadata. No production source-provenance assertion is removed or weakened.
All failed synthetic inputs remain in owned agent-scratch/dewey-441-stream-source*
directories; none are biological inputs. No broad cleanup is performed.

Original scoped R0 will compare this base to the exact published production
checkpoint using the unchanged pinned tool. Full R1/global FULL remains outside
this bounded source claim; original R1/resource failures and439 full-stdio12s
resource RED are unchanged. Completed438/439 shards are not rerun.

Installed acceptance (parent-coordinated, pending)
------------------------------------------------

After resource/slot approval, use a NEW explicit engineering saved-source/ROI
fixture and a fresh isolated managed viewer, not either original UNKNOWN input.
Fresh public health/guide then raw mount and one explicit saved result stream
must return the original PlateFileStreamResult with request-scoped progress and
unchanged10s idle. Read back exact viewer incarnation, bounded raw+ROI layers,
physical source/component identities, calibration and synthetic geometry.
Record elapsed stage times rather than infer a speedup from heartbeat delivery.
Then a distinct unsigned-ROI rejection and acknowledged warm synthetic reuse
must return their original terminal receipts without duplicate/restarted calls.
Exactly close owned processes and retain source/receipts/resources. Do not adopt,
mutate or restart Planck's active viewer, run biology, or replay UNKNOWN streams.
