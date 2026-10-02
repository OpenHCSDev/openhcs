## Ready for parent paired source merge: exact-child lifecycle and scoped startup feedback

OpenHCS #355; related managed-viewer #385. Source/integration owner: Schrodinger/Codex. Exact reviewed/published dependency head remains **`668edafcb5ee530a163377c936431ae1e8334e85`**, including readiness/activity `23097e26`, shared viewer-process ownership `a9d4ddd` and callback delivery **`423b141`**.

Paired [OpenHCS PR358](https://github.com/OpenHCSDev/openhcs/pull/358) normally merges main `76a2d392` (#388/#397) and final production **`69e917d2a7002f128392941355e827e498d1c6b1`** now advances its ORIGINAL ZMQRuntime gitlink to this EXACT668edaf head. No old-dependency fallback or install against the stale23097 pin.

### Existing owning mechanisms

ZMQClient owns the sole typed readiness algorithm and composes domain journal, exact-child activity, cancellation and total deadline. OpenHCS deletes its copied algorithm. EndpointProcess owns the shared startup observer; native leaves provide small identity/wait/stop hooks. ProcessIdentity observes exact-incarnation CPU work; CPU/journal activity may refresh inactivity but never proves readiness. Unchanged liveness, terminal child/failure/cancellation and explicit deadline do not become success. No timeout increases.

VisualizerProcessManager retains the existing EndpointProcess owner and delegates original stop rather than copying Popen signal/wait/kill or discarding identity/exit evidence. Parent owns paired installed managed-viewer acceptance; historical5992 disposition remains unproved.

NEW feedback scope: **existing EndpointStartupStatus owns callback_scope/publish**. Existing ZMQClient constructs/sequences ONE status and delivers the SAME object to explicit UI and request-local callbacks. The existing Python ContextVar mechanism resets on exit/error and propagates through asyncio.to_thread, without permanently storing MCP request callbacks on reused clients. OpenHCS's ORIGINAL MCP awaiter/notification mechanism consumes the statuses; no second observer/polling/bootstrap or parallel readiness authority. Dataclass/wire fields and process/deadline behavior are unchanged.

IMPL-12/13 reuse and delete duplicate mechanisms; IMPL-1/3/4/5 no kind/type switches; MEMB-1/2/5 no parallel rosters/stores/schema; TIME-1/3/9 no aliases/facades. No ornamental product MI. PR6/H003 execution/wait_policy.py waiter-status ownership remains untouched and is not claimed fixed here.

### Behavior, guard and limits

New StatusAudit capabilities before/after a new client declaration exercise the actual matching cooperative emission hook in both C3 orders without consumer edits. Nested/error scopes, exact original object delivery, explicit UI callback and duplicate-callback avoidance pass. Two concurrent requests use ONE reused client through worker contexts without cross-talk. Paired MCP tests cover actual generated binding/service/client pending responses, immediate phase notification, terminal error preservation and dropped late callbacks after cancellation; new declaration tools derive from the existing registry with cooperative hooks.

Retained paired source selections: **25 feedback pass** (9.86s / 324296KiB), **50 lifecycle/UI-source pass** (4.36s / 233496KiB), four overlapping cases. Preserved original red10, failed wrapper diagnostics and original355 control/rejected-R0 receipts. Main integration leaves these mechanisms/tests unchanged; no redundant replay of completed selections.

Original pinned **R0 passes final dependency85c8284f→EXACT668edaf**,184 projections/zero increases,3.67s/48328KiB; only nonzero delta ZMQClient GodClassExcess -26. Paired OpenHCS main76a2d392→69e917d2a passes5238 projections/zero increases,22.63s/87548KiB. Guard is unchanged comms-ratchet3b03785f with its original Python3.14/read-only backing dependency, not a copied policy. All source checks serial CPU0/pools1,512MiB/no swap,60s. Original global R1 deadline retained, no full R1 retry or budget increase.

Full current paired receipt and exact R0 commands/JSON/checksums are versioned in OpenHCS PR358 at `docs/validation/paired-feedback-integration-358.rst` and `paired-feedback-integration-evidence/`; feedback evidence at `startup-feedback-358.rst` / `startup-feedback-evidence/`. Original local receipts in this PR remain durable history.

Parent may merge the finite paired source checkpoint without CI wait; parent owns later installed MCP/UI lifecycle and viewer acceptance once Dalton releases the serialized live slot. No installs/native/UI/MCP/provider/science operations occurred and no installed readiness/performance/global R1 claim. Only verified completed paired source scratch was removed; original failures and frozen/live backing remain untouched.
