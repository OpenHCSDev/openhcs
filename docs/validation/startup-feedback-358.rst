MCP startup feedback through the original owners
================================================

Source integration owner: Schrodinger/Codex, existing PR358 and ZMQRuntime PR13.
OpenHCS production: 4ab076890cb2ff9568e005abae2bc4d1e77997ed, following4583a1110.
Required paired dependency: 423b1417aa1fe7971ea1023627a4a4adf3b541d3, followingaca18ea.
Current main inspected read-only: c4be92335ed6f02ce22e39a66dd3229bc08ea147.
Its original MCP progress helper and capability declarations matched this base.

The still-blocking route
------------------------

search_functions -> ZMQFunctionCatalogService.search -> reused ZMQExecutionClient
-> connect / _send_function_catalog_control_request -> _emit_connection_status.
UI already consumed its typed connection_status_callback. MCP did not bind an
observer, so its existing helper only reported started/still running. Describe
and other catalog leaves shared cold-connect behavior without the search leaf's
heartbeat declaration. Compile/run submission lacked a progress declaration too.

RuntimeServerService.start_from_request still returns an exact owned handle
promptly. observe_bootstrap still uses EndpointStartupStatusReader and typed
PONG through RuntimeBootstrapState.from_observation. Neither route was changed.
Parent's reported157s readiness witness is not a local performance measurement.

Ownership, deletion and review
------------------------------

OpenHCS:14 production lines deleted,55 added. Dependency:3 deleted,27 added.
EndpointStartupStatus owns scoped callback delivery; ZMQClient still creates
and sequences each original status exactly once. publish delivers that SAME
object to explicit UI and request-local observers. callback_scope resets its
ContextVar in finally; asyncio tasks/to_thread inherit the existing Python
context mechanism. It does not attach observers permanently to reused clients.

_await_with_declared_progress remains MCP's sole wait/heartbeat owner. It relays
the original status objects through a request-local notification queue and
_report_progress_if_available. FIRST_COMPLETED delivers a status immediately
without waiting for operation completion or the heartbeat. Silent intervals
retain the last observed message with still-running text. That presentation is
not a new child observation, readiness witness or deadline refresh. Terminal
statuses flush before the original result/error; cancellation drops late worker
callbacks without killing a native process or replaying the operation.

FunctionCatalogCapability now owns the existing5s progress declaration; the
SearchFunctions leaf copy is deleted. SubmitCompile/SubmitPipelineExecution
provide small declaration hooks. The existing generated binding/registry derives
all tools. The separate source-session leaf remains main-thread-only as before.
Raw threading.Thread contexts are not implicitly propagated; this receipt
qualifies synchronous catalog requests executed by the existing to_thread
adapter, not arbitrary background-thread delivery or all application imports.

Reviewed against the current canonical refactor-audit catalog and installed NRA
skill: IMPL-12/13, one original emission and one original MCP notification owner;
IMPL-1/2/3/4/5, no capability-name/type/phase switch or copied bootstrap; MEMB-1/2/5,
no registry, schema, identity or readiness mirror; TIME-1/3/9, no old-version
fallback, forwarding facade or retained replacement loop. No ornamental product
inheritance was introduced. Existing declaration/MRO mechanisms do the work.
No persisted or external wire format changed. This authored patch has behavioral
source evidence, not an NRA native equivalence proof or new global R1 audit.

New-case and bounded source evidence
------------------------------------

The registered FastMCP tool journey uses its actual generated wrapper, the real
endpoint catalog service and client pending-response loop, with synthetic native
I/O only. Preparation reaches MCP before its5s heartbeat while the result stays
pending; only the original successful control response releases the result.

NewBefore/NewAfter declarations compose an independent InvocationAudit with the
existing search family in both C3 orders. Matching cooperative execute_request
hooks run once, both tools are discovered from the original registry, and real
progress arrives without any generic consumer edit. Dependency AuditBefore/
AuditAfter similarly exercise matching _emit_connection_status hooks around a
new client leaf, preserving one original delivery. Concurrent requests reuse ONE
client through worker-thread contexts without cross-talk in both dependency and
MCP experiments. Nested scopes, explicit UI callbacks, terminal errors and late
callbacks after cancellation are covered.

Retained logs/checksums and exact runner: startup-feedback-evidence/.
Original experiment red10 (5.64s,264512KiB); initial green10; strengthened wrapper
failed1/22passed, then three bounded diagnostics. These exposed default
ALL_COMPLETED waiting on both futures, not a missing callback/context. The
FIRST_COMPLETED repair and expanded tests are green25 (9.86s,324296KiB).
Lifecycle/UI-source regression selection:50passed (4.36s,233496KiB), with the
four dependency scope cases overlapping. No skip in either final selection.
Two existing pytest config warnings appear in isolated diagnostic selections.
Final F/E9 lint passes all touched files; I passes except the untouched existing
capabilities import block, excluded from final I selection. Initial lint/format
findings are retained; the unused dependency import was deleted.

All diagnostics/tests: serial, CPU0/thread pools1, kernel512MiB/no swap,
CPUQuota100%, outer60s, Python3.12.3 at the exact read-only installed interpreter
shown by source_tests.py. Source roots and the read-only native-extension path
are explicit; packages/backing environments were not changed. Resource helper
warning2: RAM16.4GiB/home10.3GiB/root7.7GiB, swap9.7GiB. No provider calls,
downloads, native/MCP/UI launches, science replay or validation-lock acquisition.

Delivery boundary and cleanup
------------------------------

MCP helper/capability crossing was announced BEFORE edits in PR358 comments
5941248951 and5941340904, then parent explicitly confirmed feedback-file
ownership. Codec/Dewey, dev-client, viewer, materialization and installed files
are untouched. Earlier issue385 adaptation remains parent-owned. OpenHCS gitlink
remains23097e26c919b6c1b9621d009ee28f01626f1a65 until parent completes paired
dependency/viewer integration. callback_scope REQUIRES423b141; do not install
this OpenHCS candidate with the old gitlink or invent a compatibility fallback.

Parent owns current-main integration/guard and later paired installed MCP/UI
entrypoint acceptance after Dalton releases the serialized live slot. Source
tests are not transport/live readiness, startup-speedup, viewer resolution or
science evidence. Original cold failure and full-context R1 deadline stay intact.

Cleanup target only:
/home/ts/.cache/agent-scratch/startup-feedback-358-20261001,228KiB measured.
All test workers were terminal; lsof found no handles; retained artifact checksums
verified before exact removal. Source, versioned evidence, original failed inputs,
scientific outputs, parent state and other owners' caches were preserved.
