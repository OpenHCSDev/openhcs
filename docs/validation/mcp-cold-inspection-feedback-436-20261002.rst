Cold inspection feedback: source checkpoint for issue436
======================================================

Base: main4754fbe2b6a7969380c0fe7b749dee0a5bdf8643. Dewey owns source;
parent owns integration and fresh installed qualification. Addresses436, not an
installed or scientific completion claim. Original C3 physical inventory UNKNOWN
and successful storage-only compilation remain unchanged and are never replayed.

Current boundary and ownership
------------------------------

InspectPipelineSourceArtifactPlanCapability and source-session creation already
compose MainThreadProgressCapability. The merged438/443 dispatcher, off-main SDK
loop and matching request-token heartbeat are not being rewritten. The original
query and sample declarations lacked that capability despite calling the same
potentially cold reader/handler preparation. Both now inherit the original
main-affine capability; no worker-thread-safe claim is added.

AgentProgressQueue was a final-only raw dict collector. Its existing put boundary
now descends through ProgressEvent.from_dict once and stores the original typed
event, then projects its actual phase/status/axis/step/count into the existing
EndpointStartupStatus request relay. No additional queue, observer, store, enum,
registry or timer. progress_event_count remains compiler-event count, NOT MCP
heartbeat count. One compile axis can correctly produce count1.

The original CompileInspectionGatewayABC owns compilation preparation, failure
and successful projection-completion notification. Concrete gateways implement
the existing compiler hook through _compile; the in-process owner additionally
reports workspace initialization, compilation and source projection at their
actual boundaries. Compiler/catalog/kernel and ObjectState placement is intact.
The shared PlateInspectionService._create_handler and inventory boundary expose
actual physical preparation stages for existing consumers, including streaming.

CLI distinction
---------------

Original generic call has10s idle; artifact-plan command has60s default. Neither
changes. The original dev client captures notifications in its diagnostic stream;
its default persistent shell uses a private TemporaryFile rather than stdout.
Consequently absent intermediate stdout is not proof that wire heartbeats were
absent. This source checkpoint supplies real stage messages; parent qualification
must retain the existing diagnostic stream and actual matching wire notifications.

Pre-edit trace
--------------

Existing refactor-audit ParsedModule/measure_source AST owners parsed703 OpenHCS
production modules plus32 zmqruntime,193 pyqt-reactive and63 PolyStore modules:
991 modules, zero parse failures. Class bases, imports, field writes, comparisons,
calls and progress-family declarations were searched across these roots, then
the actual sites read. Initial guessed ObjectState root was absent (0files),
not evidence of complete dependency coverage; its actual .pth backing is traced
separately. Dynamic imports/metaclass execution were not resolved by this static
search. Generated binding/MRO and real compiler behavioral checks follow.

Search found only the original AgentProgressQueue and one production concrete
CompileInspectionGatewayABC leaf. Original queue setter remains process-global
and serialized at the original gateway; no new lifetime store or cross-thread
compiler consumer is introduced. Existing core ProgressPhase/ProgressStatus
declarations, compiler emit and core-owned projection consumers remain intact.
PR394 head424bd202 owns core/runtime; PR404 head5f17851 owns persisted ROI docs/
controls. Neither changes these agent service/capability files. Native send_input
is not exposed in this tool session; no shared394/404 file is edited.

Rules applied: MEMB-2 capability MI; IMPL-4 complete gateway lifetime through its
original ancestor; BOUND-2 use original progress codec; IMPL-12 reuse request relay.
Read current NRA/refactor-audit skill archive, catalog, source precedents44/45/51/
58/60 and the original OPENHCS-HISTORY.md in comms-cleanup-live-integration WT.
No global FULL/R1 claim; original failed resource evidence remains independent.

Qualification
-------------

First bounded shard:19PASS/3FAIL,505756KiB/12.734s. Retained RED records
the original two-field fake-event assertion (now typed through original codec),
an incomplete test path-policy constructor, and a cooperative hook placed on a
terminal concrete _compile implementation rather than the shared compile entry.
Corrected test boundary/fixtures without changing production behavior, weakening
domain assertions or adding compatibility readers. Correction shard:4PASS,
502328KiB/12.269s, including both before/after declared MROs and success/failure.
Combined unique qualification:22 cases across these shards, including original
metadata writes/path admission, syntax/enum rejection and actual inventory reads.

Original real compiler plus generated binding stage-order controls:2PASS,
494232KiB/11.380s. Staged64x64 source, original declared NLM compilation, exact
A01/source count/step identity, no unrelated catalog, original Qt/main affinity,
request ContextVar and off-main stage reporting. Actual compiler count1 and one
stored typed event; all seven preparation/compile/projection stages observed in
order. This is source qualification, not fresh installed Java cold preparation.
Existing completed client renewal/26controls/12s experiments were not repeated.

Logs retained in validation/cold436-source-controls-first.log,
cold436-source-corrections.log and cold436-real-compile.log. Scratch only under
/home/ts/.cache/agent-scratch/dewey-436-cold-feedback-*; failed inputs retained.
Original scoped R0 against this production head pending.
Parent fresh installed cold synthetic inspection and physical reader preparation
remain required; no new native/viewer/scientific process, install or download here.
Resource helper reports3.6GiB home and swap pressure; use only existing WT/env,
serial oneCPU/512MiB/60s source shards and small retained logs. No new fleet/cache.
