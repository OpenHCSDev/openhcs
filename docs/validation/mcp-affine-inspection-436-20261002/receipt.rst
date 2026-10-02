MCP source inspection affinity/progress — issue 436
==================================================

Owner: Dewey. Source-only checkpoint, based on merged main 902913616.
Parent owns installed/cold/public qualification and the native validation slot.

Original failure is retained, not replayed
----------------------------------------

Authoritative original evidence (linked, not copied) is
``/home/ts/wt/openhcs-issue-batch-20260929/neurite-development-skill383-20261001/output/assisted-5-434/STARTUP-READY-AND-INSPECTION-DISPOSITION.rst``
and the adjacent original stdin/stdout/timing. First cold source artifact-plan
inspection exceeded the ordinary 10-second client idle interval after READY;
the same MCP remained healthy. Inspection is UNKNOWN, not absent, because
authorized workspace metadata may have been persisted. Native compilation
was a distinct later request. Neither original request is replayed here.

Boundary and ownership
----------------------

The original synchronous generated inspection binding runs inline on the SDK
asyncio loop; adding a heartbeat cannot make that blocked loop responsive.
ObjectState and Qt remain main-thread-owned. MainThreadProgressCapability
composes the original ProgressAcknowledgedCapability with the original source
capability families. Both source-backed leaves inherit the 1-second heartbeat
and explicitly prohibit worker execution; their duplicated leaf settings are
removed. The request-token/client machinery from merged 422 is untouched.

McpMainThreadDispatcher extends UiThreadDispatcher, preserving its queued-call
ownership, pre-start cancellation and authoritative wait once started. Only
the request ContextVar projection and headless process-main-thread check are
added. McpTransportExecutor extends AsyncOperationExecutor and reuses
FutureCompletion plus a QCoreApplication event dispatcher to run SDK I/O
off-main. There is no QApplication, viewer, native runtime launch, new timer,
poller, progress/status store, registry or compiler algorithm. Stdio and the
resident transport share this owner. Ordinary synchronous tools also dispatch
to their original main-thread owner; worker-safe progress operations retain
their existing placement. Compiler/kernel/catalog placement is unchanged.

Review: MEMB-2 nominal capability composition, IMPL-4 complete execution family,
IMPL-12 reuse rather than copied procedures, BOUND-2 original SDK/Qt integration.
No per-tool string/type switch or mirrored declaration roster is introduced.
The new-case control adds independent cooperative audit hooks on either side
of a new leaf's MRO; the original registry and generated consumer are unchanged.

Source evidence and current limits
----------------------------------

Existing startup/progress controls: 13 PASS, aggregate RSS 322240 KiB,
9.637 seconds including the monitor, 1 CPU / 512 MiB / 60 seconds enforced.
The first attempt with the older generated-inputs interpreter failed collection
because its pyqt-reactive lacked RENDER_COMPLETE; no dependency was installed.
The current paired-parent interpreter is used read-only instead.

Initial new controls: 5 PASS / 1 FAIL, RSS 333480 KiB / 15.618 seconds.
That failure was the new test incorrectly expecting an AgentError ``details``
field. Production terminal projection was unchanged; the assertion now compares
the full original AgentError owner projection instead. This initial red remains
in the native journal; it is not claimed as a product failure or erased.

The generated binding controls exercise main-thread and Qt affinity, off-main
SDK progress, request ContextVar propagation, exactly-one invocation, original
ValueError projection and unchanged CancelledError identity. Final source
controls, both continuous transports and real compiler entrypoint qualification
are in progress. Installed cold public acceptance is PENDING, not implied by
these source controls. No global FULL/R1 qualification is claimed.
