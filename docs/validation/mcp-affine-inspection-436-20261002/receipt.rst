MCP source inspection affinity/progress — issue 436
==================================================

Owner: Dewey. Production checkpoint 08054fccf9cc05c08168cb317c222ab9abbb5e12
is MERGED in PR438 at 4d48ded6570ed0730dc8d6437ae130ab48e3ca47.
Parent qualified the ordinary private installed public entrypoint. This
follow-up archives source tests and proof only; no production bytes change.
Native execution, viewers and scientific/biological readiness are NOT claimed.

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

Source evidence at initial draft (historical)
---------------------------------------------

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

Published checkpoint continuation
---------------------------------

At the then-published 08054 checkpoint, draft PR438 was visible. Source shard:
26 PASS, 348112 KiB / 28.723 seconds with unchanged source bounds. It includes
two successive resident connections with successful and failing inspections,
using the original dev-client token idle renewal (1.6-second test idle interval,
2.4-second main-thread work), not a new client loop. The full stdio SDK probe
uses the unchanged ordinary 10-second deadline and records progress at ~20ms,
~1s and ~2s before each ~2.4-second terminal result.

First stdio harness attempt selected installed rather than own Python source
because the SDK deliberately does not inherit arbitrary PYTHONPATH entries.
The owned source loader now selects the source root explicitly and derives
read-only native extension membership from installed distribution metadata;
there is no copied binary, install or Python-source fallback.

The successful initial stdio monitor accounted only its process group: the SDK
creates a new process group. Thus its 82012 KiB figure is NOT combined RSS proof.
The existing bounded-source monitor is corrected in place to derive membership
from its original systemd scope's cgroup.procs and sum each process's RSS. The
512MiB cgroup limit and 60-second deadline remain unchanged. The full-scope
recheck was subsequently completed below; original outcomes remain retained.

Finite terminal source closure
------------------------------

No completed 26-case control or R0 was rerun to produce this receipt.
All checks enforced one CPU, 512MiB combined RSS and 60-second elapsed limits.

* Generated/affinity/cooperative-MRO/resident controls: 26 PASS,
  348112 KiB / 28.723 seconds. See affinity-resident-controls.log.
* Whole-scope real SDK stdio success/error continuous journey: PASS,
  387688 KiB / 11.829 seconds. SDK progress arrived at 13.6ms/9.9ms,
  then ~1s/~2s, ahead of ~2.4-second authoritative terminal replies.
  Ordinary SDK deadline remains 10 seconds. See stdio-whole-scope-controls.log.
* Real generated source binding plus original declared-compiler control:
  2 PASS, 439776 KiB / 9.520 seconds. The generated binding uses the actual
  ExecutionSessionService and InProcessCompileInspectionGateway, a staged
  one-field synthetic plate and original reducenoise declaration. Main/Qt
  thread and request ContextVar identity are checked at the original gateway;
  SDK reports off-main. No native execution is submitted.
* Original unchanged scoped R0: PASS / zero positive deltas, 163716 KiB /
  19.877 seconds. Exact comparison: main902913616e19f5b242928d4e835b8c2e10ab2fce
  to production08054fccf9cc05c08168cb317c222ab9abbb5e12, all six changed
  production Python paths. Original tool source comes directly from retained
  Git 3b03785f45df2ef5dc62ba6aed99294192ecbb01 using actual CPython3.14 and
  read-only metaclass backing. No detector is copied or modified.

R0 original stdout is losslessly archived as r0-original-pin.log.gz;
gzip -cd | cmp against the retained original succeeded. Uncompressed SHA256:
7166a2b70ed0b242beeb28fece55bbd681ce91d11f15986bd6da820cad142645.
This is scoped R0 and named behavioral ownership proof, not global FULL/R1.

Additional red adjudication (retained, no weakened assertions)
-------------------------------------------------------------

The first real binding fixture rendered a registry reference while forbidding
the original cold registry preparation. It failed before reaching the gateway:
pipeline_source_invalid_document. Its full real-compiler-controls.log and
original synthetic scratch remain. The corrected bounded source control is an
explicit original declared-module source (not a cold-catalog/render claim).
The original direct compiler test's unrelated-catalog rejection is preserved.

Additional MCP boundary shard: 11 PASS / 1 source-harness failure, retained in
mcp-boundary-controls.log. Its original bootstrap subprocess could not import
the source checkout's unbuilt _tabular_native extension. The exact bootstrap
test is moved, not copied or disabled, to its original stdio transport family.
Its unchanged failure/health/continued-session assertions and 5-second limits
now run with explicit read-only native ABI admission, reusing source_fixture's
distribution-derived loader. This one corrected control PASSed at 382080 KiB /
  6.926 seconds (bootstrap-source-admission-controls.log). Other stdio SDK
fixtures now explicitly inherit the selected source environment rather than
silently testing an installed implementation. No production fallback is added.

The remaining six original stdio channel/native-import/restoration controls
PASSed on the explicitly selected own source at 213772 KiB / 7.281 seconds
(stdio-original-controls.log). Overall focused source coverage is 46 distinct
PASS cases across these named shards, not a full suite. No production change
was made after 08054 and no completed R0 or 26-case shard was rerun.

Parent installed public acceptance — independently owned
-------------------------------------------------------

The ordinary installed target is
``/home/ts/wt/openhcs-issue-batch-20260929/carrier434-installed-20261002/installed-438-08054``.
I read the retained public source02 log: fresh public health reports that exact
installed source and no stale/recovery state; first_use/debugging guidance is
retrieved; artifact-plan returns errors[], A01, file_count1, step_count1,
DeclaredSyntheticNlm, progress_event_count1. Workspace initialization is
reported, not hidden. Parent reports shell56593 terminal exit0, unchanged
10-second idle deadline, no native/viewer/science launch or H001/R0010 change.

Evidence is linked without duplicating parent inputs/output stores:

* ``.../carrier434-installed-20261002/cold438-public-source02.log`` SHA256
  357ed09958072575bb4fa46e41e2747e800af8711251c80e8325daddc54e59d1.
* ``.../carrier434-installed-20261002/cold438-stage-source02.log`` SHA256
  54bfd479c870ca451454db01dbd0dd8b2c2b4b25187d0780c805494cf6a8f6dd.

Original parent flag-parse and missing-enabled-source-binding failures remain
distinct. The original assisted5 UNKNOWN request is not replayed or reclassified.
Acceptance is source-inspection/MCP technical readiness only, not scientific
execution, biological results, a viewer, a global installation or a FULL audit.

Owned scratch (retained; no cleanup in this checkpoint)
------------------------------------------------------

``/home/ts/.cache/agent-scratch/dewey-436-real-compile-source-20261002`` contains
the failed synthetic source fixture and is preserved. Qualified synthetic
controls use separate ``dewey-436-real-compile-qualified-20261002``;
MCP boundary and bootstrap admission use ``dewey-436-mcp-boundary-source-20261002``
and ``dewey-436-bootstrap-admission-20261002``. These are source-test artifacts,
with final stdio controls in ``dewey-436-stdio-source-controls-20261002``;
not biological outputs. No foreign or active installed root was touched.
