Issue355: exact-child cold-start readiness
========================================

Named source-fix integration owner: Schrodinger/Codex.
OpenHCS isolated worktree: /home/ts/wt/openhcs-gui-cold-connect-355-20261001,
branch fix/gui-cold-connect-355-20261001, base c81963475.
Original installed failure remains the predecessor, not a retried acceptance.
Authoritative reproducer:
/home/ts/wt/openhcs-issue-batch-20260929/UI349-COLD-CONNECT-DEFECT-20261001.rst.

Diagnosis and ownership
-----------------------

PlateManager.ensure_execution_server -> batch workflow.ensure_server ->
ZMQClientService.connect -> EndpointConnectionAttempt.connect(ATTACH_OR_START)
-> ZMQClient._connect_locked -> ZMQExecutionClient readiness observer ->
TransportEndpoint.wait_for_ready_response. The service runs connect in its
existing executor, not on the GUI event loop. OpenHCSZMQConfig supplies15s.
TransportEndpoint uses an inactivity deadline refreshed by poll_activity.
The domain observer reports only newly appended journal entries. The failure
log's final entry is Discovering registered callables at06:25:48.421, followed
by failed connect at06:26:08.479, including stop/cleanup. A blocking cold
discovery operation can execute without another journal entry. Original
explicit async spawn/observe kept one exact child and reached ready in109s.

Required relation: silence between domain progress messages is not proof of
inactivity or process termination. Exact-child work may refresh inactivity,
but never proves readiness. Only the original typed handshake does that.
Cancellation, failed startup, exact exit and explicit operation deadlines
remain terminal; a truly inactive child remains bounded by the same budget.

IMPL-13/IMPL-12: generic activity/readiness belongs to existing ZMQRuntime
process/startup owners, not another GUI bootstrap or process registry.
Small OpenHCS hooks supply its existing journal. No timeout increase, state
mirror, concrete consumer dispatch or speculative MI hierarchy is planned.
No persisted user format changes. Runtime-only observations are disposable.

Crossings and claims
--------------------

ZMQRuntime PR6 (945e80248f375e834f1b993ed133268445e5efce), named H003/Codex
waiter worker, owns execution/wait_policy.py status admission and its tests.
Its malformed execution-status scope is not startup/readiness; do not touch
those files or claim that PR's original issue140 hang is fixed.
Parent PR349 owns dev-client commanding/core/rendering; none are in scope.
PR351 and the frozen scientific trial stay immutable.

Validation boundary
--------------------

Source-only checks: oneCPU/thread pools1, kernel512MiB/no swap, outer60s,
provider-free synthetic lifecycle fixtures. No native/MCP/UI launch, lock
acquisition, installs, downloads, Fiji, science or backing-environment writes.
Parent retains serial installed/live ownership until exact slot handoff.
Fresh cold installed GUI plus ready/cancel/stall/terminal controls is mandatory
before readiness can be claimed. Source passing is not installed acceptance.

Startup resource check: RAM21.0GiB and home10.5GiB free; helper returns warning2
for disk below advisory20GiB and swap usage13.6GiB. These exceed actual startup
RAM11GiB/disk2GiB admission; only one bounded source process is planned.
