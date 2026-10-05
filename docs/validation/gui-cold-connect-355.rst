Issue355: exact-child cold-start readiness
========================================

Named source-fix integration owner: Schrodinger/Codex.
OpenHCS isolated worktree: /home/ts/wt/openhcs-gui-cold-connect-355-20261001,
branch fix/gui-cold-connect-355-20261001, base c81963475.
Normal main merge: 7640fd951978c0901f7911d46414e06e8b886723.
Reviewed source checkpoint: 2c2c6ccb235cb68a78c79e569ed11822292b04fc.
Paired dependency source/gitlink: 23097e26c919b6c1b9621d009ee28f01626f1a65.
Drafts: https://github.com/OpenHCSDev/openhcs/pull/358 and
https://github.com/OpenHCSDev/ZMQRuntime/pull/13.
Subsequent receipt commits do not change either reviewed source checkpoint.
Later source continuation ffba8426c adds affinity/budget admission and removes
eager unselected kernel warming; see preparation-admission-355.rst for its
separate failures, current source tests, profile and installed-proof limits.
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
mirror, concrete consumer dispatch or speculative MI hierarchy was added.
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

Reviewed implementation and new-case check
------------------------------------------

60 production lines deleted, 16 added in the two OpenHCS files versus main7640.
The dependency deletes51 production lines and adds110, including the shared
mechanism and exact OS activity sampling. This is an authored source patch,
not a revision-checked NRA DSL transaction or a native equivalence proof.

IMPL-12: delete the OpenHCS readiness loop and its two forwarding adapters.
ZMQClient owns the sole typed readiness algorithm, optional total deadline,
observer composition and successful-ready hook. EndpointConnectionAttempt owns
the sole asynchronous cancel/join mechanism; ZMQClientService invokes it.
IMPL-13: EndpointProcess ABC owns startup_observer, ProcessIdentity owns the
exact-incarnation OS projection. Native leaves keep identity/native hooks only.
IMPL-1/3/4/5: no new string/type dispatch or half-owned process family.
MEMB-1/2/5: no process roster, declaration catalogue or record mirror is added.
The two-sample CPU map records changing OS measurements, not process authority.
TIME-1/3/9: delete the Boolean readiness compatibility hook, extra PONG probe
and separate deadline adapter. Caller/test signatures migrate in lockstep with
the dependency; there is no old-version fallback or replacement bootstrap.

The existing declared bases are ExecutionClient and EndpointCompatibilityClientABC.
Their independent execution/application-identity contracts remain combined by
the existing MRO; initialization and connect use cooperative super(). The
readiness algorithm resolves through ExecutionClient to ZMQClient. Dynamic
journal/cancellation observer instances remain runtime composition, not a new
capability roster or an invented MI layer. There are no new catalogues to derive.

New case: declare a new EndpointProcess leaf with identity, native exit/wait
and stop hooks. It inherits startup_observer without edits to ZMQClient,
transport or GUI consumers. DeclaredChild in the dependency tests exercises
this contract. The OpenHCS guard checks exact inherited readiness callable
identity, and its cold-clock test exercises the same ancestor with domain hooks.
Before promotion, a domain client implementing journal startup copied the
readiness procedure plus deadline adapter; now it declares two small hooks.

Source evidence and limits
---------------------------

Retained evidence is in docs/validation/issue355-evidence/:
openhcs-checkpoint.log (23pass, 2 pytest configuration warnings; 6.79s wall,
226284KiB peak) and openhcs-r0-checkpoint.json.gz/resources.txt (16.40s wall,
87332KiB peak). Original R0 has5161 projections, zero positive deltas; the
only nonzero delta is ZMQExecutionClient GodClassExcess -46.
Dependency receipt docs/validation/openhcs355-cold-start.rst in PR13 retains
35pass (1.03s, 43496KiB), final original R0 (3.89s, 48332KiB; 177 projections,
zero positive deltas) and the rejected +3 GodClassExcess checkpoint806faa1.
58 source tests total, not the full transport/native suite or installed GUI.
Three existing dependency execution-test signatures were migrated and linted;
the broader native execution suite was not run.

Original pinned R0: comms-ratchet-pinned-ui348-20261001 at
3b03785f45df2ef5dc62ba6aed99294192ecbb01, its existing Python3.14 interpreter
and read-only metaclass dependency path. It is not a copied detector.
NRA local full-payload output in PR13 is an intermediate ownership observation,
not final/global R1: no scan_status/omission witness or full dependency context.
Independent issue357/Dewey owns full-context qualification; no competing fix.

CPU advances and journal events refresh inactivity; liveness alone does not.
A CPU-busy infinite loop still needs cancellation or a total deadline. Silent
I/O-only work supplies no CPU advance. Typed ready PONG remains the sole
readiness witness. The15s configuration is unchanged. Parent must qualify
fresh installed GUI cold connect plus cancellation/inactivity/terminal controls.

Source-test recipe and artifact disposition
--------------------------------------------

Exact source interpreter:
/home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python.
Use owned OpenHCS and dependency src on PYTHONPATH, PYTHONDONTWRITEBYTECODE=1,
PYTEST_DISABLE_PLUGIN_AUTOLOAD=1, OPENHCS_CPU_ONLY=true, numerical thread pools1,
explicit owned XDG_CACHE_HOME. Kernel scope MemoryMax=512M, MemorySwapMax=0,
CPUQuota=100%; /usr/bin/time -v timeout60s taskset-c0 python-mpytest on
tests/unit/pyqt_gui/test_zmq_client_service.py and
tests/unit/test_zmq_execution_server_process.py, --noconftest -o addopts='',
-p no:cacheprovider and an owned --basetemp. Original commands/resource footers
are retained in the evidence logs. No parent root-conftest cleanup was invoked.

Initial missing native extension and two typed-fixture failures, default NRA
cache maintenance and early shared lock access are recorded honestly in PR13's
receipt. Those failed tool transcripts were truncated, not preserved in full.
The parent's private wheel supplied two extracted binary members for source
imports only, not an installation:
/home/ts/wt/openhcs-issue-batch-20260929/ui349-installed-20261001/wheels354-merged/openhcs-0.8.7-cp311-abi3-linux_x86_64.whl.
Extracted SHA256s: tabular7a6d9583e67dd76e4f9fe4cb3a4feb8a7462f816a8b862fdf9afbca8ad387de5;
granularitycce73671ef175c766196e7bbb6b972f6877db116853926c7e868a45cb9e23337.
These are not claimed identical to the unavailable earlier frozen binaries.

Cleanup completed after retaining logs/JSON and checking all owned test/audit
workers had exited. Removed only the two task-owned source-test symlinks
openhcs/core/_tabular_native.abi3.so and
openhcs/processing/backends/cellprofiler/_granularity_native.abi3.so, the exact
owned OpenHCS .validation directory, the exact owned dependency .validation
directory and the original generated /tmp/pytest-of-ts/pytest-994 fixture dir.
They contained regenerable fixture/cache/binary extraction output, not source or
parent evidence. Shared locks/caches, parent wheel, PR351 worktree,
frozen science, saved state and backing dependencies were not removed.
No native/UI slot consumed. Approximately50MiB of owned scratch reclaimed;
retained evidence is versioned here and in the dependency receipt.
