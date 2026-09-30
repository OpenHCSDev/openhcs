PR256 resumed source checkpoint: reserved-child takeover
========================================================

Explicit new source-only authority after account-switch pause. The original
``PAUSED-ACCOUNT-SWITCH-20260930.md`` is retained unchanged. S1 remains BLOCKED;
no original failed/UNKNOWN input or native attempt was replayed. This is not
resumption of the broader archive goal.

Exact pair and normal integration
--------------------------------

OpenHCS main ``c42d9bf5d83249975618c1d1c8dcfd3819a7b036`` was normally merged
into the existing PR256 branch at ``5b330a7b3e77a23af4b1468421b3734ac75256b9``.
No parser/UI-owner file was edited beyond retaining those incoming main commits.
The only new dependency production correction is native commit
``0ca331a1c197e26656965193d6502e7a3c298808``. Its reviewed receipt head
``112c240464df6e81c25b0f97d2b1376d43bbbbc8`` was normal-pushed to existing PR9
and independently matched by ls-remote BEFORE adopting this gitlink.
Native main2aa6d21c (including ACK3374 and viewer7) remains an ancestor.
ArrayBridge409, metaclass-registry448cdf0, PolyStore1209068 and all other pins
are unchanged. No second worktree/environment/launcher or installed cutover.

Concrete source fix and new-case proof
-------------------------------------

Ordinary ``connect()`` could kill TCP data/control port owners after failed
attachment but before checking pair startup reservations. Exclusive startup
already had the correct nominal pair owner. The preceding tests intercepted
occupancy as false, missing the bind-before-ready case.

The fix consumes existing ``TransportEndpoint.has_live_startup_owner(config)``
under both held locks BEFORE takeover; healthy attachment stays allowed.
Original transport record decode/release, exact PID+creation-time identity,
inode retention and post-spawn uncertainty remain untouched. No new registry,
process store, default/mode resolver, codec, type/string switch, fallback,
automatic replay, timeout or size-only helper/mixin.

Applicable current NRA/archive pattern review: IMPL-13 weak occupied-connection
rigour is closed through the same startup owner; IDEN-8 exact incarnations and
unknown liveness are retained; BOUND-2 original malformed-record decode fails
closed; IMPL-12/AGENT-6 no duplicated pair procedure or forwarding extraction.
Native receipt ``docs/validation/issue251_reserved_child_takeover_20260930.rst``
contains the owner/new-case witnesses and exact original packaged comparison.
This is not full catalog/global NRA coverage.

Actual test receipts
--------------------

First pre-fix command preserved six failures/six passes, but the accompanying
path assertion failed on mis-cased PolyStore/ObjectState directories. It is
NOT credited as all-nine-package source authority. After correcting path case,
find_spec asserts all nine packages originate inside this own tree. The
unchanged pre-fix cases again failed at six intercepted kills: current or
unknown-live reservation on either address, plus partial record on either
address. Corrected pre-fix receipt:6 failed/6 passed/22 deselected,0.99s;
process1.23s/53548KiB/exit1. Both original XML/log/resource receipts retained.

At OpenHCS5b330a7b3e plus native0ca331a, exact own root plus all eight child
src paths, existing Python3.12 ``-B``, thread1, plugin autoload disabled, shared
Fiji cache/downloadfalse, original30s shell bound: **197 passed in5.39s, zero
skips/deselections**, process6.20s/264612KiB/exit0. ``after-tests.xml`` and
``after-tests.log``/``after-resources.txt`` accompany this receipt. Two warnings
are disabled asyncio-plugin options. The original187 controls plus10 new cases
cover the existing typed bootstrap service/client route, native lock/reservation
rollback/close, transport projection and merged viewer-state source seam.
Process/network/native boundaries are controlled; records and portalocker
locks are real. Controlled visualizers plus one short lock-probe thread are
not an actual viewer. No native/MCP/JVM/GUI/science/provider allocation.

Authenticated original agent-comms ratchet on WHOLE native root2aa6d21c ->
production0ca331a: **PASS188 metrics/no positive deltas/client excess delta-1**,
process4.79s/47992KiB/exit0. Native JSON/resources are published in PR9. Earlier
paired +142 failure remains retained, not relabeled. Existing debt remains;
not full NRA/R1/all-detector or performance proof. The prior OpenHCS5159-metric
pass keeps its original7d0ce5->9cb7703 source; no freshc42d root-pass claim.

For reproducible source checks, the executed shard was:

.. code-block:: text

   tests/unit/agent/test_owned_runtime_bootstrap.py
   tests/unit/test_zmq_execution_server_process.py
   tests/unit/agent/test_agent_services.py::test_execution_connection_spec_owns_zmq_endpoint_projection
   external/zmqruntime/tests/test_owned_startup.py
   external/zmqruntime/tests/test_owned_close.py
   external/zmqruntime/tests/test_endpoint_ownership.py
   external/zmqruntime/tests/test_startup.py
   external/zmqruntime/tests/test_viewer_state.py

Run with ``--noconftest -o addopts= -q`` and the explicit own root/child paths;
never use the frozen installation as this source test authority.

Ownership, cleanup and remaining live gates
------------------------------------------

Current correction writes ONLY native ``client.py``, ``test_owned_startup.py``,
native receipt/ratchet evidence, OpenHCS gitlink and owned receipts/PR bodies.
Parent owns PR215 main-flow/primary_objects/diagnostics and ACK issue10; these
files were not edited. Published waiter6, viewer7 and ACK12 claims were checked:
disjoint; ACK12 is documentation only. Existing bootstrap claim includes
TransportEndpoint from the preceding checkpoint, but no shared transport/config/
message/ACK/viewer file changed in this correction. Broader archive author is
still unknown; no coordination agreement or whole S1-S8 completion invented.

Resource guard warned on home19.9GiB and swap9.5GiB (RAM17.1GiB). The explicit
source-only continuation used no validation lock or heavy/parallel allocation.
Fermat's original science slot, frozen OpenHCS c42d/managed skill, protected H002
and foreign endpoints were untouched. All tool/test handles here are terminal.
After terminal tests and empty lsof, removed ONLY2.7MiB rebuildable new test
scratch (before-pytest/before-corrected-pytest/after-pytest); receipts retained.
Original native-attempt01/02/03 artifacts and untracked paths remain unchanged.

Source pair is ready for parent integration REVIEW, not live activation. Parent
owns merge/install and next serialized affected installed/native journey.
Valid-volume four selections with first/chained complete image/labels/CSV/all
five source-address fields/ROI and main+named projection inventory remain
unaccepted, as do additional cross-process uncertainty cases. No attempt04,
installed proof, issue251/257 closure or startup-performance optimization claim.
Stop here until an explicit source review defect or native slot disposition;
never replay original attempts or resume BLOCKED S1 implicitly.
