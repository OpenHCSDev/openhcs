Execution axis outcome and terminal status (#1005)
=================================================

Source boundary
---------------

Reviewed main 4d8c9c1 and the immutable H003fresh26 receipt0134.
The receipt contains an ERROR axis, partial nuclei artifacts, and a COMPLETE
transport record. No original scientific execution was replayed.

ExecutionResult owns each axis's status, error message and returned observations.
CompiledPlateExecutionResults owns the collection and parent diagnostics.
Previously four orchestration decisions independently recomputed aggregate
success. ZMQ ExecutionServer.run_execution independently treated normal return
from execute_task as success, without querying OpenHCS axis results. This is
IDEN-4 (completion name disagrees with outcome) and IMPL-5 (repeated decision).

The collection now owns is_success and require_success. Orchestration consumes
is_success; the OpenHCS server consumes require_success after runtime exports.
The original ZMQ lifecycle handles the resulting exception and publishes FAILED.
No competing error flag, UI status, result store or protocol format is added.
Successful axes and partial artifacts remain intact. Compile-only bypasses the
execution aggregate, as before. Empty-result semantics remain unchanged.

Consumer closure
----------------

Worker lanes return ExecutionResult values. Compiled plate execution derives
plate-step admission, viewer settling, progress success and orchestrator state
from the collection. The OpenHCS server exports observations before qualifying
terminal success. ZMQ lifecycle owns the terminal record; its status poller,
OpenHCS execution job service and GUI completion service consume that record.
Those views do not need local failed-axis overrides.

The existing audit.measures.measure_source parsed 64 files in orchestrator,
runtime, progress and vendored ZMQ execution before edits, with zero omissions.
This is scoped AST evidence, not a completed global NRA proof. After migration,
the expanded family (including agent and actual pyqt_gui roots) parsed 215 files
with zero omissions. Source reads confirmed ExecutionJobRecord.status derives
status/errors from the terminal response; the GUI completion callback parses
that same terminal status into TerminalExecutionStatus.completion_payload.

Crossings and acceptance
------------------------

#140 / draft PR160 addresses a fork-worker exception whose waiter did not
terminate. That documentation-only investigation is not this implementation.
Both share the existing lifecycle publication path; no lifecycle source is
changed here. PR981 Gaussian axes and PR1004 neurite rooting are disjoint.
Planck explicitly confirmed no outcome/status claim on #1005.

The initial source pytest collection could not import TiffPhotometric from the
foreign PolyStore checkout. The reused interpreter's baseline installed wheel
also lacks it. Neither package nor dirty submodule has been changed.

Focused checks passed 62 tests in 6.60 seconds using the existing receiving26
dependency target and reused interpreter. Source package search includes this
branch; dependency imports use the qualified installed target, not the foreign
externals. Tests cover original server run_execution and terminal publication
for failed/all-success aggregates, export ordering, and retained successful
axis results. Controlled worker responses are not installed public-MCP proof.

Pending: a
distinct tiny registered public MCP failing-axis and all-success pair on an
owned reused engineering route coordinated with Dewey. Original science,
UNKNOWN inputs and active blind-author packages remain untouched. Hosted CI
is deferred. Do not merge or close #1005 as live-verified yet.
