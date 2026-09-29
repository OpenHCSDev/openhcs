# Artifact-plan write authority

Owner: current OpenHCS coordinator. Issue #211. Base: remote main
`98d9b9d233b1278175136acc1d76185337f6ed1d`.

The actual compile-inspection gateway initializes the real orchestrator, which
can persist metadata and locks. The agent service admitted only read access,
and the capability declaration advertised no mutation. H003 observed both
generated metadata and a lock in its original read-only input directory.
Original brief/image hashes are preserved; later trials use staged inputs.

This patch uses existing `AgentPathPolicy.assert_writable` before initialization,
and puts mutation/side-effect metadata on the existing capability declaration.
Catalog projections and MCP exposure remain derived from that declaration.
No alternate policy, registry, compile implementation, input-copy fallback or
configuration switch was introduced. Existing path-policy error ownership stays
unchanged.

This is a focused authorization repair, not genuinely non-persisting compilation
or a global NRA proof. The read-only inspection promise cannot be restored merely
by relabeling persistence. Other write destinations and workspace mechanisms
need their own authorization review. This checkpoint specifically prevents the
observed forbidden plate write and makes the current operation's exposure honest.

Regressions cover denied input roots with and without existing metadata, no
gateway invocation/no file changes, declaration-owned side effects, and admitted
writable workspace compilation. The denial fixture uses the existing gateway
test boundary; live acceptance must also call the real MCP entrypoint with
separate read/write roots and verify unchanged directory contents and original
hashes. AST parsing/order and diff checks are preliminary evidence only.

Focused pytest and live MCP acceptance are pending the shared validation slot
while Euler performs H003. This is not an installed/readiness claim. Do not close
the issue or merge on AST evidence alone.
