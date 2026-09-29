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

Focused provider-free pytest passed: four tests, 105 deselected, 2.11 seconds.
The first attempted invocation failed to create its missing scratch parent (one
capability test passed, three fixture-setup errors); creating that owned parent
and rerunning the same cases passed without changing product assertions. The
earlier lock-gated attempt returned 75 and did not start tests. These small checks
do not start another GUI/JVM or run scientific data. Live MCP acceptance remains
pending while Euler owns the substantial validation slot. This is not an
installed/readiness claim; do not close the issue on source tests alone.

## Released-slot real MCP checkpoint

The previous analysis owner saved its rejected candidate and closed its owned
viewer/client/MCP before this checkpoint. A fresh actual stdio MCP server
projected the truthful capability metadata. Both denied directories (with and
without preexisting metadata) returned `agent_path_policy_rejected` and their
recursive byte hashes were unchanged. A generated single-field ImageXpress
fixture was preserved after the allowed cold inspection hit the unchanged
10-second transport limit; only its generated TIFF/HTD files existed at closure.
No scientific execution was submitted or replayed.

That cold path forced full function-catalog preparation in
`InProcessCompileInspectionGateway`, despite `PipelineDocumentAuthority` already
normalizing each callable through `FunctionStepTransportAuthority` and the
registry's declaration-local metadata. Delete that redundant initialization;
the existing document, compiler, registered-callable and function-reference
owners remain authoritative. No new registry, special-case roster or timeout
increase. The same real MCP inspection then completed in 1.19 seconds with
one axis, one step and one virtual source file, and reported the authorized
metadata creation. This is the cold-inspection follow-up to #178, not a global
latency or numerical-accuracy claim.

A real one-field gateway regression rejects any full-catalog preparation while
compiling the registered NLM declaration. The first two new regression assertions
confused the summary count with the core projection's relative/full-path lookup
aliases. Use the existing canonical artifact-plan projection to count files;
the successful compile assertions and catalog prohibition remain unchanged.
The corrected focused suite passes: nine tests, 101 deselected, 6.00 seconds;
two plugin-disabled pytest configuration warnings. The full real MCP sequence
then passes with all thirteen QA rules, source-identical preprocessing guidance,
truthful capability metadata, both unchanged denied directories and the allowed
one-axis/one-step/one-file plan. Source pass is not installed acceptance; that
check follows publication. No scientific NLM execution or accuracy is claimed.
