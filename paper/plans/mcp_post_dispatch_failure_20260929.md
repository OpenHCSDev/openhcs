# Preserve an established MCP session's failure boundary

Owner: OpenHCS blind-analysis integration coordinator. Issue #178.
Audited main abb8b6116b14e4a7d3dbe84bb1db4a5eaea61c0c.

The live compile reached runtime :5791 and completed, but an exception escaped
the resident session body. `open_mcp_dev_session` caught it as if connection
establishment failed, attempted another daemon launch and yielded a second time.
The caller received `generator didn't stop after athrow()` instead of the
original error. It lost the ordinary compile-job receipt; public runtime status
recovered the accepted compile without resubmission.

## Ownership and required answers

Transport establishment belongs to `open_mcp_dev_session` and its existing
`McpDevTransportAuthority`; actual protocol I/O belongs to `McpDevSocketSession`
and inherited `McpDevStdioSession`. After yielding a usable session, the caller
owns the operation and its uncertain side effects. A post-dispatch error MUST
propagate unchanged and MUST NOT cause another transport or server launch.
Connection/initialization failures before yield retain existing fallback policy.
No wire schema, registry, declaration roster or durable session changes.

The bounded NRA original-ClassDef census covers dev_client_core.py, dev_client.py,
and socket.py: 39 original classes, 39 unique compact-family joins, zero OPEN
syntax rows. All classes, not only matched transport names, were retained as
alternative-owner evidence. Global detector/R1/effect-equivalence proof remains
OPEN; this is an authored behavioral repair, not an NRA-equivalent migration.

The specific identity defect resembles IDEN-1/IDEN-7 in the refactor-audit
catalog: the catch boundary answers both "did establishment fail?" and "did a
dispatched operation fail?", although those require different recovery. The
existing `AsyncExitStack` standard-library owner admits the session before the
yield, so only the former enters fallback. No new class or phase-tag switch is
needed. A new body exception requires no added roster or consumer branch.

## Acceptance and scope

Parametrized regression preserves exception identity, one initialization and
one teardown for OSError, TimeoutError and protocol failure after dispatch;
fallback/spawn are forbidden in those cases. Verify pre-yield fallback separately.
Verify the installed client against the actual resident JSON-RPC server:
health handshake, one readonly tool call, intentional caller failure, and a new
healthy handshake to the same server with no startup attempt.

This patch is NOT a cold-start speed or compile-reuse fix. #179 owns observation
options changing reuse signatures. #165/#166 and #174 own catalog/docstring costs;
remaining MCP liveness/preparation timing under #178 stays explicit.
