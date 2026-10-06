# Canonical exclusive bootstrap and exact owned lifecycle (OpenHCS251)

Extends existing ZMQClient startup/lifecycle owners: explicit local empty-pair
startup, ProcessIdentity capture, both-address pre-bind reservations under the
existing startup locks, post-spawn uncertainty handle, and identity-proven close.
No new launcher, registry/future, warmup, foreign takeover or RPC replay.

FORCE distinguishes listener disappearance from exact process exit. The original
ProcessIdentity owner uses one bounded TERM/KILL/wait budget. GRACEFUL clears
workers and keeps the server. Owned close requires both native reservations and
incarnation-bound admission before native worker mutation. IPC cleanup retains
its original stale-address owner. Original5993 disposition remains parent-owned.

## Reviewed no-child reservation rollback correction

Parent's9a93bbe canonical-lock reproducer proved zero spawn calls on deadline
expiry after both provisional invoker reservations, but retained a live invoker
claim that stranded future independent startup. Original receipt is preserved.
Client28d9ed6 rolls back only provisional publication/deadline/cancellation before
spawn, under both held locks. TransportDeclaration releases exact ProcessIdentity
matches by truncating the existing inode; it never unlinks a flock identity.
Unknown/changed/child records are untouched; spawn exceptions and child-publication
uncertainty retain claims/handles without automatic startup or shutdown replay.

Thirteen new source cases cover deadline expiry, second publication failure
before/after complete write, partial unknown write, cancellation, actual held-lock
exclusion and inode retention, explicit independent-start admission after rollback,
post-spawn uncertainty and TCP/IPC inherited release. No foreign record is cleared.

**45 dependency source tests pass0.40s**, whole process3.68s/362564KiB RSS/exit0.
**136 combined paired source tests pass10.64s**,2 actual-MCP cases deselected,
whole process14.18s/432464KiB RSS/exit0. Earlier123-pass and initial fixture-path
failure captures retained. Sources verified with the existing shared Python.
No native/MCP/JVM/GUI/science launch, installation, download or runtime replay.

Paired [OpenHCS256](https://github.com/OpenHCSDev/openhcs/pull/256), references
[issue251](https://github.com/OpenHCSDev/openhcs/issues/251), and
[metaclass-registry1](https://github.com/OpenHCSDev/metaclass-registry/pull/1).
[Owner/test receipt](https://github.com/OpenHCSDev/ZMQRuntime/blob/feat/exclusive-endpoint-bootstrap-20260930/docs/validation/issue251_bootstrap_20260930.md).
PR6/7 files remain untouched; IMPL-13/IDEN-8/BOUND-2 reviewed at original owners.

Remaining: parent paired review/integration, serialized synthetic bootstrap ->
preparation READY -> registration -> compile/execute -> exact exit, then actual
installed user-entrypoint validation. No Closes251 or global NRA/ratchet proof.
Parent retains integration/live ownership while Dirac's frozen science runs.
