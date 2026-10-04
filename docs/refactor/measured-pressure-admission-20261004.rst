Measured pressure admission
===========================

The existing operations/resource-check.sh is the admission owner. A numeric
full_memory_psi_max_percent previously turned any10/60/300 full-stall sample
above1% into exit77 for cold/large admission, independently of available host
RAM, current family usage and operation size. This is our policy, not a user
hardware requirement (IDEN-7: check wider than the requested work).

Delete that numeric decision, its required configuration read and its future
projector/publisher field. Preserve exact pressure windows, host MemAvailable,
family charge/swap/RSS/PSS, original operation modes, desktop reserve and
missing/malformed telemetry rejection. The operator sizes incremental work,
reduces workers or delays expansion for actual pressure; no replacement cutoff,
override, poller or admission owner is introduced (AGENT-7, TIME-1).

Read/consumer closure: resource-check.sh; successor-program.jq;
project-program.sh; AUTHOR-PACKET.rst; README.rst; both existing publication and
resource-admission shell controls. Search the tracked family for the removed
field. Remaining occurrences are deletion and deliberately old fixture input,
not another reader or a live limit. No Python declaration/consumer changes;
Python AST tools do not parse Bash/JQ. Semantic shell/JQ inspection, syntax
checks and original entrypoint controls supply that coverage, not an AST claim.

Reuse: previously owned627 basicpy-readiness checkout on a new normal branch
from current main. It was tracked-clean excluding foreign submodule worktrees,
with no untracked files and no current FUND source/operation borrower; only
the diagnostic shell itself held its root cwd. All active RUNs resolve to
immutable receiving04/07 and the copied next-bbbc00788 harness operations.
Preserve foreign gitlinks and the input-preparation checkout's five dirty files.

Operational scope: future owner family only. Original engineering receiving01
exit77 was before MCP dispatch; a later receiving02 passed and owns the active
eded089b incarnation. Neither is replayed. Current immutable science/engineering
operations, FUND and their original refusal journals are not rewritten.

Qualification is recorded separately after coherent source implementation.
Source tests do not claim biological acceptance or public native success.
