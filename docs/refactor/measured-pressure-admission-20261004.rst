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

Qualification after coherent source implementation: original shell resource
admission control01 and funded-publication control01 terminal0. High samples
4.82/1.09/.23 pass both full/replacement when desktop space is available; low
RAM startup, malformed RAM/pressure, dead/foreign clients, missing custody,
expired clocks, overlapping roots and duplicate receipt/publication still
reject. Projector and publisher delete the old field. Existing provider-free
recorded-client child42/lifecycle control passes, no new native/provider run.

Actual current original FUND/engineering671 full observation
psi_source_accept01 terminal0: MemAvailable12.698GiB, fullPSI .01/.55/.35,
measured common charge9700007936B/swap947216384B and actual family RSS/PSS.
No configured PSI override, admission bypass, new MCP request or another client.
This exercises the changed production entrypoint against real host/family and
existing granted custody; it does not install this source into frozen clients.
All original refusal/runtime science evidence remains unchanged.

Evidence paths: issue-batch/engineering-pressure-policy-20261004-control01.log,
engineering-pressure-policy-20261004-publication01.log,
engineering-pressure-policy-20261004-live01.log and ast-coverage01.json in
engineering-pressure-policy-20261004. The existing overlay reports zero Python
sites in the Bash/JQ-only owner root, not Python structural or behavioral proof.
Shell syntax/diff checks pass. No biology or public-native acceptance claimed.
