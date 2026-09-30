# PR256 / paired ZMQ9 pre-spawn rollback

Fresh direct authority fixes the parent-reviewed no-child reservation leak;
the separate S1/refactor goal remains BLOCKED. Parent owns integration/live.
OpenHCS normally merged current main295e into d915da7b7; dependency main was
already integrated. Existing PR6/7 published write sets are disjoint.

Original reproducer and receipt remain unchanged:
/home/ts/wt/openhcs-issue-batch-20260929/REVIEW-256-PREBIND-REPRO-20260930.py
/home/ts/wt/openhcs-issue-batch-20260929/pr256-prebind-review-20260930/receipt.json
They proved TimeoutError,spawn_calls0 and two live invoker records at9a93bbe.
No replay or contact with any scientific/native runtime occurred.

Correction is solely in paired ZMQRuntime client.py/transport_modes.py and
test_owned_startup.py. Under both canonical locks, the no-spawn section releases
only an exactly matching provisional ProcessIdentity, truncating the existing
inode. Unknown/changed/child ownership stays intact. Spawn is outside rollback;
no automatic startup/shutdown replay or larger deadline. New-case witness:
the same original transport ancestor serves both TCP and IPC without a roster,
codec subclass, new launcher or reservation registry (IMPL-13,IDEN-8,BOUND-2).

Existing Python: /home/ts/code/projects/openhcs/.venv/bin/python. Explicit
PYTHONPATH points at this tree and its recorded external src directories;
imports verified for OpenHCS,ZMQRuntime,metaclass-registry,python-introspect,
PolyStore,ObjectState,pycodify,pyqt-reactive and arraybridge. CPU thread limits1.
No package install, native build, download, ImageJ/JVM/GUI/MCP startup or lock slot.

Executed dependency command: python -B -m pytest --noconftest -o addopts= -q
tests/test_owned_startup.py tests/test_owned_close.py, timeout60s. Result45 passed
in0.40s; process3.68s/362564KiB RSS/exit0. Initial44pass/one fixture-path failure
is retained separately. Source cases preserve exact lock inodes and actual
flock exclusion, zero spawn before rollback, partial-record fail-closed behavior,
post-spawn child handles and one source fixture spawn attempt without retries.

Combined command matches the existing nine-file paired source shard documented
in runtime_bootstrap_20260930.md, timeout60s, -k 'not actual_mcp_onboarding'.
Result136 passed,2 actual-MCP cases deselected in10.64s; whole process14.18s,
432464KiB RSS,exit0. No claims of native cross-process or installed acceptance.

Guard before execution: /home27.9GiB,RAM14.0GiB, historicalswap15.6GiB warning
only (existing exception); no non-swap warning. Owned scratch:
/home/ts/.cache/agent-scratch/pr256-pre-spawn-rollback-20260930 (2.4MiB after tests).
Receipts are retained here before scratch cleanup. No live source handles remain.

Remaining: paired review/merge by parent, serialized actual bootstrap -> prepare
-> register -> compile/execute -> identity-proven close, then installed user-path
acceptance. Prior R0 packaged ratchet failure on this feature's god-class growth
is retained separately; this correction does NOT claim a passing own-PR ratchet
or global structural audit. Existing native/installed/uncertain receipts stand.
