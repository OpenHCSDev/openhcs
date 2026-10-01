Issue327 source resource ledger
==============================

Owner: SOURCE-ONLY issue327 implementation agent. Parent owns integration.
Source worktrees: /home/ts/wt/openhcs-metadata-namespace-327-20261001 and
/home/ts/wt/polystore-metadata-namespace-327-20261001.
Disposable scratch: /home/ts/.cache/agent-scratch/metadata-namespace-327.
Purpose: tiny synthetic fixtures, pytest XML/logs and bounded source evidence.
Limits: one CPU, 512 MiB combined process RSS, 256 MiB scratch, 60s per shard.
Initial resource guard: warning, 8.5 GiB home free, 16.5 GiB RAM available,
8.9 GiB historical swap used. The owner's 20 GiB disk threshold is warning-only;
the bounded scratch maximum is less than available disk. No science/runtime lock,
installed package, GUI/MCP, provider, interpreter or environment changes.
Archive terminal command output in this worktree before removing owned scratch.

Own read-only guard-tool worktree:
/home/ts/wt/metadata-namespace-327-audit-tool, pinned3b03785f45df2ef5dc62ba6aed99294192ecbb01,
3.1 MiB sparse checkout. Existing system3.14.7 executes the unchanged original
CI tool; product/native test processes use3.12. Source native build outputs are
openhcs/core/_tabular_native.abi3.so and
openhcs/processing/backends/cellprofiler/_granularity_native.abi3.so in this own
application worktree (376,344 bytes total); never installed/copied externally.
Final scratch is approximately4 MiB, well below256 MiB. All shards are terminal;
peak observed process-group RSS355.73 MiB, including a retained initial guard
failure, and longest shard22.03s. Archive the raw errors and results, then remove
only this owned scratch, source-native build outputs and clean guard-tool WT.
Keep both implementation WTs and their seven source dependency WTs persistent.

Cleanup completed after terminal-process check. Fresh extraction and byte-for-byte
comparison verified original negative log/XML, current unresolved-source XML and
both complete structural-guard logs before deletion. Archive SHA256:
05b24739c81fbdc86c3dbc9e96f45e1764a5f50ffe946953271c386df68c8dfa.
Owned scratch, two reproducible native build outputs and clean tool worktree are
removed; all implementation source, parent original errors and saved history
remain untouched. Rebuild the two source extensions with the recorded standard
setup.py command before rerunning application source tests in this own WT.
