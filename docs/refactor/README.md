# OpenHCS refactor

Plans for removing OpenHCS's structural debt, written against `main` at `c86f562e`. **Put this directory in the repository at `docs/refactor/`,** so every agent's worktree has it.

## Read in this order

Read [OWNER-OVERRIDES.md](OWNER-OVERRIDES.md) first. It preserves the owner's
latest explicit no-wait-for-hosted-CI rule without reducing any surface scope.

1. **[00-RULES.md](00-RULES.md): binding on every agent.** OpenHCS is published, so it separates external contracts from internals, and it makes CellProfiler parity the gate before any merge.
2. **[01-INDEX.md](01-INDEX.md):** the evidence, the surfaces, their order, and four decisions.
3. **Surface files,** written one at a time, just before dispatch. The first is [R0](R0-stop-the-inflow.md).

## What the owner does

Answer D1 to D4 (each has a default), and approve R0's CI changes.
