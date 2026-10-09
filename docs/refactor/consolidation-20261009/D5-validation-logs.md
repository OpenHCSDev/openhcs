# D5: Committed validation logs

**Head audited:** `openhcs` `main` at `0be261732` (#1152). **Rules:** [00-RULES.md](00-RULES.md). **Step 1.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* none.

## What is wrong

**`docs/validation/` holds 160 MB in 1,137 tracked files: run logs, ratchet JSON and source-tree listings from finished agent work. Most are referenced by nothing (fake work: validation logs committed to the tree).**

`paper/`, `docs/` and their scripts reference 85 distinct paths under `docs/validation/`. Those are evidence the manuscript or documentation cites.

## Target

- Keep every file that a tracked file outside `docs/validation/` references by path. Also keep any file a kept file links to, transitively.
- Delete everything else in one commit. It remains in git history.
- Do not touch `benchmark/results/`: the manuscript's benchmark claims derive from those records through checksum receipts.

## Guards

- A test asserting that every path referenced under `docs/validation/` from `paper/` and `docs/` exists.
- A `.gitignore` rule for `*.log` under `docs/validation/`, so new run logs stay local.

## Done when

Only referenced files remain, the paper builds (`paper/build_paper.py build`) with every supplement link resolving, and the guard passes. Report the size before and after.

## Dispatch

> **`validation-logs`:** Complete surface D5 per `docs/refactor/consolidation-20261009/D5-validation-logs.md`. Decision Q4 applies. Build the paper before opening the PR.
