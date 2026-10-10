# Coordination

**Rules:** [00-RULES.md](00-RULES.md). One agent per surface, each in its own worktree. The session that wrote this package reviews and merges each PR; there is no separate coordinator agent.

## Agents and when they start

| Agent | Surface | Starts |
|---|---|---|
| dead-processing | D1 | step 1 |
| dead-core | D2 | step 1 |
| product-boundary | D3 | step 1 |
| equivalence-out | D4 | step 1 |
| validation-logs | D5 | step 1 |
| capabilities, renderers, binding-editor, backends, cp-backends, progress, viewers | C1 to C7 | step 2 (C2 after C1 merges) |
| payloads, then artifacts and callables; measurements, sources, debug, execution, contracts | K1 to K8 | step 3 |
| placement, packages | P1, P2 | step 4 |

## Status

One line in the PR description, updated only when state changes. Deletions first, because deleting is the point:

    D1 · PR #1160 open · guards 2/2 · production −1,180 +12 · tests −310 +20 · next: review

## Cutover

Runtime state (function registry cache, compiled plans, metadata caches, viewer sessions) resets on install; restart the GUI, execution server and viewers after each merged step. Durable state (saved pipelines, plate configs, preferences) changes only under a decision: Q3 makes old GroupBy pickles fail loudly instead of migrating.

## Decisions

See [01-INDEX.md](01-INDEX.md#decisions). Every question has a default; "accept defaults" is a complete answer.

## The prompt addendum

Append to every surface agent's prompt, with `{{SURFACE}}` filled in:

> **Your assignment: refactoring surface `{{SURFACE}}`.** Read, in order: `docs/refactor/consolidation-20261009/00-RULES.md`, `01-INDEX.md`, `02-SHARED-ABSTRACTIONS.md`, then your surface file. The rules override everything else, including your own instinct to be cautious.
>
> In your surface's files, refactoring is your task. **Delete** legacy code, compatibility code, converters, dead code and tests of deleted code. **Never** add a fallback, an alias, a converter or a "for now" path. **Finish completely:** your surface is done when its guards pass with zero exceptions.
>
> Re-verify your surface file against current `main` first; where it is wrong, correct it in your PR and say what changed. Before deleting any module, check registration by discovery, entry points and launches by name.
>
> Tests protect behaviour, not structure. Test churn never blocks the refactor: rewrite broken tests as fewer family-level tests. Delete tests of what you deleted. No golden files for our own formats. Never weaken an assertion. The 30-workflow CellProfiler parity corpus must stay green.
>
> Run heavy commands with `nice -n 19`. Work on a branch named `refactor/{{SURFACE}}-<topic>`, open a PR against `main`, and do not merge. Report production lines (Python under `openhcs/`) and test lines deleted and added.
