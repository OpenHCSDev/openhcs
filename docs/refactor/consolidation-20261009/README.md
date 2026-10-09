# OpenHCS consolidation

Plans for deleting unneeded production code and giving each owned concept one owner, across `openhcs/`. Written against `openhcs` `main` at `0be261732` (#1152), from a debt census, an overlay of slop patterns and four verified subsystem maps. The plans exist for steps 1 to 4; surface files exist for step 1 only and are written for later steps just before dispatch.

## Read in this order

1. **[00-RULES.md](00-RULES.md): binding on every agent.**
2. **[01-INDEX.md](01-INDEX.md):** evidence, surfaces, order, crossings, decisions.
3. **[02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md):** the two new mechanisms more than one surface uses.
4. **[03-COORDINATION.md](03-COORDINATION.md):** agents, status, cutover, the prompt addendum.
5. **Surface files:** [D1](D1-dead-processing.md), [D2](D2-dead-core-runtime.md), [D3](D3-product-boundary.md), [D4](D4-equivalence-tooling.md), [D5](D5-validation-logs.md).

## What the owner does

Answer the decisions in the index (defaults apply otherwise), approve merges, restart the GUI and servers after each step. Nothing else.
