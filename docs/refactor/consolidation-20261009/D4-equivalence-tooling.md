# D4: Equivalence tooling out of core

**Head audited:** `openhcs` `main` at `0be261732` (#1152). **Rules:** [00-RULES.md](00-RULES.md). **Step 1.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* none.

## What is wrong

**`core/equivalence/` (11.2k lines) and `core/runtime_equivalence.py` (3.3k) mix two roles in the product package: measurement semantics used at runtime, and comparison tooling that only verifies OpenHCS against native CellProfiler (AGENT-8).**

- Production modules outside the package import `policy` (11), `keys` (5), `measurement_features` (4), `relationships` (2) and `cells` (1). Those importers are 18 modules on the CellProfiler measurement path, including `core/artifacts.py`, `core/measurement_row_materialization.py`, `interop/cellprofiler/measurement_dialect.py` and `processing/backends/cellprofiler/granularity.py`.
- Nothing outside the package imports `comparison`, `report`, `outputs`, `images`, `arrays`, `tables`, `measurement_rows`, `measurement_facts`, `measurement_requirements` or `object_label_measurements` directly. Some of them may still be reached through the production-imported modules.
- `runtime_equivalence.py` has three importers outside it. `processing/backends/cellprofiler/zernike.py:38` takes tolerance classes from it; read the other two.

## Target

1. Compute reachability. Start from every production module outside `core/equivalence/` and `core/runtime_equivalence.py`, and follow module-level and function-level imports into the package. Whatever is reached stays. Do not count `TYPE_CHECKING` imports.
2. Move every unreached module to `benchmark/equivalence/` (decision Q1), together with the parts of `runtime_equivalence.py` that production does not reach. Move the tolerance classes zernike needs to the module that owns measurement policy (`core/equivalence/policy.py` today). Update imports in `benchmark/`, `scripts/` and `tests/`.
3. If a reached module mixes a production part and a tooling part, split it along that line; the tooling part moves.

Leave the reached modules' internals alone. K3 refactors the measurement dialect after this lands.

## Guards

- AST check: no module under `openhcs/` imports `benchmark.equivalence`.
- `openhcs/core/runtime_equivalence.py` does not exist, or contains only what production reaches.

## Tests

Tests of the moved tooling move with it, or are deleted where they test internal structure. The 30-workflow parity check, which uses the tooling, must run unchanged from its new location.

## Done when

Every module left in `openhcs/core/equivalence/` is reachable from production. The guard passes. The parity check is green. The PR reports how many lines moved out.

## Dispatch

> **`equivalence-out`:** Complete surface D4 per `docs/refactor/consolidation-20261009/D4-equivalence-tooling.md`. Compute reachability first and put the reached/unreached table in the PR description. Decision Q1 applies.
