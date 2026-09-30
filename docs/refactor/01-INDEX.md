# OpenHCS refactor index

**Head audited:** `main` at `c86f562e` (29 September, 23:38). **Rules:** [00-RULES.md](00-RULES.md). Surface files are written one at a time against the head of the day; re-verify yours before editing. Measures are the refactor-audit skill's census, overlay and `merge_review.py`, parsed with Python 3.14.

## Evidence

**Size:** 409,288 Python lines in `openhcs/` (353,263 code lines), plus a new C++ native backend.

**Where the debt is,** weighted as the skill's census weights it:

| Subpackage | Code lines | Share of debt | Per 1,000 lines | Leading measures |
|---|---|---|---|---|
| `core` (top-level modules) | 56,292 | 20.0% | 62 | `None` 1,601, `isinstance` 619, foreign probes 263 |
| `processing/backends` | 105,221 | 16.1% | 27 | `None` 976, string-keyed reads 426, probes 150 |
| `mcp/dev_client_renderers` | 6,068 | 7.6% | **221** | **`.get("…")` 1,011**, `None` 164, `isinstance` 125 |
| `runtime` | 19,487 | 6.4% | 58 | `None` 435, `isinstance` 190, probes 107 |
| `agent/services` | 17,799 | 5.6% | 55 | `None` 300, `isinstance` 146, probes 114 |
| `interop/cellprofiler` | 22,461 | 5.1% | 40 | `None` 403, `isinstance` 160, probes 89 |
| `pyqt_gui/widgets` | 15,153 | 5.1% | 59 | `None` 441, probes 104, broad `except` 37 |
| `pyqt_gui/services` | 16,144 | 4.9% | 53 | `None` 348, probes 77, broad `except` 65 |

**Structure (overlay):** 280 raw record shapes, **199 of which bypass a class that already models them** (135 in `mcp/dev_client_renderers`); 46 string dispatches (20 in `processing/backends`); 59 type switches; 260 functions over 100 lines (115 in `processing/backends`); 65 classes over 500 lines, the largest `PlateManagerWidget` (2,178), `PipelineCompiler` (1,806), `OpenHCSMainWindow` (1,771), `ViewerWindowService` (1,602), `SourceBindingsEditorWidget` (1,458), `PathPlannerArtifactStage` (1,440), `PipelineEditorWidget` (1,424) and `CellProfilerModuleExecutor` (1,398); 1,098 legacy markers; 98 modules nothing imports. Long conditions are low (20): chains are not OpenHCS's problem, `None`-as-state is.

**Direction:** in the last 24 hours, 49 first-parent commits added code denser in debt than the package (per 1,000 lines: `None` 27 against 19, `isinstance` 12 against 7, foreign probes 6 against 4, broad `except` 2.1 against 1.2), mostly from features (#198, #225, #154, #177) and one fix (#233). Only 6 of 129 commits removed debt.

**Guardrails:** none. No ratchet, no NRA in CI, and parity runs only on pushes to `main`.

## Surfaces

| ID | Surface | Evidence | Target |
|---|---|---|---|
| **R0** | [Stop the inflow](R0-stop-the-inflow.md) | no ratchet; parity after merge only | ratchet, NRA changed-file scan and parity on every PR |
| **L0** | Legacy and dead code | 1,098 legacy markers; 98 unimported modules, many probably discovered by the function registry rather than imported | classify external-format support against internal compatibility; delete the second kind and truly dead modules |
| **S1** | MCP development-client renderers | 1,011 `.get` reads and 135 raw shapes in 6,068 lines, most bypassing existing classes | decode MCP results once into the DTOs that exist; renderers read typed fields |
| **S2** | Processing backends | 105,221 lines; 20 string dispatches, 115 god functions, 426 string-keyed reads | families for what the dispatch decides; functions split by owned concept; parity-gated |
| **S3** | Core configuration and context | 1,601 `None` checks and 619 `isinstance` in `core`'s top-level modules | depends on D2: resolution states instead of `None` probing, and decoding instead of re-validation |
| **S4** | Pipeline compilation | `PipelineCompiler` 1,806, `PathPlannerArtifactStage` 1,440, `core/steps` and `core/pipeline` probes | components owning compilation stages |
| **S5** | CellProfiler interop | `None` 403, `isinstance` 160, `CellProfilerModuleExecutor` 1,398 | CellProfiler semantics decoded once at the boundary; parity-gated |
| **S6** | Runtime and agent services | `ViewerWindowService` 1,602; `runtime` and `agent/services` probes | owners report their state |
| **S7** | PyQt GUI | four god classes over 1,400 lines; 102 broad `except` clauses in widgets and services | components owning GUI state; after GUI journeys exist (D4) |
| **S8** | Microscopes and formats | string dispatch and string-keyed reads over external formats | each format decoded once into a family |

## Order

1. **R0,** before anything else.
2. **L0,** so no surface refactors dead or legacy code.
3. **S1** (the worst density, at one boundary) and **S3** (after D2) in parallel.
4. **S2, S5, S8,** parity-gated, in parallel by subpackage.
5. **S4, S6.**
6. **S7,** last, once GUI journeys protect it.

## Distribution across new and existing PRs

**Existing PRs keep their scope.** They don't absorb surface work, with one exception: a PR already rewriting a function a surface targets writes that function in the surface's target form, so the code isn't churned twice. Measured on production code against each merge-base:

| Existing work | Production change | Weighted debt | Before merging |
|---|---|---|---|
| #205 exact label selection | +274 / −56 | −3 | nothing; merge |
| #217 BaSiCPy readiness | +172 / −253 | −2 | nothing; merge |
| #159 viewer bind (plan) | +139 / −56 | −1 | nothing; merge |
| #227 centrosome watershed registration | +10 | 0 | nothing; merge |
| #259 callable reference payload | +59 / −10 | 0 | nothing; merge |
| #110, #125, #160, #207 | none | 0 | nothing (docs and plans) |
| **#208 memory session** | +513 | **+19** | remove the debt it adds |
| **`mcp-materialized-result-reopening`** (no PR) | +201 / −55 | **+18** | open a PR, remove its debt |
| **`custom-source-inspection`** (no PR) | +294 / −60 | **+14** | open a PR, remove its debt |
| #256 owned runtime bootstrap | +350 / −15 | +3 | remove its debt |
| `perf-fork-compiler-prewarm` (no PR) | +106 / −14 | +3 | open a PR with benchmark evidence, remove its debt |
| #215 primary segmentation diagnostics | +256 / −9 | +2 | remove its debt; parity evidence |
| `perf-wide-intensity-distribution` (no PR) | +256 / −183 | +2 | open a PR with parity and benchmark evidence |
| #206 input preparation | +161 / −80 | +1 | remove its debt |

"Remove the debt it adds" means leaving every touched file no worse than on `main`, which is what the ratchet enforces once R0 lands. Branches with no PR and no production change (`headless-bootstrap`, `plan/issue-140-zmq-failure`, the documentation branches) either open a PR or are deleted: a stale branch is a second version too.

**New PRs, one owned concept each,** at most a few hundred production lines, merged one at a time with their own checks, never in batches:

1. **R0,** CI and the PR template only, before anything else.
2. **S1,** immediately: no open work touches `mcp/dev_client_renderers`.
3. **L0,** one PR per subpackage, each after that subpackage's open PRs merge.
4. **S3,** after the six open items touching `core` merge (#205, #159, #206, #256, #259 and `custom-source-inspection`), and after D2.
5. **S2,** after #215, #217, #227 and `perf-wide-intensity-distribution`, one PR per backend concept, each with parity evidence.
6. **S5, S8, S6 (after #159 and #256), S4,** then **S7** once GUI journeys exist.

## Decisions

| ID | Question | Default |
|---|---|---|
| **D1** | Which user-facing formats are external contracts? | `PipelineDocument` source, registered function names, the configuration schema users write, and persisted results. They change only with a version and a one-shot migration tool |
| **D2** | Is `None` in the lazy configuration system a deliberate "inherit from context" sentinel? | Yes where users write it (keep it at that boundary, as D1), decoded internally into explicit resolution states; everywhere else `None` is state to be modelled |
| **D3** | Which parity checks run per PR? | The CellProfiler reference cases whose modules the PR changes, within a time budget; the full corpus nightly |
| **D4** | Do the PyQt GUI flows get installed journeys, like Toad's? | Yes, before S7 starts |

## Pending

NRA's complete scan of the package is running and will be added to the evidence when it finishes.

## Surface files

Written just in time: [`R0-stop-the-inflow.md`](R0-stop-the-inflow.md),
and the authoritative [L0 pattern-resolver checkpoint](L0-pattern-resolver.rst).
The latter closes one confirmed dead module, not the whole L0 surface.
