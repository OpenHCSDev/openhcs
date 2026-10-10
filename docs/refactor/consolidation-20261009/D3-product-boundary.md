# D3: Research tools and vestigial packages

**Head audited:** `openhcs` `main` at `0be261732` (#1152). **Rules:** [00-RULES.md](00-RULES.md). **Step 1.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* none.

## What is wrong

**Research and diagnostic tools, a dead package, a re-export shim and a legacy migration live inside the product package (TIME-6, TIME-3, AGENT-1).**

| Item | Lines | Evidence |
|---|---|---|
| `agent/blind_recipe_audit.py` | 177 | Imported only by `tests/unit/agent/test_blind_recipe_audit.py` |
| `mcp/recorded_evidence.py` | 278 | Imported only by `tests/unit/test_recorded_evidence.py` |
| `mcp/memory_diagnostic.py` and `memory_diagnostic_launch.py` | 563 | Used only by `scripts/check_mcp_memory_ownership.py` and its test; moved there from `benchmark/` |
| `validation/` | 628 | No product importer (only `tests/.../test_ast_validator_registry.py`) |
| `introspection/__init__.py` | 55 | Re-exports `python_introspect` with a side-effect `register_namespace_provider` that runs only if a GUI importer happens to load it. Its docstring names lazy dataclass utilities that no longer exist (IDEN-4). Referenced by 3 workflows and the guardrail test. |
| `components/framework.py` | 210 | `core/components/__init__.py:9` says it was "moved to openhcs/components/". Four importers. |
| `core/components/multiprocessing.py` | 140 | `Task` and `MultiprocessingCoordinator`; the only reference is the re-export in `core/components/__init__.py:14,21` |
| `utils/pipeline_migration.py` | 508 | Legacy GroupBy pickle migration, still wired into `pyqt_gui/widgets/pipeline_editor.py:130` and `widgets/shared/services/pipeline_editor_workflows.py:41` (decision Q3: delete) |

## Target

- Move `memory_diagnostic*` into `scripts/`, beside its only consumer.
- Delete `blind_recipe_audit.py`, `recorded_evidence.py`, `validation/` and their tests. Their work is over: the paper's evidence is archived in `paper/supplementary/`.
- Fold the namespace-provider registration into application bootstrap. Import `python_introspect` directly everywhere and delete `openhcs/introspection/`. Update the three workflows and the guardrail test.
- Merge `components/framework.py` back into `core/components` and delete `openhcs/components/`. Delete `core/components/multiprocessing.py` and its re-export. D3 owns `core/components/`.
- Delete `pipeline_migration.py` and its two call sites. Loading a pre-GroupBy pickle then fails with the current loader's error.

## Guards

- AST check: no module under `openhcs/` imports from `openhcs.introspection`, `openhcs.validation` or `openhcs.components`.
- `scripts/` modules are not importable as `openhcs.*`.

## Tests

Delete tests of deleted modules. Move `test_mcp_memory_diagnostic.py` with its module.

## Done when

The table is empty, the guards pass, and CI workflows referencing the removed paths are updated.

## Dispatch

> **`product-boundary`:** Complete surface D3 per `docs/refactor/consolidation-20261009/D3-product-boundary.md`. Done when every row is resolved. Decision Q3 applies (delete the pickle migration).
