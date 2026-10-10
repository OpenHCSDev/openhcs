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
| `introspection/__init__.py` | 55 | Re-exports `python_introspect` with a side-effect `register_namespace_provider` that runs only if a GUI importer happens to load it. Its docstring names lazy dataclass utilities that no longer exist (IDEN-4). Two importers (`step_parameter_editor.py`, `dual_editor_window.py`). No workflow references it; the three workflows that mention "introspect" name the `python-introspect` submodule. The guardrail test only requires the already-deleted `lazy_dataclass_utils.py` to stay absent. |
| `components/framework.py` | 210 | `core/components/__init__.py:9` says it was "moved to openhcs/components/". Four importers. `core/components/__init__.py` re-exports six names nobody imports from the package. Seven methods in `core/components` have no caller (`get_available_variable_components`, `get_available_group_by_components`, `get_component_names`, `extract_component`, `validate_parse_result`, `validate_component_value`, `validate_component_combination_constraint`). |
| `core/components/multiprocessing.py` | 140 | `Task` and `MultiprocessingCoordinator`; the only reference is the re-export in `core/components/__init__.py:14,21` |
| `utils/pipeline_migration.py` | 508 | Legacy GroupBy pickle migration, still wired into `pyqt_gui/widgets/pipeline_editor.py:130` and `widgets/shared/services/pipeline_editor_workflows.py:41` (decision Q3: delete). The second call site is the code-mode `migration_namespace` hook, which the UI agent bridge also invokes (`pyqt_gui/services/ui_agent_bridge.py:560`). |

## Target

- Move `memory_diagnostic*` into `scripts/mcp_memory_diagnostic*.py`, beside its only consumer. The product import authority launches only `openhcs.*` modules, so the diagnostic's server spec owns its own `-c` launch from the selected import root.
- Delete `blind_recipe_audit.py`, `recorded_evidence.py`, `validation/` and their tests. Their work is over: the paper's evidence is archived in `paper/supplementary/`.
- Register the forward-reference namespace provider in `core/config.py`, the module that owns the namespace, so it runs whenever config is loaded rather than when a GUI module happens to import the shim. Import `python_introspect` directly everywhere and delete `openhcs/introspection/`.
- Merge `components/framework.py` back into `core/components` and delete `openhcs/components/`. Delete `core/components/multiprocessing.py`, the package re-exports and the uncalled methods. D3 owns `core/components/`.
- Delete `pipeline_migration.py` and its two call sites. Loading a pre-GroupBy pickle then fails with the current loader's error (`dill.load`, then a `TypeError` for a non-list payload). Delete the bridge's `migrate_code_namespace` retry, which no implementer serves any more.
- Outside D3's files: pyqt-reactive still declares `ManagerCodeExecutionWorkflow.migration_namespace` abstract and `ManagerActionOperations.migrate_code_namespace`; both OpenHCS implementers now return `None`. Removing the hook needs a pyqt-reactive release; it is not done here.

## Guards

`tests/unit/test_product_boundary_guards.py`:
- Every removed module (`openhcs.introspection`, `openhcs.validation`, `openhcs.components`, `openhcs.core.components.multiprocessing`, `openhcs.utils.pipeline_migration`, `openhcs.agent.blind_recipe_audit`, `openhcs.mcp.recorded_evidence`, `openhcs.mcp.memory_diagnostic*`) is absent from the tree.
- AST check: no module under `openhcs/` imports, or names as a dotted module string, a removed module or anything in `scripts` or `benchmark`.

## Tests

Delete tests of deleted modules. Move `test_mcp_memory_diagnostic.py` with its module.

## Done when

The table is empty, the guards pass, and CI workflows referencing the removed paths are updated.

## Dispatch

> **`product-boundary`:** Complete surface D3 per `docs/refactor/consolidation-20261009/D3-product-boundary.md`. Done when every row is resolved. Decision Q3 applies (delete the pickle migration).
