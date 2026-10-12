# K7: Execution protocol

**Head audited:** `openhcs` `main` at `d597aa224` (#1205; G7, K2, K3, N1 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* `AutoRegisterMeta`, the G1 axis family.

Re-measured at this head. G7 replaced part of K7 (see Already done); the other three items were still open.

## Already done (closure note for the worker-lane item)

**Worker lanes dispatching tuple commands on strings with two receivers: landed in G7 (#1191).** Verified at `d597aa224`: `core/orchestrator/worker_execution.py:655-760` declares `WorkerCommand.serve` with `AnsweredWorkerCommand` (`PrepareWorker`, `ExecuteInheritedLane`, `ExecuteShippedLane`, `MapPartitions`, `FinishExecution`) and `StopWorker`; replies are `WorkerReply.settle` (`WorkerResult`, `WorkerFailure`, `WorkerProgress`); one entry `_serve_worker` and one `WorkerProcess` reader. No tag literal is sent (`tests/unit/test_g7_runtime_protocol_guards.py`). Nothing remains for K7 here.

## What is wrong

**Three execution-protocol values encode their variants as `None` and flags, so every consumer re-decides the variant: the component-group scope, the processing context's phase, and the execution result.**

1. **`ComponentGroupScope` packs three variants into two fields** (`core/component_group_scope.py:30`). `keys=(None,), component=None` is ungrouped, `keys=(None,), component=X` is dynamic (keys discovered at run time), anything else is static. The variant is re-decided through `is_ungrouped`/`is_grouped`/`is_dynamic`/`is_static`/`has_single_static_key`/`require_single_static_key`: **73 predicate reads** (AST scan, 25 inside the class, 48 in 8 consumer modules: `pipeline/path_planner.py` 20, `artifacts/input_projection.py` 9, `runtime_stores.py` 8, `artifacts/plans.py` 6, `pipeline/compiler.py` 2, `steps/function_execution.py` 2, `runtime_artifact_values.py` 1), plus `component is None` checks on scopes in `compiler.py:1213,1223`.
   - The same two fields are restated on every `ArtifactPlan` as `group_keys` and `group_component` (`artifacts/plans.py:288-289`), re-packed into a scope by `group_scope()` on each call and unpacked again by `PathPlannerGroupScope.from_output_plan/from_plan`, `RuntimeArtifactQuery.from_input_plan` and `ArtifactInputProjectionPlan.__post_init__` (`from_raw(scope.keys, component=scope.component)` written 8 times).
2. **`RuntimeValue.compose(producer_group_scope=None)` is a `None` mode** (`runtime_artifact_values.py:108`). `None` means "plain composition"; a scope means "reconstruct the producer's group axis". Each kind's `compose_runtime_values` (`artifacts/kinds.py:383,836,1094,1301,1385,1510`) re-decides it: three test `producer_group_scope is None and len(values) == 1`, three `del` the argument.
3. **`ProcessingContext` mixes compile-time and execution-time state** (`core/context/processing_context.py:64`, 324 lines, 258 references in 45 production files). One mutable object carries the compiler's facts (`step_plans`, `axis_id`, `filemanager`, sequential combinations, visualizers, axis filters) and the executor's (`runtime_value_store` and four runtime caches, `completed_step_outputs`, `execution_runtime`, `debug_event_sink`, the per-step value scope). The phase is a flag: `_is_frozen`, checked by `is_frozen()` in 6 compiler stages (`compiler.py:252,536,660,738,775,800`) and in `worker_execution.py:1473`. The compiled context is pickled to workers with empty runtime stores, executed in place, and its stores cleared afterwards (`worker_execution.py:1357`). `compiler.py:227` sets `context.visualizer_config`, an attribute nothing declares or reads.
4. **`ExecutionResult` is a longhand union** (`orchestrator/execution_result.py:190`): an `ExecutionStatus` enum plus `failed_combination` and `error_message` Optionals meaningful only for some statuses, three `is_*` predicates, and three constructors that restate the field defaults. `RuntimeObservationMode` (same file) is an enum whose members' behaviour is written as `if self is …` branches (rule 1a).

## Target (as built)

- **Scope variants** (`core/component_group_scope.py`). `ComponentGroupScope` is an ABC: `UngroupedScope`; `GroupedScope` (holds `component`) with `DynamicGroupScope`, `StaticGroupScope` (two or more keys) and `SingleKeyScope` (exactly one). Each variant owns `runtime_keys`, `candidate_keys`, `contains_runtime_key`, `contains_scope`, `resolve_runtime_key`, `select_runtime_key`, `single_key`, `excludes`, `selectable_from`, `owned_by`, `admits_record_key`, `value_for_plane`, `may_supply_key`, `shared_invocation_scope` and `output_lineage_scope`. `as_grouped()` yields the typed grouped scope (a non-`None` component) where a caller acts only on grouped scopes; `has_compiled_keys` and `names_several_keys` are declared per variant. `ComponentGroupScope.of(keys, component)` is the one reader of the raw spelling. Deleted: the six predicates, `from_raw`, `ungrouped()`, `dynamic()`, `PathPlannerGroupScope` (its union moved to `ComponentGroupScope.union_compatible`; `output_groups_for` and `missing_from` had no caller), and the seven "lost its component" checks the types now make impossible.
- **Plans hold a scope.** `ArtifactPlan.group_scope` is a field. Deleted: `group_keys`, `group_component`, `group_scope()`, `ArtifactInputPlan.producer_group_scope()`, `single_group_key`, `has_dynamic_group_scope`; `relation_scope(component)` replaces `PathPlannerGroupScope.relation_scope_from_plan`.
- **Two compositions.** `RuntimeValue.compose(values)` and `RuntimeValue.compose_groups(values, producer_scope: GroupedScope)`; kinds implement `compose_runtime_values` and, where rebuilding the group axis differs (image, object labels, object lineage), `compose_runtime_groups`. The `producer_group_scope` parameter is deleted.
- **Phase types** (`core/context/processing_context.py`). `ProcessingContext` is the base (`require_axis_id`, `require_parameter_name`). `CompilingContext` is the only mutable phase; `freeze()` returns a `CompiledContext`, which rejects every attribute assignment and is what bundles, transport and workers carry. `CompiledContext.executing(lane)` starts one execution: `ExecutingContext` adds the runtime value store, the four runtime caches, the debug sink, the lane runtime, completed outputs and the per-step value scope, and still rejects assignment to compiled facts. A worker lane builds one per compiled context it executes; the parent builds one per compiled context per `execute_compiled_bundle` call, merges worker observations into it, runs dataset-scoped steps and post-execute hooks on it, and returns them as `BundleExecutionResults.executed_contexts` (the ZMQ observation export reads them there, not from the bundle). Deleted: `_is_frozen`, `is_frozen()`, the six compiler checks and the worker check, `bind_execution_runtime`, `reset_completed_step_outputs`, `inject_plan`, `visualizer_config` (always `None`) and the `core.context` re-export.
- **One result family** (`core/orchestrator/execution_result.py`). `ExecutionResult` ABC with `ExecutionSucceeded`, and `ExecutionStopped` (owns `error_message`, `failed_combination`, `progress_phase`, `progress_status`, `at_combination`) with `ExecutionFailed` and `ExecutionCancelled` (`stops_lane`). Deleted: `ExecutionStatus`, `is_error`, `is_cancelled`, the three constructors, and `ZMQExecutionAxisOutcome` (the outcome export stores `result.without_runtime_observation()`; schema version 5). `RuntimeObservationMode` is a family: `OmitRuntimeRecords`, `MergeAllRuntimeRecords`, `MergeDatasetInputRecords` (E1's names), each owning `retain_records`.

Production (Python under `openhcs/`): −1331 +1248. The net is small because three families replace three encodings one for one; the deletions are the predicates, re-packs and checks, the additions are the variant classes.

## Deletion certificates

| Deleted | Certificate |
|---|---|
| `is_ungrouped`/`is_grouped`/`is_dynamic`/`is_static`/`has_single_static_key`/`require_single_static_key`, `from_raw`, `ungrouped()`, `dynamic()` | **derived** (the variant classes and `ComponentGroupScope.of`) |
| "lost its component" `RuntimeError`s (7), `ArtifactInputProjectionPlan` re-normalisation | **derived** (`GroupedScope.component` is required by construction) |
| `ArtifactPlan.group_keys`/`group_component`, `group_scope()`, `producer_group_scope()`, `single_group_key`, `has_dynamic_group_scope` | **derived** (the `group_scope` field) |
| `PathPlannerGroupScope.output_groups_for`, `.missing_from` | **unused** |
| `producer_group_scope` parameter of `compose`/`compose_runtime_values` | **derived** (`compose_groups`/`compose_runtime_groups`) |
| `ProcessingContext._is_frozen`, `is_frozen()`, 6 compiler checks, the worker "not frozen" check | **derived** (`CompilingContext`/`CompiledContext` types) |
| `bind_execution_runtime`, `reset_completed_step_outputs` | **derived** (`CompiledContext.executing(lane)` builds a fresh execution) |
| `CompilingContext.inject_plan` | **unused** |
| `context.visualizer_config` and the `vis_config` argument at the one call | **derived** (it was always `None`, the parameter's default) |
| `ExecutionStatus`, `is_error`, `is_cancelled`, `ExecutionResult.success/error/cancelled` | **derived** (the result subclasses) |
| `ZMQExecutionAxisOutcome` | **derived** (`ExecutionResult.without_runtime_observation`) |
| `NamedSourceBinding.input_plan` (`core/source_bindings.py`) | **unused** (no caller in `openhcs/`, tests, benchmark or scripts) |
| `openhcs.core.context.ProcessingContext` re-export | **contract** (no re-exports) |

**Tests-only** (behaviour the interface admits that no test exercises):
- `ComponentGroupScope.of` removes duplicate keys and reads an empty key tuple as "no named keys"; `from_raw` kept duplicates and rejected an empty tuple. No producer of duplicate or empty keys is tested.
- `RuntimeArtifactInput.records` no longer special-cases an ungrouped producer; the general path selects the same record. A relation that declares a complete-producer selection on an ungrouped producer now runs the declaration check it previously skipped.
- `ArtifactInputProjectionPlan.validate_storage_plan` raises one message for every out-of-scope selection (three before).
- Runtime caches (`runtime_image_stack_cache`, pattern-discovery, source-binding, output-identity) now live for one execution of a compiled context. They were already per compiled context (one per axis value, or per axis value and sequential combination), so no cache that axes shared is now rebuilt per axis; every reader is axis-scoped step execution (`function_execution.py`, `function_runtime.py`, `source_binding_selection.py`). What is lost: when one in-memory bundle is executed again with inline or thread lanes, the pattern-discovery, source-binding and output-identity caches used to start warm (the image cache and the value store were cleared each time already). Process lanes always started cold, from the pickled bundle. Re-execution of one bundle with warm caches is untested.
- Thread and inline lanes no longer execute on the parent's context object; they get their own `ExecutingContext` like process lanes, and only returned observations reach the parent. Code that read a parent context's store mid-execution from another thread is untested (none found).
- A cancelled or failed axis reports `type(result).__name__` in `require_success` and export messages (`ExecutionFailed: …`), not `error: …`.

## Reassigned / found outside this surface

| Item | Evidence | Belongs to |
|---|---|---|
| Annotations `ProcessingContext` on functions that read `execution_runtime` | `core/materialization/core.py`, `path_scopes.py` (moved by K8 #1208) | done here after K8 merged: annotated `ExecutingContext`; K8's `execution_axis_count()` lives on `ExecutingContext` |
| `RuntimeExecutionAxisScope(component=None, value=None)` packs "no group coordinate" the same way the scope did. Not small: 88 production references in 16 files and 388 test references, and it is the `scope` of every runtime record key (`key.scope.component` is compared across `runtime_stores.py`, `kinds.py`, materialization) | `core/component_group_scope.py` | follow-up surface, not started here |
| E1 (#1203, merged first) converted `ExecutionStatus` and `RuntimeObservationMode` | `execution_result.py` | resolved in the merge of `625150118`: E1's observation-mode family is kept as written; its `ExecutionStatus`/`AxisSucceeded`/`AxisFailed`/`AxisCancelled` family is deleted for the result subclasses and its readers migrated. E1's guard table had no row for anything deleted here |
| `PipelineOrchestrator.execute_compiled_bundle(runtime_observation_mode=None)` derives the mode when `None` | `orchestrator.py:765` | G7 follow-up, not assigned |

## Guards

`tests/unit/test_k7_execution_protocol_guards.py`: none of the deleted names exists in `openhcs/`; the scope, context-phase, result and observation-mode families are exactly the declared members; `ArtifactPlan` has `group_scope` and neither old field; each scope variant reads back from its raw spelling and pickles; each context phase carries only its own state and compiled facts cannot be reassigned; stopped results own their message and combination.

## Tests

Tests take the new constructors (`tests/context_support.py` builds phase contexts without the compiler). Deleted assertions were on structure only: that a transport context shares the runtime store, that the passed context object was the one executed and cleared. Run: the guards; 191 unit test files that touch the changed modules; `test_main` disk direct and ZMQ; official30 parity.

## New-case experiments

- A new scope variant today needs a new `(keys, component)` encoding and a branch at each of 48 predicate reads. After: one subclass implementing the family's methods.
- A new execution outcome today needs an enum member, a predicate, a constructor and optional fields. After: one `ExecutionResult` subclass.

## Done when

The guards pass; touched tests pass; official30 is 30/30; the structural ratchet and nra-r1 show zero regressions.

## Outcome

- Scope predicate reads outside the family: 48 before, 0 after (AST scan). `is None` checks on a scope's component in the compiler: 2 before, 0 after.
- Production (Python under `openhcs/`): −1331 +1248. Tests: −1462 +1684 (the guard file, the context helper and wider import blocks).
- Structural ratchet (`openhcs`, `scripts`, `benchmark`) and nra-r1 against `d597aa224`: no increase.
