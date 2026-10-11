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

## Target

- **Scope variants.** `ComponentGroupScope` is an ABC with `UngroupedScope`, and `GroupedScope` (holds `component`) with `DynamicGroupScope` and `StaticGroupScope` (holds `keys`). Each variant owns `runtime_keys`, `contains_runtime_key`, `contains_scope`, `resolve_runtime_key`, `select_runtime_key`, `excludes`, `output_lineage_scope` and the other questions consumers asked through predicates. `ComponentGroupScope.of(keys, component)` is the one constructor from raw values. The predicates and `from_raw` are deleted.
- **Plans hold a scope.** `ArtifactPlan.group_scope` is a field; `group_keys`/`group_component` and every unpack/re-pack are deleted.
- **Two compositions.** `RuntimeValue.compose(values)` and `RuntimeValue.compose_groups(values, producer_scope: GroupedScope)`; kinds override `compose_runtime_groups` where reconstruction differs. The `producer_group_scope` parameter is deleted.
- **Phase types.** `ProcessingContext` is the base carrying compile facts. `CompilingContext` is the only mutable one (`inject_plan`, `freeze() -> CompiledContext`); `CompiledContext` is immutable and is what bundles and workers carry; `ExecutingContext(CompiledContext)` adds the runtime stores, caches, debug sink, lane runtime and completed outputs, and is built per execution by `CompiledContext.executing(...)`. `_is_frozen`, `is_frozen()`, the six compiler checks and `visualizer_config` are deleted.
- **One result family.** `ExecutionResult` ABC with `ExecutionSucceeded`, `ExecutionFailed` (owns `error_message`, `failed_combination`) and `ExecutionCancelled` (owns `error_message`); `ExecutionStatus` and the `is_*` predicates are deleted. `RuntimeObservationMode` becomes a family whose members own `retain_records`.

## Guards

`tests/unit/test_k7_execution_protocol_guards.py`: no production read of the deleted scope predicates or `from_raw`; no `group_keys`/`group_component` plan fields; no `producer_group_scope` parameter; no `is_frozen`/`_is_frozen`; no `ExecutionStatus` in `execution_result.py`; the scope, context and result families are exactly the declared members.

## Tests

Touched tests take the new constructors and types. Run: the guards; the unit test files that import the changed modules (one process each); official30 parity (30/30).

## New-case experiments

- A new scope variant today needs a new `(keys, component)` encoding and a branch at each of 48 predicate reads. After: one subclass implementing the family's methods.
- A new execution outcome today needs an enum member, a predicate, a constructor and optional fields. After: one `ExecutionResult` subclass.

## Done when

The guards pass; touched tests pass; official30 is 30/30; the structural ratchet and nra-r1 show zero regressions.

## Progress

- [x] Receipt.
- [ ] ExecutionResult and RuntimeObservationMode families.
- [ ] ComponentGroupScope variants, plan `group_scope` field, compose split.
- [ ] Context phase types.
- [ ] Guards, tests, ratchet, parity, PR.
