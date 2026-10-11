# G7: Runtime vocabulary and protocol

**Head audited:** `openhcs` `main` at `d35934da7` (#1188; G1, G2, L3 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.** Replaces K7 and C6.
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "Runtime". *Uses:* G1 `AxisFamily.partition_axis()`, L2 codec (`to_jsonable`, `dataclass_from_mapping`), L3 `TaskProgress` (`WireView`) and its words (`subject_id`, `execution_subject_id`, `partition_values`).

## What is wrong

**The runtime (orchestrator, lane planning, worker IPC, progress, execution server, config) speaks microscopy, encodes its worker protocol as string-tagged tuples and its progress events by hand, and copies the lane identity into every emit (IDEN-4, IMPL-1, MEMB-2).**

Census at `d35934da7`, an AST scan of `openhcs/runtime/zmq_*.py`, `openhcs/core/orchestrator/`, `openhcs/core/progress/` and `openhcs/core/config.py` for identifiers (names, attributes, definitions, arguments, keywords and identifier-shaped string literals) whose words include `well(s)` or `plate(s)`:

| File | Hits | What they are |
|---|---|---|
| `core/progress/projection.py` | 201 | `PlateRuntimeState` enum plus a 9-class declaration family keyed by it; `PlateRuntimeIdentity`/`PlateRuntimeProjection`; `plates`, `by_plate_latest`, `add_plate`, `upsert_plate`, `get_plate`, `generic_plate` |
| `core/progress/runtime_tree.py` | 145 | `PlateProgressTreeNode` (`node_kind = "plate"`), `known_wells`, `well_nodes`, `make_well_progress_node`, `events_by_plate`, `plate_name` |
| `core/orchestrator/orchestrator.py` | 92 | `plate_path` (constructor, frozen attribute, setter), `source_plate_path`, `_rebind_plate_path_*`, `compile_pipelines(well_filter=…)`, `execute_compiled_plate` |
| `core/orchestrator/compiled_plate_execution.py` | 64 | `CompiledPlateExecution{Request,Results,Extras}`, `ValidatedCompiledPlateExecution`, plate-scoped step helpers, `PLATE_STEP_PROGRESS_HEARTBEAT_SECONDS` |
| `core/orchestrator/worker_execution.py` | 53 | `plate_id`/`owned_wells` in 7 `emit` calls and 2 profiling scopes |
| `runtime/zmq_execution_server.py` | 52 | `plate_id`, `plate_path_str`, `_wells_for_execution`, `owned_wells`/`total_wells` worker claims, `plate_pipeline` |
| `core/progress/types.py` | 33 | `ProgressIdentity.plate_id`, `ProgressExecutionContext.plate_id`, `total_wells`, `owned_wells` |
| `runtime/zmq_compilation.py` | 29 | `plate_id`, `output_plate`, `well_filter=` |
| `core/config.py` | 29 | `WellFilterConfig`, `WellFilterMode`, `StepWellFilterConfig`, `well_filter`, `well_filter_mode`, `auto_add_output_plate_to_plate_manager` |
| `runtime/zmq_execution_client.py` | 24 | `PlateIdentifier`, `execution_plate_id`, `plate_id` |
| 12 more files | 100 | `zmq_server_hooks`, `worker_profiling`, `zmq_execution_signature` (`WELL_FILTER = "well_filter"` wire key), `zmq_progress` (`wells=`), `zmq_orchestrator_environment`, `progress/__init__` (`emit(plate_id=…, total_wells=…, owned_wells=…)`), `worker_lanes`, `zmq_worker_execution`, `execution_result` (`MERGE_PLATE_INPUTS`), `zmq_control`, `progress/registry`, `viewer_component_system` (a false positive: `template`) |
| **Total** | **822 in 22 files, 102 distinct identifiers** | `plate_id` 140, `PlateRuntimeState` 75, `owned_wells` 64, `plate_path` 51, `plate_projection` 34, `total_wells` 30, … |

Reach outside these files: `well_filter` 58 production lines in 16 files and 191 test lines in 51 files; `WellFilterConfig` 20/6 and 34/9; `plate_id` 239/44 and 202/69; `owned_wells` 56/9; `PlateRuntimeState` 76/2.

Protocol and codec:
- **Worker IPC is string-tagged tuples with two receivers.** `worker_execution.py` sends `("execute", payload, lane_keys, lane_context, mode, log_base)`, `("partition", func, requests)`, `("finish",)` and `None`, and receives `("result", x)`, `("error", exc, tb)`, `("progress", dict)`: 21 tag literals and 18 `send`/`recv` sites. `_execute_fork_inherited_worker_lane_process` and `_execute_prepared_fork_worker_process` each decode commands; `ForkInheritedWorkerLaneRunner._receive_result` and `PreparedForkWorkerExecutorResources._collect_results` each decode replies, with an "unknown message" branch apiece.
- **Progress events are dicts inside the process tree.** `ProgressQueue.put(progress_update: dict)`; `emit` and `ZMQProgressEmitter` call `event.to_dict()` before queueing, and the server decodes `ProgressEvent.from_dict` again before re-encoding for the wire (each event is encoded 2 to 3 times in-process).
- **The progress field list is written eight times** (C6): `ProgressEvent` fields, `ProgressEventPayload` fields, `ProgressEventPayload.to_event`, `emit()` parameters, `emit()` body, `ProgressEvent.from_dict`, `ProgressEvent.to_dict`, `ZMQProgressEmitter.emit`. `ProgressIdentity` maps `plate_id` to the wire key `subject_id` by hand in both directions, and `ProgressExecutionContext` has a third hand codec (`from_transport_fields`, `to_transport_fields`, `from_value`) whose wire key is still `plate_id`.
- **The lane identity is restated at every emit.** `execution_id`, `plate_id`, `worker_slot`, `owned_wells` are copied into 7 `emit` calls in `worker_execution.py` and 1 in `steps/function_execution.py`; `owned_wells` is defined twice (`WorkerLaneExecutionContext.owned_wells`, `WorkerAssignmentPlan.owned_wells`); `WorkerLaneExecutionPlan.lane_context` restates the plan's identity field by field.
- **`ZMQExecutionContext.progress_context()` builds an identity dict** that `PipelineOrchestrator.execute_compiled_plate` decodes back with `ProgressExecutionContext.from_value`.
- **`PlateRuntimeState` is an enum keying a declaration family** (rule 1a): every consumer reaches behaviour through `PlateRuntimeStateDeclarationBase.for_state(state)`.

## Target

- **Vocabulary.** Runtime-owned names say what they are: `subject_id` (what one execution is about, as in zmqruntime), `execution_subject_id`, `dataset_root` (the orchestrator's `plate_path`), `partition_values` (every partition value of an execution; was `total_wells`), `owned_partition_values` (one lane's; was `owned_wells`), `partition_filter` (`PartitionFilterConfig`, `PartitionFilterMode`, `StepPartitionFilterConfig`, `PartitionFilterProcessor`, `partition_filter_mode`), the ZMQ auxiliary key `partition_values`, `SubjectRuntimeState`/`SubjectRuntimeProjection`, `SubjectProgressTreeNode`, `execute_compiled_bundle` and `bundle_execution.py`, dataset-scoped steps.
- **Progress events: one declaration.** `ProgressEvent` extends zmqruntime's `TaskProgress` (`WireView`), so its wire mapping is its declared fields and the codec is L2's. Inside the process tree the queue carries `ProgressEvent` objects; only the ZMQ boundary calls `to_dict`. `ProgressEventPayload`, `create_event`, `ProgressIdentity` and the three hand codecs are deleted.
- **Lane identity derived.** `ProgressExecutionContext` (`execution_id`, `subject_id`) builds and emits events; `WorkerLaneExecutionContext` adds its `worker_slot` and `owned_partition_values` by inheritance. Every worker emit becomes `lane_context.emit(...)` with only the per-event fields.
- **Typed worker IPC.** Commands (`ExecuteLane`, `MapPartitions`, `FinishExecution`, `StopWorker`) and replies (`WorkerResult`, `WorkerFailure`, `WorkerProgress`) are declared message families; each command runs itself in the worker and each reply delivers itself to the parent. One worker loop and one reply reader replace the two of each; there is no unknown-message branch.
- **`SubjectRuntimeState` is a family** keyed by its nominal classes; the enum is deleted.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Progress events, worker pipe messages, ZMQ auxiliary params, results summaries, compile artifacts | runtime | reset |
| Saved global config (`global_config.config`, `.py`) and saved `.py` pipelines that name `WellFilterConfig`, `StepWellFilterConfig`, `WellFilterMode`, `well_filter`, `well_filter_mode`, `well_filter_config`, `auto_add_output_plate_to_plate_manager` | durable | Not converted (decision G7-Q1 in the index; default: no tool). Such files fail loudly on load and are re-saved from the GUI. |

## Guards

`tests/unit/test_axis_family_guards.py`, `test_runtime_modules_name_no_dataset_member`: over the runtime modules (`openhcs/runtime/zmq_*.py`, `openhcs/core/orchestrator/`, `openhcs/core/progress/`, `openhcs/core/config.py`), the set of (module, identifier) whose words include `well(s)` or `plate(s)` **equals** `RUNTIME_FOREIGN_NAMES`, an exact allowlist of names declared outside the runtime modules (each with its owning surface). `tests/unit/test_g7_runtime_protocol_guards.py`: no string literal is sent or compared as a worker message tag; `ProgressEvent` defines no `to_dict`/`from_dict`; `ProgressEventPayload`, `create_event` and `PlateRuntimeState` do not exist.

## Tests

The touched runtime, progress, ZMQ and lane tests take the new names and types; tests of the deleted codecs are deleted. One round-trip test over `ProgressEvent`; one test per message family that each member runs or delivers.

## New-case experiments

- A new worker command today needs a tag literal, a branch in each receiver and an unknown-tag error path. After: one subclass with `run`.
- A new progress field today needs eight edits. After: one field.
- The remote-sensing witness running over ZMQ today reports `total_wells`/`owned_wells` and filters by `well_filter`. After: `partition_values` and `partition_filter`.

## Done when

The guards pass; the witness, the touched test files (one process each), `test_main` disk direct and disk zmq, and official30 parity (30/30) are green.
