# G7: Runtime vocabulary and protocol

**Head audited:** `openhcs` `main` at `d35934da7` (#1188; G1, G2, L3 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.** Replaces K7 and C6.
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "Runtime". *Uses:* G1 `AxisFamily.partition_axis()`, L2 codec (`to_jsonable`, `dataclass_from_mapping`, `project_dataclass`), L3 `TaskProgress` (`WireView`) and its words (`subject_id`, `execution_subject_id`, `partition_values`).

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
- **Worker IPC is string-tagged tuples with two receivers.** `worker_execution.py` sends `("execute", payload, lane_keys, lane_context, mode, log_base)`, `("partition", func, requests)`, `("finish",)` and `None`, and receives `("result", x)`, `("error", exc, tb)`, `("progress", dict)`: 21 tag literals and 18 `send`/`recv` sites. `_execute_fork_inherited_worker_lane_process` and `_execute_prepared_fork_worker_process` each decode commands; `ForkInheritedWorkerLaneRunner._receive_result` and `PreparedForkWorkerExecutorResources._collect_results` each decode replies, with an "unknown message" branch apiece. Workers are `(slot, process, connection)` tuples unpacked at 14 sites.
- **Progress events are dicts inside the process tree.** `ProgressQueue.put(progress_update: dict)`; `emit` and `ZMQProgressEmitter` call `event.to_dict()` before queueing, and the server decodes `ProgressEvent.from_dict` again before re-encoding for the wire (each event is encoded 2 to 3 times in-process).
- **The progress field list is written eight times** (C6): `ProgressEvent` fields, `ProgressEventPayload` fields, `ProgressEventPayload.to_event`, `emit()` parameters, `emit()` body, `ProgressEvent.from_dict`, `ProgressEvent.to_dict`, `ZMQProgressEmitter.emit`. `ProgressIdentity` maps `plate_id` to the wire key `subject_id` by hand in both directions, and `ProgressExecutionContext` has a third hand codec (`from_transport_fields`, `to_transport_fields`, `from_value`) whose wire key is still `plate_id`.
- **The event context is an untyped bag** (C6): three payloads (`RuntimeArtifactProgressPayload`, `LiveMeasurementProgressPayload`, `DebugProgressContext`) each hand-code the key lookup, the mapping check and the merge, and the debug payload is found by probing for a `debug_session_id` key among the others.
- **The lane identity is restated at every emit.** `execution_id`, `plate_id`, `worker_slot`, `owned_wells` are copied into 7 `emit` calls in `worker_execution.py` and 1 in `steps/function_execution.py`, into the debug sink request and both debug sinks, and into the profiling policy's four keyword arguments; `owned_wells` is defined twice (`WorkerLaneExecutionContext.owned_wells`, `WorkerAssignmentPlan.owned_wells`); `WorkerLaneExecutionPlan.lane_context` restates the plan's identity field by field.
- **`ZMQExecutionContext.progress_context()` builds an identity dict** that `PipelineOrchestrator.execute_compiled_plate` decodes back with `ProgressExecutionContext.from_value`.
- **Pattern discovery receives the partition filter as a keyword spelled from the axis name** (`f"{axis_name}_filter"` built by the caller and read back by the engine).
- **`PlateRuntimeState` is an enum keying a declaration family** (rule 1a): every consumer reaches behaviour through `PlateRuntimeStateDeclarationBase.for_state(state)`.

## Target (as built)

- **Vocabulary.** Runtime-owned names say what they are: `subject_id` (what one execution is about, as in zmqruntime) and `execution_subject_id`; `dataset_root` (the orchestrator's and `ProcessingContext`'s `plate_path`, the server's `plate_path_str`, `source_dataset_root`); `partition_values` (every partition value of an execution, was `total_wells`, and the ZMQ auxiliary key, was `well_filter`); `owned_partition_values` (one lane's, was `owned_wells`); `PartitionFilterConfig`, `StepPartitionFilterConfig`, `PartitionFilterMode`, `partition_filter`, `partition_filter_mode`, `partition_filter_config` and `PartitionFilterProcessor` (moved from `core/utils.py` to `core/partition_filter.py`); `auto_add_output_dataset`, `ExecutionOutputSummary`, `output_dataset_root`; `SubjectRuntimeState`/`SubjectRuntimeProjection`/`SubjectRuntimeIdentity`, `SubjectProgressTreeNode` (`node_kind = "subject"`), `partition_nodes`; `bundle_execution.py` with `BundleExecutionRequest`/`Results`/`Extras`, `execute_compiled_bundle`; dataset-scoped steps; `MERGE_DATASET_INPUTS`; `WorkspaceSourceProjections.from_dataset_metadata(dataset_root=…)`; `SourceBindingContext.logical_dataset_id`/`display_dataset_root`/`execution_dataset_root`. Log and error text in the runtime modules follows. Census after: 7 occurrences of 5 names, all declared outside the runtime modules (Guards).
- **Progress events: one declaration.** `ProgressEvent` extends zmqruntime's `TaskProgress` (`WireView`): its wire mapping is its declared fields and the codec is L2's. `identity` is a projection (`project_dataclass(ProgressIdentity, event)`). Inside the process tree queues carry `ProgressEvent` objects (thread and process queues are registered `ProgressQueue` members); only the ZMQ boundary calls `to_dict`. `ProgressEventPayload`, `create_event`, the module-level `emit`, the three hand codecs, `ProgressValidationError` and `ProgressRegistrationError` are deleted.
- **Event context: a payload family.** `ProgressContextPayload` (`AutoRegisterMeta`, keyed by `context_key`) owns the key lookup, the mapping check and the merge (`context_of`); `DeclaredProgressContextPayload` adds the L2 codec. `RuntimeArtifactProgressPayload` and `LiveMeasurementProgressPayload` keep their bodies; `DebugProgressContext` is declared and moves under the `debug` key, so `is_progress_context`/`to_progress_context`/`from_progress_context`, `runtime_artifact_context_for_records` and `live_measurement_context_for_records` are deleted.
- **Lane identity derived.** `ProgressExecutionContext` (`execution_id`, `subject_id`) builds and emits events; `WorkerLaneExecutionContext` adds its `worker_slot` and `owned_partition_values` by overriding `event_fields`, and `WorkerLaneExecutionPlan.lane_context` is `project_dataclass` of the plan. Every worker and pattern-group emit is `lane_context.emit(...)` with only the per-event fields; the debug sinks and the profiling policy take the lane context; `WorkerAssignmentPlan.owned_wells` is deleted. `ZMQProgressEmitter` is a `ProgressExecutionContext` whose `emit` enqueues; `PipelineOrchestrator.progress_context()` supplies the compiler's events; `execute_compiled_bundle` takes a typed `progress_context` and `progress_queue`.
- **Typed worker IPC.** Commands are one family, `WorkerCommand.serve(connection)`: `AnsweredWorkerCommand` (answers one `WorkerResult` or `WorkerFailure`) with `PrepareWorker`, `ExecuteInheritedLane`, `ExecuteShippedLane`, `MapPartitions`, `FinishExecution`; and `StopWorker`. Replies are one family, `WorkerReply.settle(worker, progress_queue)`: `WorkerResult`, `WorkerFailure`, `WorkerProgress`. One process entry (`_serve_worker`) serves both fork lanes and prepared workers; one `WorkerProcess` record reads replies; there is no tag and no unknown-message branch. Profiling moved into `execute_worker_lane`, so every lane kind profiles.
- **`SubjectRuntimeState` is the family.** States are its subclasses (`QueuedSubjectRuntimeState`, …), the boundary spelling is `state_name`, and `PlateRuntimeState` and `for_state` are deleted.
- **Partition filter by role.** Pattern discovery takes `partition_values=`; `PartitionFilterMode` members carry `keeps_matches`/`rejects_unknown_values`, so the processor has no include/exclude branch.
- **`ZMQCompilationResult`** derives `compiled_axis_ids`, `step_names` and `worker_assignments` from its bundle instead of storing copies.

Production (Python under `openhcs/`): −2733 +2036.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Progress events, worker pipe messages, ZMQ auxiliary params, results summaries, compile artifacts, debug progress contexts | runtime | reset |
| Benchmark manifests (`benchmark/manifests/*.json`, `well_filter`/`default_well_filter` keys) | ours | renamed in lockstep (`partition_filter`/`default_partition_filter`) |
| Saved global config (`.py`) and saved `.py` pipelines that name `WellFilterConfig`, `StepWellFilterConfig`, `WellFilterMode`, `well_filter`, `well_filter_mode`, `well_filter_config`, `auto_add_output_plate_to_plate_manager` | durable | Not converted (decision G7-Q1 in the index; default: no tool). Such files fail loudly on load and are re-saved from the GUI. Recorded pipelines under `paper/` and `validation/` keep their text. |

## Guards

- `tests/unit/test_axis_family_guards.py::test_runtime_modules_speak_no_microscopy_word`: over the runtime modules (`openhcs/runtime/zmq_*.py`, `openhcs/core/orchestrator/`, `openhcs/core/progress/`, `openhcs/core/config.py`), the set of (module, identifier) whose words include the partition axis's spellings (`well`, `wells`) or the dataset scope's (`plate`, `plates`) **equals** `RUNTIME_FOREIGN_NAMES` (exact; a new name or a removed exemption both fail).
- `tests/unit/test_g7_runtime_protocol_guards.py`: no replaced name exists anywhere (`ProgressEventPayload`, `create_event`, the transport-field codecs, `PlateRuntimeState`, the `WellFilter*` names, `well_filter*`, `owned_wells`, `execution_plate_id`, …); nothing sent on a worker connection is a tuple, literal or `None`, and no string is compared as a message kind; the worker command and reply families are exactly the declared members; `ProgressEvent` defines no `to_dict`/`from_dict` and round-trips through its declaration; no progress queue receives `to_dict()`.

## Tests

Touched tests take the new names and types; tests of deleted codecs and enum coverage are deleted; tests that patched the module-level `emit` or `_execute_fork_inherited_worker_lane_static` capture events through the installed progress queue and patch `execute_worker_lane`. Run, each file in its own process: the guards and the witness; 166 affected unit test files; `tests/integration/test_compiled_artifact_inspection.py`; `test_main` disk direct and disk ZMQ (6 cases); official30 parity.

## New-case experiments

- A new worker command today needs a tag literal, a branch in each of two receivers and an unknown-tag error path. After: one `AnsweredWorkerCommand` subclass with `run`.
- A new progress field today needs eight edits. After: one field.
- A new progress context payload today needs a key constant, a lookup, a mapping check and a merge branch. After: one `DeclaredProgressContextPayload` subclass with a `context_key`.
- The remote-sensing witness running over ZMQ today reports `total_wells`/`owned_wells` and filters by `well_filter`. After: `partition_values` and `partition_filter`.

## Handoff (recorded for later surfaces)

- **P (with processing):** `FunctionStepExecutionScope.PLATE` (`callable_contract.py`; spelled in processing and interop) and the `Plate{Input,Output}{File,Directory}` path declarations in `core/vfs_protocol.py` (used by `processing/backends/enhance`). G7 stayed out of processing while L5 rewrites it.
- **W:** the kernel-wide dataset vocabulary outside the runtime modules: `DatasetSource.plate_folder`, `OpenHCSMetadataGenerator.create_metadata(plate_root=…)` and the path planner's `plate_root`/`plate_path`, `WorkspaceSourceProjections.plate_path`, `CompilationPlateScope`, `PlatePathDeclaration`. When W's ratchet covers them, `RUNTIME_FOREIGN_NAMES` shrinks to the P entries.
- **L6 (ObjectState):** `objectstate/context_manager.py` and `dual_axis_resolver.py` still name `well_filter`/`WellFilterConfig` in debug logging and comments (one debug read of `current_global.well_filter_config` is swallowed by a bare `except`).
- **K6:** the bodies of `RuntimeArtifactProgressPayload` and `LiveMeasurementProgressPayload` (and `RuntimeArtifactAddress`/`RuntimeArtifactLocation.to_dict`) are still hand-written; they move to the L2 codec with K6's `to_jsonable` merge.
- **Rule 1a, open:** `ProgressPhase`, `ProgressStatus` and `ProgressChannel` remain enums keying their declaration families, and `PartitionFilterMode` remains a two-member enum (a form choice and a saved-config spelling) that now carries its behaviour. Converting them touches every progress consumer in the GUI and the saved-config spelling of the mode; no surface owns this yet, so it is recorded here for the session lead to assign.

## Done when

The guards pass; the witness, the touched test files (one process each), `test_main` disk direct and disk ZMQ, and official30 parity (30/30) are green.
