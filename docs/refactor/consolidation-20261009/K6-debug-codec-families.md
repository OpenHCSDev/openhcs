# K6: Debug views, debug and progress records on the declared codec; progress and filter kinds as families

**Head audited:** `openhcs` `main` at `84e7a2904` (#1193; L2, G7, W merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Uses:* A2 as built by L2 (python-introspect `to_jsonable`, `dataclass_from_mapping`, `project_dataclass`), zmqruntime `TypedWireMessage`. *Builds:* the decoder half for registered classes (python-introspect), so a family member travels as its registry key and comes back as the class.

## What is wrong

**The debug and progress records restate their own fields in hand-written codecs, the debug view keeps two private copies of the value-to-JSON switch, and eleven kinds are enums keying the families that already carry their behaviour (IMPL-1, MEMB-2, rule 1a).**

Re-measured at `84e7a2904`. L2 already deleted `serialization/json.py` and `DebugJsonCodec`, so of the index's three switches two remain, both in the debug view:

- **Value-to-JSON and cell text, written twice.** `debug_view_models.py:410 debug_view_cell_text` and `:430 debug_view_jsonable`; `debug_views.py:241 _debug_table_cell_text` and `:259 _debug_table_jsonable`. Each re-decides None, scalars, `Enum`, grouping declarations, `ArtifactType` classes, tuples, lists, mappings and dataclasses, and falls back to `str(value)`, beside `to_jsonable`, which already encodes every one of those. `debug_views.py:38-43` re-wraps the two record helpers it imports.
- **Record shapes written by hand (27 codec methods in `core/debug.py`, 6 in `debug_view_models.py`).**
  - `DebugSnapshot.to_json_dict`/`from_json_dict` (`debug.py:859, 884`), `DebugArtifactRef` (`:462, 477`), `DebugArtifactIdentity` (`:570, 582`), `DebugInvocationParameter.from_json_dict` (`:824`): each lists its fields again, twice.
  - `DebugEvent.to_snapshot` (`:1744`) copies 13 shared fields by name; `DebugSession.with_*` (4 methods) and `DebugArtifactRef.with_content_digest` copy every field to change one; `DebugTerminalSummary.from_session` copies 7.
  - Four `Debug*ControlPayload` classes (`:964, 1063, 1155, 1615`) restate their request's fields, convert both ways (`from_request`/`to_request`), and hand-code `to_dict`/`from_dict` with a `"type"` check against `DebugControlMessageType`.
  - Four `Debug*Response.to_control_response`/`from_control_response`, `DebugPausedWorkerStatus.to_dict`/`from_dict` (`:274, 286`), `DebugExecutionConfig.to_config_params`/`from_payload` (`:2151, 2193`, plus `__post_init__` coercions), `DebugViewTable`/`DebugViewSection`/`DebugViewModel.to_json_dict`/`from_json_dict` (`debug_view_models.py:261-405`).
- **Progress payload bodies written by hand (G7 handoff).** `RuntimeArtifactProgressPayload.context_body`/`from_context_body` (`progress/runtime_artifacts.py:39-62`), `LiveMeasurementProgressPayload` and `LiveMeasurementTablePreview` (`progress/live_measurements.py:102-217`), and under them `RuntimeArtifactAddress.from_dict`/`to_dict` (`runtime_stores.py:950-1008`, a 50-line decoder) and `RuntimeArtifactLocation.from_dict`/`to_dict` (`:88-107`). `DebugProgressContext` already derives its body from its declaration (`DeclaredProgressContextPayload`); the other two cannot only because the decoder cannot read a class-valued field (`type[ArtifactType]`, `type[Axis]`).
- **Enums keying families (rule 1a).**
  - Assigned: `ProgressPhase` (14 members), `ProgressStatus` (8), `ProgressChannel` (4) and its `ProgressChannelRole` (2), each a key into a declaration family that already holds the behaviour (`ProgressPhaseDeclarationBase`, `ProgressStatusDeclarationBase`, `ProgressChannelDeclarationBase`, `progress/types.py:25-412`); consumers reach behaviour through `for_phase`/`for_status`/`for_channel` and six free functions (`phase_channel`, `progress_channel_role`, `is_execution_phase`, `is_failure_event`, `is_success_terminal_event`, `is_terminal_event`). 63+56+35+11 production references in 9 files, 174 in 22 test files. `PartitionFilterMode` (`config.py:103`) is a two-member enum carrying three facts through a custom `__new__`.
  - Found in the same files: `DebugViewSectionKind` (11) and `DebugViewTableProjection` (3) key the section and table declaration families; `DebugEventType` keys `DebugBoundaryEventDeclarationBase`, which carries `DebugBoundaryOutcome` and `DebugTimelineNodeState` values; `DebugCommandType` keys `DebugCommandDeclarationBase` and two strategy families; `DebugControlMessageType` names the control payloads; `DebugPausedWorkerState` and `DebugReplayMode` are behaviourless rosters switched on in `DebugPausedWorkerController` and `ProgressDebugExecutionPolicy`.
- **zmqruntime's `TaskProgress`** types `phase`/`status` as `str | Enum` and rejects anything else in `__post_init__` (`messages.py:155-175`), and declares `TaskPhase`/`TaskStatus` enums that nothing reads.

## Target

- **One encoder, one decoder.** python-introspect 0.2.6 decodes a field annotated `type[F]`, where `F` is an `AutoRegisterMeta` family, from the registry key `to_jsonable` writes (`registered_class_from_key`, dispatched on the family's metaclass so a family with its own boundary spelling, the axis family, registers its decoder; the default reads the registry and checks membership). It also supplies `RegisteredClassChoices(family)`, the form-choice view of a registry. Every record above is encoded by `to_jsonable` and decoded by `dataclass_from_mapping`; field copies are `dataclasses.replace` or `project_dataclass`.
- **Debug view.** Cell text is one function over `to_jsonable`'s output (`debug_view_models.debug_view_cell_text`); both private copies and the two re-wrappers are deleted. The section and table declarations key by a plain `name` (the wire spelling); `DebugViewSection.kind`/`DebugViewTable.projection` carry that name, and callers name the declaration class directly.
- **Debug records.** The control requests are the wire messages (`TypedWireMessage`, `wire_type` is the control message type): the four `*ControlPayload` classes and `DebugControlMessageType` are deleted, and `zmq_control` keys its handlers by the request class's `wire_type`. `DebugSnapshot`, `DebugArtifactRef`, `DebugArtifactIdentity`, `DebugPausedWorkerStatus`, `DebugExecutionConfig`, the responses and the view model lose their hand codecs.
- **Kinds are families.**
  - `ProgressPhase`, `ProgressStatus`, `ProgressChannel` become the family bases (registry key `name`, the wire spelling); members are the existing declaration classes (`CompileProgressPhase`, `RunningProgressStatus`, `PipelineProgressChannel`, …). A phase owns its `channel`; a channel is execution by inheriting `ExecutionProgressChannel` (the role enum is deleted); `ProgressEvent` owns `is_failure()`, `is_success_terminal()`, `is_complete()` and `channel`. The six free functions and the `for_*`/`require_*` lookups are deleted.
  - `PartitionFilterMode` is a family with `IncludePartitions` and `ExcludePartitions` carrying `preview_prefix` and `keeps_matches`; the config field holds the class with `RegisteredClassChoices`.
  - `DebugEventType` → the `DebugBoundaryEvent` family (`BeforeInvocation…`, `AfterInvocation…`, `Exception…`), which owns its progress status, outcome and timeline state; `DebugBoundaryOutcome` and `DebugTimelineNodeState` become the names those classes declare. `DebugCommandType` → the `DebugCommand` family, and the two strategy families key by command class. `DebugPausedWorkerState` and `DebugReplayMode` become families whose members own what the controller and policy switch on.
- **zmqruntime 0.6.1.** `TaskProgress.phase`/`status` are typed `object` (the application's vocabulary, encoded by `to_jsonable`); the type check and the unused `TaskPhase`/`TaskStatus` are deleted.

## Persisted state

| Store | Class | At cutover |
|---|---|---|
| Debug snapshots and manifests (`LocalDebugSnapshotStore`, VFS store), debug control messages, progress events and contexts, debug execution config in run requests | runtime | reset; field spellings are unchanged except enum values that were spelled by `.value` and are now spelled by registry key (same strings) |
| Saved global configs and `.py` pipelines naming `PartitionFilterMode.INCLUDE`/`EXCLUDE` | durable | Not converted (no backwards compatibility; same rule as G7-Q1). Such files fail loudly on load and are re-saved from the GUI, which writes `IncludePartitions`/`ExcludePartitions`. |

## Guards

`tests/unit/test_k6_debug_codec_guards.py`:
- No recursive value-to-JSON function under `openhcs/core/debug*.py` or `openhcs/core/progress/`: a function that calls itself and branches on `isinstance` of `Enum`, `Mapping` or a dataclass check is a second encoder. The named copies (`debug_view_jsonable`, `_debug_table_jsonable`, `_debug_table_cell_text`) do not exist anywhere.
- `ProgressPhase`, `ProgressStatus`, `ProgressChannel` and `PartitionFilterMode` are not `Enum` subclasses, and no `Enum` subclass is defined in `core/progress/`, `core/debug.py` or `core/debug_view_models.py`; `ProgressChannelRole`, `DebugControlMessageType` and the `*ControlPayload` classes do not exist.
- No `to_json_dict`, `from_json_dict`, `to_dict`, `from_dict`, `context_body` or `from_context_body` is defined in `core/debug.py`, `core/debug_view_models.py`, `core/debug_views.py` or `core/progress/`.

## Tests

- One round-trip test per record family: every debug record and progress payload through `to_jsonable` and `dataclass_from_mapping`; every progress phase, status and channel and every filter mode through the registry; the library's own round trip for registered classes.
- Tests that built the enums take the classes; tests of deleted codecs and of `for_*` lookups are deleted.

## New-case experiments

- A new debug record field today needs edits in `to_json_dict`, `from_json_dict` and every `with_*` copy (up to 6). After: one field.
- A new progress phase today needs an enum member and a declaration class keyed by it. After: one class.
- A new progress context payload with a class-valued field today needs a hand decoder (`RuntimeArtifactAddress.from_dict` is 50 lines). After: one `DeclaredProgressContextPayload` subclass.

## Done when

The guards pass; the library PRs (python-introspect 0.2.6, zmqruntime 0.6.1) are open with tests green and pinned by submodule; the touched test files pass one per process; the structural ratchet and NRA show no regressions.

## Outcome and corrections

Library PRs: python-introspect #20 (0.2.6), ZMQRuntime #30 (0.6.1); the submodules point at their branch heads.

Corrections to the plan above:

- **Section and table kinds keep a string on the wire.** `DebugViewSection.kind` and `DebugViewTable.projection` hold the declaration's registry `name`, not the class: the view model is decoded by MCP clients that never import the runtime-heavy `debug_views`, whose classes fill the registry. The GUI looks a declaration up by that key. `DebugViewModel.from_debug_snapshot` and `from_runtime_value_store` moved to `debug_views` (`snapshot_view_model`, `RuntimeValuesDebugViewSection.view_model_for_store`), so the module that builds a view is the one that registers its sections.
- **Family names.** `DebugEventType` became `DebugBoundary` (members `BeforeInvocationDebugBoundary`, …); `DebugCommandType` kept its name as the family base, merged with `DebugCommandDeclarationBase`, and each command owns `apply_to_worker` (the controller's `if`/`elif` over commands is deleted); `DebugPausedWorkerState` became `DebugWorkerState`; `DebugReplayMode` members own `retains_compile_artifact` and `keeps_worker_paused`.
- **Deleted as dead, not converted.** `DebugBoundaryOutcome`, `DebugTimelineNodeState`, `DebugTimelineNode`, `DebugRuntimeProjection.timeline` and `node_state_for_cursor` had no production reader. The `DebugSessionRequest` registry (`request_kind`) was never read.
- **Control requests are the wire messages.** The four `*ControlPayload` classes are deleted; each request subclasses zmqruntime's `TypedWireMessage` with its `wire_type`; the four responses share one `DebugControlResponse` envelope. `DebugWorkerCommandResponse.status` is renamed `worker` (its field collided with the envelope's `status`).
- **`DebugStoreManifest`** is `debug_session_id` plus `snapshot_ids`, the shape it was written as; it no longer reads every snapshot to list ids.
- **`_json_safe_cell`** in live measurements (renamed `_preview_cell`) stays: it bounds and stringifies arbitrary measurement cells for display, which `to_jsonable` deliberately does not.

Out of scope, found here (no open surface owns them; recorded for the session lead): GUI debug enums `DebugActionPlacement`, `DebugToolbarAuxiliaryAction` (`pyqt_gui/widgets/shared/services/pipeline_debug_actions.py`) and `DebugSessionPhase` (`core/debug_session_projection.py`); `CompiledArtifactInspectionControlPayload` (`core/artifact_inspection.py`) restates its request like the deleted debug payloads; numpy JSON projections in `core/plate_image_inventory.py` and `napari_roi_manager/_dataclasses.py`.
