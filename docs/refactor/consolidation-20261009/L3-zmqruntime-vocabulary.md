# L3: zmqruntime owns its runtime vocabulary, launch policy and transport config

**Head audited:** `openhcs` `main` at `89b8fdbff` (#1185); `zmqruntime` `main` at `079a1c4` (0.5.0); `pyqt-reactive` `main` at `291b1be` (0.3.30); `PolyStore` `main` at `45a9bc1` (0.5.0). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* zmqruntime's declared-message base. *Uses:* the L2 codec (`python_introspect.to_jsonable`, `dataclass_from_mapping`), `AutoRegisterMeta`.

## What is wrong

**A generic runtime library speaks one domain's words, writes its codec by hand 45 times, and two pieces of its own machinery live in its consumers.**

- **Domain words.** 107 microscopy tokens in six zmqruntime modules: `plate_id` on `TaskProgress`, `ExecuteRequest`, `ExecutionRecord`, `RunningExecutionInfo`, `QueuedExecutionInfo` (`messages.py`, 29); `GenericPlateProjection`, `plates`, `by_plate_latest`, `get_plate`, `adapter.plate_id` (`progress/projection.py`, 60); `MessageFields.WELL_COUNT/WELLS/WELL_ID` and the results summary written with them (`execution/server.py:289-290`); `execution_plate_id`. The kernel's word for the values of the parallel axis is `partition_values` (G2: `ZMQCompilationRequest.partition_values`).
- **Hand-written codec.** `messages.py` defines 24 `to_dict` and 21 `from_dict` (45) over 21 message dataclasses. Each restates its field list two or three times; strictness differs per class (`WorkerState` rejects unknown keys, `ExecutionRecord` sweeps them into `metadata`, the rest drop them); `ExecutionRecord.to_dict` carries a private `_to_transport_value` encoder, a fourth encoder beside `to_jsonable`. `PongResponse.from_dict` is 98 lines.
- **Launch policy in a widget library.** `pyqt_reactive/process_launch.py` (standard-library only) owns console suppression and detached sessions for every background process. Ten openhcs call sites in six production modules (`gui_startup`, `processing/backends/lib_registry/registry_service`, `desktop/restart`, `desktop/update`, `runtime/zmq_execution_client`, `runtime/viewer_protocol`) and three in pyqt-reactive (`log_highlight_client`, `system_metrics_sampler` x2) import a process policy from a Qt library. The policy is an enum (`BackgroundProcessPlatform.WINDOWS/OTHER`) with `if platform is WINDOWS` branches in `resolve` and `python_executable` (rule 1a).
- **Transport config in the application.** `openhcs/runtime/zmq_config.py` (`OpenHCSZMQConfig`, 119 lines) declares twelve generic execution-endpoint fields (hosts, transport mode, request deadlines, discovery scan, readiness poll, port range, artifact TTL) and `client_endpoint`. zmqruntime's own base client reads `config.server_poll_interval_seconds` (`client.py:1291`), a field its `ZMQConfig` does not declare.
- **Compatibility shims** in the execution server: `_run_execution` and `_handle_status` ("Compatibility shim for callers still bound to the old private hook").
- **Dead:** `ROIMessage`, `ShapesMessage` (no reader outside their own module), `MessageFields.WELL_ID`.

## Target

- **Vocabulary.** `plate_id` → `subject_id` (what one execution request is about), `execution_plate_id` → `execution_subject_id`, `GenericPlateProjection` → `GenericSubjectProjection` (`subjects`, `by_subject_latest`, `get_subject`, `adapter.subject_id`). The results summary carries `partition_count`/`partition_values`. No microscopy word remains in zmqruntime.
- **Declared messages.** One base, `WireMessage`: `to_dict()` is `to_jsonable(self)`, `from_dict()` is `dataclass_from_mapping(cls, data)`. Two capabilities compose on it: `TypedWireMessage` (a `wire_type` class attribute carried under `type`) and `WireView` (a declared message read out of a wider payload, for application progress envelopes and status responses). Control requests derive their body from their declared fields under `ControlRequestHeader`, which alone encodes the relative observation budget. No message class writes `to_dict`/`from_dict`. `ExecutionRecord`'s server-local attachments (`extras`, `progress_event`) stop being dataclass fields, so its declared fields are exactly its wire record.
- **Launch policy** moves to `zmqruntime.process_launch`. `BackgroundProcessPlatform` becomes an `AutoRegisterMeta` family keyed by `sys.platform`: `WindowsBackgroundProcesses` owns creation flags and the `pythonw.exe` interpreter; the default family member owns `start_new_session`. pyqt-reactive and openhcs import it from zmqruntime; `pyqt_reactive/process_launch.py` is deleted.
- **Transport config** moves to `zmqruntime.execution.config.ExecutionTransportConfig(ZMQConfig)`; `server_poll_interval_seconds` moves onto `ZMQConfig`, where the base client reads it. `OpenHCSZMQConfig` keeps only OpenHCS's two names (`app_name`, `ipc_socket_prefix`), so saved UI preferences that name the type load unchanged.
- **Deleted:** the 45 methods, `_to_transport_value`, `ExecutionRecord.metadata` as a field, `ROIMessage`, `ShapesMessage`, `MessageFields` keys no reader uses, both compatibility shims, `pyqt_reactive/process_launch.py`, the generic fields of `OpenHCSZMQConfig`, and openhcs's hand-assembled `ExecuteRequest` items.

## Persisted state

Runtime only (ZMQ messages between processes of one install). The UI preference file stores `OpenHCSZMQConfig` field values; every field keeps its name and owner type, so it loads unchanged.

## Releases

zmqruntime 0.6.0 (breaking); pyqt-reactive 0.4.0 (drops `process_launch`, `zmqruntime>=0.6,<0.7`); PolyStore 0.6.0 (`zmqruntime>=0.6,<0.7`).

## Guards

`tests/unit/test_l3_zmqruntime_vocabulary_guards.py`:
- No microscopy word (`plate`, `well`) in any `external/zmqruntime/src` module.
- No class in `zmqruntime.messages` defines `to_dict` or `from_dict` except the declared bases.
- `pyqt_reactive/process_launch.py` does not exist; nothing under `openhcs/` imports `pyqt_reactive.process_launch`.
- `OpenHCSZMQConfig` declares no field beyond `app_name` and `ipc_socket_prefix`.

## Tests

- zmqruntime: one round-trip test over every declared message (registry of `WireMessage` subclasses), one test that a typed message rejects another type, one for envelope reading, the launch-policy family test (moved from pyqt-reactive), the transport config validation test.
- openhcs: the existing ZMQ execution, progress and streaming tests; tests that built wire dicts by hand use the declared types.

## New-case experiments

- A new control message: today a dataclass plus a hand-written `to_dict`/`from_dict` pair restating its fields and its `type`. After: the dataclass under `ControlRequestHeader` or `TypedWireMessage`.
- A non-microscopy application (the remote-sensing witness) submitting work: today its request is about a `plate_id` and its results report `wells`. After: `subject_id` and `partition_values`.
- A new host family for background processes: today an enum member plus a branch in two methods. After: one subclass.

## Done when

The guards pass; the three library PRs are open with CI green; openhcs points at the PR branches and its runtime, ZMQ and streaming tests, the `test_main.py` disk ZMQ cases and the Official30 parity check over ZMQ (29/30) pass.
