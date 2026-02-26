# ZMQ Progress Reporting + Pending Status Plan

## Goals
- Emit detailed per-well/per-step progress from FunctionStep execution over ZMQ.
- Provide percent + phase context (step index, total steps, pattern-group progress).
- Surface “pending” status during plate init and compilation in the Plate Manager.
- Remove legacy progress schema and update all listeners in lockstep (no backward compatibility).

## Non-Goals
- Textual TUI updates (deprecated).
- Backward compatibility with legacy `progress` payloads.

## Current Behavior (Summary)
- ZMQ progress is emitted only via zmqruntime’s `progress_queue`, but nothing in OpenHCS feeds it during execution.
- Orchestrator has a `progress_callback`, but it is only used in the single-process path.
- Multiprocessing path uses `_execute_single_axis_static` and never reports progress.
- Plate Manager only updates per-plate label on completion; no pending state for init/compile.

## New Progress Schema (Strict Migration)
Define a single required schema for all progress messages (no legacy fallback):

Required fields:
- `type`: `progress`
- `execution_id`
- `plate_id`
- `axis_id`
- `step_name`
- `step_index`
- `total_steps`
- `phase` (enum string: `axis_started`, `step_started`, `pattern_group`, `step_completed`, `axis_completed`, `compile`, `init`)
- `status` (enum string: `started`, `running`, `completed`, `error`)
- `completed` (int)
- `total` (int)
- `percent` (float 0–100)
- `timestamp`

Optional fields:
- `pattern` (short pattern repr)
- `component` (group_by component value)
- `message` (human-readable)
- `error` / `traceback`

Example:
```json
{
  "type": "progress",
  "execution_id": "...",
  "plate_id": "/data/plate_01",
  "axis_id": "B06",
  "step_name": "SegmentNuclei",
  "step_index": 2,
  "total_steps": 7,
  "phase": "pattern_group",
  "status": "running",
  "completed": 14,
  "total": 50,
  "percent": 28.0,
  "timestamp": 1700000000.0
}
```

## Implementation Plan

### 1) zmqruntime: Formalize Progress Schema
Files:
- `external/zmqruntime/src/zmqruntime/messages.py`
- `external/zmqruntime/src/zmqruntime/execution/server.py`
- `external/zmqruntime/src/zmqruntime/execution/client.py`

Changes:
- Replace `ProgressUpdate` dataclass to reflect the new schema.
- Add new constants to `MessageFields` for the additional fields.
- Update `ExecutionServer.send_progress_update()` to accept a full progress dict or `ProgressUpdate` and enqueue it unchanged.
- Update `ExecutionClient._progress_listener_loop()` to expect the new schema (fail loudly on missing required fields).

### 2) OpenHCS ZMQ Server: Progress Bridge
Files:
- `openhcs/runtime/zmq_execution_server.py`

Changes:
- Add a helper on `OpenHCSExecutionServer` to emit progress events using the new schema and include `execution_id`/`plate_id`.
- Create a multiprocessing-safe progress queue for worker processes and forward those events into the server’s `progress_queue`.
- Wire that progress queue into the orchestrator execution path so all worker-side progress reaches ZMQ.

### 3) Orchestrator: Progress in Both Threading + Multiprocessing
Files:
- `openhcs/core/orchestrator/orchestrator.py`

Changes:
- Threading path: keep using `progress_callback`, but switch to the new schema payload.
- Multiprocessing path:
  - Add a module-level worker progress reporter that pushes events into a multiprocessing queue.
  - Pass this queue to the ProcessPool initializer (new init arg) and set a global reporter in workers.
  - Emit axis/step start and completion events from `_execute_axis_with_sequential_combinations()` or `_execute_single_axis_static()` using the global reporter.

### 4) FunctionStep: Fine-Grained Progress Events
Files:
- `openhcs/core/steps/function_step.py`

Changes:
- Calculate total pattern groups for the current step/well after `prepare_patterns_and_functions()`.
- Emit a `pattern_group` progress update after each processed group.
- Include `completed`, `total`, and `percent` for step-level progress.
- Emit `step_started`/`step_completed` (or `phase` values) for extra clarity.

### 5) PyQt: Display Rich Progress
Files:
- `openhcs/pyqt_gui/widgets/shared/services/zmq_execution_service.py`
- `openhcs/pyqt_gui/widgets/plate_manager.py`

Changes:
- Update `_on_progress()` to parse the new schema.
- Maintain per-plate progress state (last step name, percent, phase) for list display.
- Update the status bar message format to include `axis_id`, `step_name`, and percent.

### 6) Pending Status During Init + Compile
Files:
- `openhcs/pyqt_gui/widgets/plate_manager.py`
- `openhcs/pyqt_gui/widgets/shared/services/compilation_service.py`

Changes:
- Add per-plate pending flags in Plate Manager (e.g., `init_pending`, `compile_pending`).
- Set `init_pending` when `action_init_plate` begins per plate; clear on success/failure.
- Set `compile_pending` when compile starts in `CompilationService` (before submit); clear on success/failure.
- Update `_format_plate_item_with_preview_text()` to show `⏳ Init` / `⏳ Compile` when pending overrides are active.

## Update Sites Checklist (All Callers)
- Progress schema source of truth: `external/zmqruntime/src/zmqruntime/messages.py`
- Server-side enqueue: `external/zmqruntime/src/zmqruntime/execution/server.py`
- Client-side listener: `external/zmqruntime/src/zmqruntime/execution/client.py`
- OpenHCS ZMQ server execution flow: `openhcs/runtime/zmq_execution_server.py`
- Orchestrator (threading + multiprocessing): `openhcs/core/orchestrator/orchestrator.py`
- Function-step runtime: `openhcs/core/steps/function_step.py`
- PyQt ZMQ progress UI: `openhcs/pyqt_gui/widgets/shared/services/zmq_execution_service.py`
- Plate Manager pending states: `openhcs/pyqt_gui/widgets/plate_manager.py`
- Compilation service pending hooks: `openhcs/pyqt_gui/widgets/shared/services/compilation_service.py`

## Migration Strategy (Strict)
- Replace legacy `progress` payloads immediately; no fallback parsing.
- Update all internal listeners in the same change set.
- Add explicit validation in the progress listener to surface schema mismatches quickly.

## Validation Steps
- Run a small plate with a short pipeline and confirm progress updates show step name + percent.
- Validate pending label transitions: Created -> Init Pending -> Ready, and Ready -> Compile Pending -> Compiled.
- Verify that progress continues to flow in multiprocessing mode.
- Confirm no legacy progress payloads are emitted (grep logs for missing fields).
