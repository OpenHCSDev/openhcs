# U1: The session interface

**Head audited:** `openhcs` `main` at `66a0b30a0` (#1182). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.** Takes over G8.
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "The UI: one session interface, thin renderers" and "Authoring surfaces (surface G8)". *Builds:* `Session`, the `SessionOperation`, `SessionView` and `SessionEvent` families in `openhcs/authoring/session`, `GridAddressed`, `PipelineImporter`, `DatasetScopeKind`. *Uses:* `AgentCapabilityDeclaration`, `AutoRegisterMeta`, ObjectState, G1's `AxisFamily.with_role`, pyqt-reactive's `AsyncOperationExecutor`.

## What is wrong

**OpenHCS's session semantics (which datasets exist, what is pending, compiled or running, and what each button does) live in two Qt widgets, the agent interface reaches them by calling widget methods, and the headless MCP path re-implements add, compile, run and stop in a second store with different semantics (IMPL-1, IMPL-2, MEMB-2, IDEN-1).**

- **Widget-held session state.** `PlateManagerWidget.__init__` (`pyqt_gui/widgets/plate_manager.py:628-710`) holds `plate_configs` (:661), `plate_compiled_data` (:662), `_execution_state` (:663), `_active_debug_sessions` (:664), `plate_terminal_activity_status` (:669), `plate_init_pending` (:674), `plate_compile_pending` (:675), `runtime_progress_projection`/`debug_runtime_projection` (:676-677), `selected_plate_path` (:660) and the debug snapshot/summary dicts (:650-654). Workflow services treat the widget as their `host`: 26 distinct `host.*` members are read across `pyqt_gui/widgets/shared/services/*.py` and `plate_manager_batch_workflow.py` (`plate_terminal_activity_status` 17 times, `emit_status` 15, `update_item_list` 10). `PipelineEditorWidget` (`pipeline_editor.py:449-507`) mirrors ObjectState's step list into `pipeline_steps` (:464, 13 write sites) and keeps `current_plate`, `debug_session_state`, `debug_terminal_summary`.
- **Agent actions are widget lambdas.** `agent/ui_bridge_actions.py` declares `PlateManagerAction` (:135) with 11 `lambda widget: widget.action_*` handlers, `MainWindowAction` (:40) with 6 `lambda window:` callables, `PlateOperation` (:20) and `CompilationActionProjection`; `PipelineEditorAction` (`pipeline_editor.py:208`) and `PipelineEditorActionTargetMode` (:171) are the same pattern. All are `str, Enum` rosters whose members carry callables; `PlateOperationValidator` (`plate_manager.py:398-494`) is a side table keyed by `PlateOperation`. The bridge provider dispatches through the widget (`ui_bridge_plate_manager.py:939`, `dispatch_widget_action`) and reads availability from `button.isEnabled()` (:1088).
- **Two implementations of add, compile, run and stop.** GUI: `add_plate_callback` (`plate_manager.py:1149-1219`), copied in `PlateManagerCodeWorkflow.ensure_plate_entries` (`plate_manager_workflows.py:234-264`) and `_maybe_auto_add_output_plate_orchestrator` (`plate_manager.py:1762-1827`); compile and run through `PlateManagerBatchWorkflow` (`plate_manager_batch_workflow.py:97-199`). Headless: `ExecutionSessionService` (`agent/services/execution_session_service.py:782-1245`) keeps `ExecutionSessionStore`/`ExecutionJobStore` dicts, builds a new ZMQ client per job and has no init, no batch, no pending state. Stop differs (GUI shuts the endpoint down, `execution_control_service.py:95-123`; headless cancels one job, `execution_session_service.py:1144`). Streaming builds its context twice (`image_browser.py:513-527` from the orchestrator; `plate_streaming_service.py:84-320` from an inspection context).
- **Polling instead of events.** Action results advise `recommended_poll_interval_ms=500` (`ui_bridge_plate_manager.py:964`, `ui_bridge_pipeline_editor.py:181,443`); the dev client polls state surfaces every 0.5 s (`mcp/dev_client_core.py:85`, `dev_client_commands/ui.py:340-390`); the GUI polls each execution's status every 0.5 s (`execution_submission_service.py:166`).
- **MCP DTOs import pyqt-reactive.** `agent/dto/ui_bridge.py:12,21` and `agent/dto/viewer.py:14` import it directly; `ui_bridge.py:58` imports `PlateManagerAction`.
- **G8: the authoring surfaces name microscopy members.**
  - `well:` filters on five plate DTOs (`agent/dto/plate.py:152,319,323,387,391`) and the `well_filter` alias fallback (`agent/dto/execution.py:199-202`, `mcp/dev_client_commands/knowledge_pipeline.py:374-379`).
  - `microscope_type` restated on five request DTOs (`agent/dto/plate.py:137,201,249,319,387`).
  - Grid placement: `Axis.grid_coordinates` (`core/axes.py:335`) is on every axis instead of a role; the letter-to-index decode is written three times (`plate_view_widget.py:181-191`, `image_browser.py:1513-1517,1626-1632`) and the 96-well default three times (`plate_view_widget.py:129,156,827`).
  - `.cppipe` import is a suffix `if` (`pipeline_editor.py:954-961`) and a second import path in the plate manager (`plate_manager.py:2591`).
  - The CellProfiler scope kind is a string marker tested by `cppipe_path is None` (`ui/shared/plate_scope_identity.py:10,27,35`; branch sites `plate_manager.py:230-295,909,927-955`).

## Target

```python
# openhcs/authoring/session/
class SessionEvent(ABC, metaclass=AutoRegisterMeta): ...    # frozen; DatasetsChanged, DatasetStateChanged,
                                                            # CompiledStateChanged, ExecutionStateChanged, Status, Error, ...
class SessionOperation(AgentCapabilityDeclaration):        # one declaration: MCP tool, Qt button, bridge action
    request: ClassVar[type]; result: ClassVar[type]
    def available(self, session) -> AgentError | None: ...
    def run(self, session, request): ...
class SessionView(ABC, metaclass=AutoRegisterMeta):
    state: ClassVar[type]                                   # frozen DTO derived from ObjectState + session runtime
    operations: ClassVar[tuple[type[SessionOperation], ...]]
class Session:
    def invoke(self, operation, request): ...
    def view(self, view): ...
    def events(self, after: int = 0, timeout: float | None = None) -> tuple[SessionEvent, ...]: ...
    def subscribe(self, listener) -> Callable[[], None]: ...
```

- **One owner of session state.** Datasets, per-dataset `PipelineConfig` and pipeline steps stay in ObjectState (they are already there). Runtime state (pending init/compile, compiled artifacts, execution batch, debug sessions, runtime projections, selection) moves onto `Session`. Widgets hold a `session` reference and nothing else of session state. `plate_configs` is deleted: ObjectState already owns per-plate `PipelineConfig`.
- **The workflow engine moves** from `pyqt_gui/widgets/shared/services` and `pyqt_gui/services/plate_manager_*` into `openhcs/authoring/session`, with `host` replaced by the `Session`; the Qt progress timer becomes event publication.
- **Operations are classes.** Every `PlateManagerAction`, `MainWindowAction` and `PipelineEditorAction` member becomes a `SessionOperation` subclass carrying its label, tooltip, side effects, availability and `run`. Operations that only open a window (`edit_config`, `code_plate`, `view_results`, `view_metadata`, the main-window actions, the step editor) inherit `RendererOperation`: `run` asks the attached renderer, and they are unavailable on a session with none. `PlateOperation`, `PlateOperationValidator`, `CompilationActionProjection`, `ManagerButtonPresentationMixin`, `ACTION_ROUTES` and `dispatch_widget_action` routes over enums are deleted; the GUI binds buttons from `view.operations`, the bridge provider calls `session.invoke`.
- **Headless MCP is a session with no renderer.** `OpenHCSAgentContext.session` builds one; the dataset operations are MCP tools. `ExecutionSessionService`'s session and job stores (`create_session*`, `get_session`, `submit_compile`, `submit_execution`, `get_job_status`, `wait_job`, `cancel_job`) and their six capabilities are deleted; artifact-plan inspection stays.
- **Push events.** `Session.events(after, timeout)` blocks until an event arrives; MCP exposes it as one tool; the 500 ms advisory fields are deleted.
- **G8.** `component_filters: Mapping[str, tuple[str, ...]]` validated against `AxisFamily.active()` replaces `well`; the `well_filter` alias is deleted; `source_format` is declared once on a `DatasetTarget` base; `GridAddressed(AxisRole)` owns `grid_coordinates`/`grid_index` and the default grid; the plate grid is shown only when the family has a grid axis; `PipelineImporter` (keyed by suffix; `.py` in OpenHCS, `.cppipe` registered by interop) replaces the suffix `if`; `DatasetScopeKind` (plain dataset, CellProfiler pipeline scope) replaces the marker tests.

## Decisions (defaults taken)

1. **Init stays an operation.** The session initializes datasets locally (GUI semantics); the headless journey is add → init → compile → run.
2. **Stop keeps GUI semantics** (stop the batch); headless per-job cancel is subsumed.
3. **Run recompiles before submission** (GUI semantics); the MCP run request keeps the runtime-observation export fields.
4. **Runtime state is not ObjectState.** Pending flags and compile artifacts in undo history would let time travel restore a running batch; they live on `Session` and are reset at construction (rule 2: runtime state).

## Guards

- No widget class under `openhcs/pyqt_gui` assigns an attribute named in the session-state set (`plate_configs`, `plate_compiled_data`, `plate_init_pending`, `plate_compile_pending`, `plate_terminal_activity_status`, `_active_debug_sessions`, `pipeline_steps`, `selected_plate_path`, `execution_state`).
- `openhcs/authoring/session` imports no `PyQt6` and no `openhcs.pyqt_gui`.
- No `lambda widget`/`lambda window` handler, no `Enum` subclass with callable members in `agent/ui_bridge_actions.py` (deleted) or `openhcs/authoring`.
- Importing every `openhcs.agent.dto` module loads no `PyQt6` module.
- No `well_filter`, no `well:` DTO field, no `microscope_type` field outside `DatasetTarget`.
- No `.cppipe` suffix comparison outside `openhcs/interop`.

## Tests

- One family test over `SessionOperation`: every operation declares label, request/result, `available`, and is an MCP tool exactly when it is not a `RendererOperation`.
- A headless journey (session with a fake execution client): add dataset → init → compile → run, observing events, and the same journey through the GUI's session offscreen.
- Existing widget and bridge tests are rewritten against the session; tests of deleted structure (enum members, widget dict shapes, `ExecutionSessionService` stores) are deleted.

## New-case experiments

- **A new dataset action** (for example "duplicate dataset"): today an enum member with a widget lambda, a widget method, a validator entry, a bridge summary path and an MCP route — five edits in four files. After: one `SessionOperation` subclass.
- **A new authoring client** (a TUI): today it re-implements availability, the run loop, add and the compiled dict (the deleted Textual TUI did, `32ca17c17`). After: it renders `SessionView`s and calls `Session.invoke`.

## Done when

The guards pass with zero exceptions; `agent/ui_bridge_actions.py` is deleted; the GUI and headless MCP add, compile and run through the same `SessionOperation` classes; the touched widget, bridge and MCP tests and the MCP contract tests pass; the headless and GUI journeys pass.

## Dispatch

> **`U1`:** Build `openhcs/authoring/session`, move the plate-manager and pipeline-editor semantics and the workflow engine into it, make widgets and headless MCP clients of it, and land G8. Traps: the workflow engine calls back into the widget through 26 `host` members; the headless execution tools are used by the benchmark CLI and demos.
