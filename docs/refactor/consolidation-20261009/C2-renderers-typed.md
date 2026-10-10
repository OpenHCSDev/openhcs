# C2: MCP CLI renderers consume their DTOs

**Head audited:** `openhcs` `main` at `1c1059867` (#1172). **Rules:** [00-RULES.md](00-RULES.md) (including 1a, 1b). **Step 2**, after C1 (#1167).
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* the `McpDevTypedOutputRenderer` exemplar (`mcp/dev_client_rendering.py:280`), `McpDevToolBatchResponse.for_rendering`, the capability invocation family (C1).

## What is wrong

**A migration stopped halfway: every renderer declares its output DTO, but 40 renderer classes (42 output contracts) ignore it and read the JSON dict by key.**

- `mcp/dev_client_renderers/*.py`: 40 classes subclass the untyped `McpDevOutputRenderer` (knowledge 9, object_state 4, plate 7, ui_bridge 15, viewer 5 of which two carry five contracts through `render_bindings`/`render_function`). Together: 724 `.get(` reads and 718 `McpDevPayloadProjection.*` calls. The worst: `PlateInspectionRenderer`, `WidgetTreeOutlineRenderer`, `PipelineDebugSessionStateSurfaceRenderer`, `ObjectStateFieldRenderer`.
- The typed base `McpDevTypedOutputRenderer` (decodes once through `McpDevToolBatchResponse.for_rendering`, renders `render_payload(DTO)`) is used by 23 renderers. Two bases, two ingress paths (`render(dict)` and `render_result(response)`), and a binding object (`McpDevOutputRendererBinding`) that forwards every call to the renderer type.
- A copied preamble: each raw renderer re-implements "payload None → `json.dumps`; payload errors → `X: unavailable`" (16 copies in `ui_bridge.py`), plus six private `_append_messages`/`_error_lines` copies printing the payload's errors and warnings.
- The `UiPlateManagerRowState` row is presented twice in the CLI: the dict renderer (`PlateManagerStateSurfaceRenderer._row_lines`) and a second typed formatter in `dev_client_commands/ui.py:504` (`SelectedWorkflowCommandSpec._row_lines`). (The DTO and the GUI mapper are the other two restatements; the GUI mapper is outside this surface.)
- The CLI side restates renderer options: commands override `renderer_options` and `call_render_args` (11 copies) and add the same flags the options types declare; `--json` is added by hand in 47 places.
- 10 `test_mcp_server` tests build raw-dict responses that the typed ingress rejects (`McpDevToolBatchResponse is missing required field(s): server`).
- `benchmark/agent_validation/mcp_attempt_recorder.py` imports `first_payload_mapping`, removed in #400 (`ImportError` at collection).

## Target

- One renderer base, `McpDevOutputRenderer`, registered by output DTO (`AutoRegisterMeta`, key = the class body's `output_contract`). `render(response, options=None)` is the single ingress: decode the batch once, render the first decoded payload with the renderer registered for that payload's type, or `unavailable_summary` when there is none; append the payload's `AgentWarning`s and the batch's diagnostic errors. Subclasses implement only `render_payload(payload: DTO, options)` and read attributes.
- One renderer class per output contract; shared presentation is inherited from a common parent, never a second registration mechanism.
- Renderer options are declared by the renderer (`render_options_type`); the options type declares its CLI flags (`configure_cli_parser`/`from_cli_args`) and its defaults are what a generic `call` renders with. `--json` is declared once on `McpDevCommandSpec`.
- The plate-manager row is presented by the state-surface renderer only; the workflow command reuses it.
- Deleted: `McpDevTypedOutputRenderer` (merged into the base), `McpDevOutputRendererBinding`, `render_bindings`, `render_function`, `render_with_options`, `render_result` on renderers, `McpDevPayloadProjection`, `McpDiagnosticRenderer` (one `diagnostic_lines` function remains), every `_append_messages`/`_error_lines` copy, `TypedCompositeCommandSpec`, `render_response` on commands, `renderer_options`/`call_render_args` overrides, the hand-written `--json` flags.
- C1 handoff: each of the 41 hand-written `CapabilityBackedCommandSpec`s is audited against `GeneratedCapabilityCommandSpec`; a spec whose parser and tool arguments equal the invocation's projection is deleted; presentation flags move to the renderer's options type.

## Guards

`tests/unit/agent/test_mcp_renderer_guards.py`:
- no `McpDevPayloadProjection`, `McpDevTypedOutputRenderer`, `McpDevOutputRendererBinding`, `render_bindings`, `render_function`, `first_tool_payload`, `first_mapping_payload`, `first_payload_mapping` in `openhcs/`, `benchmark/`, `scripts/`;
- no `.get(` call on a value in `openhcs/mcp/dev_client_renderers/`;
- every `McpDevOutputRenderer` subclass that declares `output_contract` overrides `render_payload` and none overrides `render`;
- no renderer module references `AgentError`/`AgentWarning` presentation (`errors`/`warnings` attributes) — the base owns them;
- `"--json"` appears once in `openhcs/mcp/dev_client_command*`.

## Tests

- One family test: every registered renderer renders a payload built from its DTO class (`tests/unit/agent/test_mcp_dev_client_renderers.py`), plus a handful of behaviour tests per renderer family over typed fixtures (filters, truncation, outline selection, row presentation).
- The external contract `tests/unit/agent/test_mcp_tool_contract.py` stays green (the CLI and renderers are not on the MCP wire).
- Raw-dict renderer tests in `test_mcp_server.py` are deleted with the dict readers.

## New-case experiments

- Today a new output DTO with a compact view needs: a renderer class, a dict reader per field, its own None/errors preamble, its own warnings printer, and, if its command takes presentation flags, a `renderer_options` and `call_render_args` override plus the flags on the command (5 places). After: one `McpDevOutputRenderer` subclass with `output_contract` and `render_payload`, and optionally its options type.

## Done when

The guards pass; no renderer reads a dict; the tool contract test passes; the renderer, command and attempt-recorder tests pass.

## Outcome

- One base, `McpDevOutputRenderer` (the typed exemplar merged into the registry root). 63 registered renderers, one per output DTO; every one implements only `render_payload` and reads attributes. Multi-contract renderers were split (`ViewerNavigation`/`ViewerLayerIsolation`, `RuntimeServerInfo`/`Scan`/`ExecutionStatus`). State-surface documents decode their body into the surface's declared state DTO (`UiPlateManagerState`, `UiPipelineEditorState`, `UiPipelineDebugSessionState`, `UiLiveOverviewState`) through `UiStateSurfaceStateRenderer`, keyed by the surface identity declaration.
- The base owns the preamble: unavailable summary, `Warnings:` (every `AgentWarning` in the payload; a renderer may narrow it through `presented_warnings`, as the widget-filtered action catalog does) and `Errors:`.
- Renderer options declare their own CLI flags (`--contains/--limit`, `--no-source/--max-source-chars`, `--max-chars`, `widget_id`, `--outline-root-class/--include-technical-widgets`); `--json` is declared once (`configure_json_option`; widget-tree overrides it as its `--output json` alias). The argparse structure of all 82 subcommands is identical to `main` (compared by script).
- The plate-manager row is presented once (`PlateManagerStateSurfaceRenderer.row_lines`), reused by `selected-workflow --wait`. Workflow polling reads `UiPlateManagerState`/`UiPlateManagerRowState`; `WorkflowPollRowState` (a fifth, partial restatement of the row read by key) and `optional_bool/int/str` are deleted.
- Also fixed: a single `AgentError` held as a record field (`disabled_error`) no longer counts as a call failure, so `ui-actions` no longer exits nonzero when an action is disabled; already-decoded payloads are no longer re-decoded at every view; `mcp_attempt_recorder` reads typed payloads (`decoded_payload_as`); `installed_demo.py` and `scripts/smoke_installed_gui.py` read DTOs. Rule 1b: `McpDevPayloadFailure.receipt` → `payload`, `McpToolArgumentAuthority` → `McpToolArguments`.
- C1 handoff: of the 41 hand-written command specs, 3 were identical to the generated projection once presentation flags moved to the options types and are deleted (knowledge, architecture, actions). 38 stay: 14 build a CLI request type but add positionals, inverse flags, stdin/file source input or composite polling; 24 take a request that is not an `AgentCliRequest`, so the invocation has no CLI projection to generate. Deleting them needs their request DTOs to declare those spellings as CLI argument specs (`agent/dto`, owner: C1b or a follow-on CLI surface).
- Remaining JSON key reads, all on `JsonObject` fields no class models: 9 in `plate.py` (`json_member`: file-stat `size`/`modified`, CSV preview rows, ROI examples, source diagnostics) and 1 in `installed_demo.py` (record metadata by axis name). Typing them changes the MCP output schema; recorded for the plate DTO owner.
- Out of scope, found: `agent/services/selected_plate_service.py` reads plate-manager rows by key (owner: UI bridge services); the GUI mapper is the fourth restatement of the plate-manager row (pyqt_gui).
