# C1: Capability invocation family

**Head audited:** `openhcs` `main` at `c1ec3c5e7` (#1164). **Rules:** [00-RULES.md](00-RULES.md) (including 1a). **Step 2.**
**Shared abstractions** ([02-SHARED-ABSTRACTIONS.md](02-SHARED-ABSTRACTIONS.md)). *Builds:* none. *Uses:* the `AgentCapabilityDeclaration` exemplar (`agent/capabilities.py`).

## What is wrong

**A capability's execution shape is encoded as absence across seven nullable slots, and the MCP server re-derives that shape eleven times, once per slot, with a hand-written binding class beside each generated one.**

- `AgentCapabilityDeclaration` (`agent/capabilities.py:1313`) carries seven `*_invocation: ClassVar[... | None] = None` slots and seven `execute_*` classmethods (`:1363-1438`), each raising `TypeError` when its slot is `None`.
- `mcp/server.py` has 11 `generated_*_capability_declarations()` filters (`:591, 664, 817, 1067, 1233, 1382, 1494, 1627, 1813, 1828, 2083`), each repeating "names of the explicit bindings excluded + `isinstance(declaration.X_invocation, …)`", and pairs 10 `Mcp*BindingABC` registries with 10 `GeneratedMcp*Binding` classes. `build_server` walks the 21 resulting loops (`:2322-2468`).
- 7 explicit server bindings supply what the declaration could own: `HealthCheckMcpToolBinding`, 4 UI list bindings (`UiListCodeDocuments/StateSurfaces/Actions/Windows`, whose declarations declare no invocation at all), `UiGetWidgetTreeMcpToolBinding` (also no invocation), `ViewerProbeMcpToolBinding` (also no invocation). 7 of 108 declarations have no invocation.
- `to_spec()` (`:1441`) copies 21 class attributes into `AgentCapabilitySpec` (`:974`), a dataclass restating the declaration's ClassVars; 12 server call sites and the namespace call it per access.
- `kind = CapabilityKind.TOOL/RESOURCE` is written on 108 declarations although the execution shape (a resource is a no-argument read) decides it.
- `CapabilityCliConnectionProfile` (enum, 4 members) is restated on three base classes and matched by a 4-leaf `GeneratedMcpDevCommandProfile` registry (`mcp/dev_client_commanding.py:818-895`); the profile is a function of the invocation shape (UI connection, viewer connection, runtime-server request, direct).
- Dev client: 66 `cli_command`s, 41 hand-written `CapabilityBackedCommandSpec` subclasses, 25 generated through the profile registry.

## Target

- One `invocation: ClassVar[AgentCapabilityInvocation]` on every named declaration (enforced at class creation). `AgentCapabilityInvocation` is an ABC family; leaves compose input mixins (scalar, from-fields request, dataclass request, ConfigPatch, viewer request) with connection mixins (UI bridge) over the service/function execute owners. Each leaf owns `execute`, its MCP parameters and argument decoding (`tool_parameters`/`invoke`), its registration (`bind_mcp`; the resource mixin registers a resource) and its CLI projection (`configure_cli`/`cli_tool_arguments`/`cli_timeout_seconds`).
- The transport primitives stay in their transport packages and are handed to the invocation as ports: `McpCapabilityBinder` (server.py: tool/resource registration, JSON-schema annotation, UI/viewer connection resolution, selected registry, process health) and `McpDevCliProjection` (dev client argument helpers). The agent package does not import the MCP SDK.
- `build_server` is one loop: `declaration.invocation.bind_mcp(declaration, binder)` for each selected declaration.
- `AgentCapabilitySpec` and `to_spec()` are deleted: the declaration class is the capability. Derived facets (`kind`, `read_only`, `input_type`, `output_type`, `output_contract_types`) are properties of the declaration metaclass; exposition is required and read through `exposition`.
- `kind` is derived from the invocation leaf (rule 1a: the family is the kind). `CapabilityKind` remains only as the wire vocabulary of the MCP search input/output, whose schema (including `prompt`) is an external contract.
- `CapabilityCliConnectionProfile` and the `GeneratedMcpDevCommandProfile` registry are deleted; one `GeneratedCapabilityCommandSpec` asks the invocation.
- Deleted: the 7 slots, 7 `execute_*`, 11 `generated_*` functions, 10 binding ABCs, 10 generated binding classes, 7 explicit bindings (moved onto invocation leaves: server health, viewer-connection-only probe, widget-tree compact projection, UI list connection invocations), `to_spec`, `AgentCapabilitySpec`, `get_agent_capability_declaration` (duplicate of `get_agent_capability`), `kind =` on 108 declarations, `cli_connection_profile`.

## Guards

`tests/unit/agent/test_capability_invocation_guards.py`:
- no `*_invocation` attribute and no `execute_*` method on `AgentCapabilityDeclaration`; no `to_spec`/`AgentCapabilitySpec` anywhere in `openhcs/`;
- no function named `generated_*_capability_declarations` and no class named `Mcp*BindingABC`/`GeneratedMcp*Binding` in `openhcs/mcp/`;
- no `kind =` assignment and no `cli_connection_profile` in any capability declaration;
- every registered declaration has an `AgentCapabilityInvocation`.

## Tests

- **External contract:** `tests/unit/agent/test_mcp_tool_contract.py` compares every tool's name, title, description, annotations, meta and input/output schema, every resource, and the tool set of every transport/profile surface against a fixture generated once from `main` (`fixtures/mcp_tool_contract.json`).
- One family test: every declaration's invocation binds through a recording binder and its CLI projection parses.
- Tests that exercised the deleted binding classes, slots and `execute_*` methods are rewritten against `invocation`; tests of deleted structure are deleted.

## New-case experiments

- Today a capability with a new execution shape needs: a new slot, a new `execute_*`, a binding ABC, a generated binding, a `generated_*` filter, a `build_server` loop pair, and possibly a CLI profile member plus leaf (7 edits in 3 files). After: one invocation leaf (or a mixin composition) in `agent/capabilities.py`.
- Today a UI list capability without a matching invocation needs an explicit server binding. After: it declares `AgentConnectionServiceInvocation`.

## Done when

The guards pass; every declaration declares its invocation; the MCP contract test passes against the `main` fixture; the touched agent/MCP tests pass. The 41 hand-written dev-client command specs that add arguments beyond the invocation's projection remain command-owned; any spec that becomes identical to its generated projection is deleted.

## Outcome

- Also deleted: `validate_capability_registry` (the metaclass now rejects a named declaration without invocation/exposition, with duplicate or empty transports, or with `mutating` disagreeing with `side_effects`, when the class is defined); `RuntimeServerToolRequest` (a marker that existed only to select the runtime-server CLI profile); `optional_jsonable` (exposition is required); the four request-builder methods on `McpViewerConnectionToolArgs`.
- Verified: the MCP contract test passes against the fixture generated from `main` (105 tools, 3 resources, 8 transport/profile surfaces, every schema, annotation and meta). The argparse structure of all 83 dev-client commands is identical to `main` (compared by script).
- The 41 hand-written command specs stay. The ones sampled (`KnowledgeCommandSpec`, `ArchitectureCommandSpec`, `FunctionsCommandSpec`, `ActionsCommandSpec`) add presentation options (`--contains`, `--limit`, renderer flags) and positional aliases that belong to their renderers, not to the invocation; the rest were not audited one by one. Deriving those options from the renderer is recorded for **C2**, which owns the renderers and follows this surface.
- Rule 1a: `CapabilityCliConnectionProfile` is gone (the invocation family is the kind). `CapabilityKind` stays as the wire vocabulary only: the MCP `openhcs_search_capabilities` input schema enumerates `resource`, `tool`, `prompt` and is an external contract; its membership in code derives from the invocation leaf, and the remaining three uses are wire projections (group counts, `non_read_only_tools`). The exposition enums (`CapabilityWorkflowGroup/Stage`, `CapabilityTargetContext`, `CapabilityVisibility`, `CapabilityRole`) carry no per-member behaviour beyond a title and are matched only as search/profile facets that are also MCP schema enums; converting them to families is recorded for **C1b** (not started; needs a derived-enum view that keeps the search schema identical).
- Pre-existing failures observed identically on `main` (not caused here): `test_capabilities.py::test_source_session_capability_owns_progress_heartbeat_policy` (expects 10.0, declaration inherits 1.0), `test_mcp_startup_feedback.py::test_registered_catalog_tool_routes_original_pending_control_statuses_without_native_launch`, the `test_mcp_dev_client_*viewer*` renderer tests (`McpDevToolBatchResponse is missing required field(s): server`, C2's area), `test_mcp_plate_stream_progress.py` collection (`No module named 'test_streaming_service'`).
