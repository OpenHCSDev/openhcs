# U2: The UI-bridge contract family derives its gateways

**Head audited:** `openhcs` `main` at `df687fc68` (#1187, U1 merged). **Rules:** [00-RULES.md](00-RULES.md). **Step 4.**
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "The UI: one session interface, thin renderers", row U2. *Builds:* the `UiBridgeOperation` family (one class per operation: request, result, failure answer, feature tag), one generic `invoke` per gateway kind, one `UiBridgeService.invoke`, capabilities derived from `operation`, one `UiActionProvider` base. *Uses:* `AutoRegisterMeta`, `AgentCapabilityDeclaration`, U1's `Session` events and `SessionView`.

## What is wrong

**Each of the 26 running-UI bridge operations is written six to seven times: a contract class, an abstract gateway method, the unavailable, ZMQ and in-process gateway methods, a service method, and an MCP capability that restates the contract's request and result types and forwards to the service method by name (IMPL-1, MEMB-2).** Census at `df687fc68` (file:line of every restatement; the last column is the in-process implementation, which is the operation's one real body):

| Operation | Restatements | Sites | Implementation |
|---|---|---|---|
| `status` | 7 | contract ui_bridge_service.py:613; abstract gateway ui_bridge_service.py:359; unavailable gateway ui_bridge_service.py:972; ZMQ gateway ui_bridge_transport.py:210; in-process gateway ui_agent_bridge.py:2146; service ui_bridge_service.py:1979; capability capabilities.py:3377 | ui_agent_bridge.py:1648 |
| `list_documents` | 7 | contract ui_bridge_service.py:622; abstract gateway ui_bridge_service.py:363; unavailable gateway ui_bridge_service.py:987; ZMQ gateway ui_bridge_transport.py:214; in-process gateway ui_agent_bridge.py:2150; service ui_bridge_service.py:2012; capability capabilities.py:3395 | ui_agent_bridge.py:1655 |
| `list_state_surfaces` | 7 | contract ui_bridge_service.py:633; abstract gateway ui_bridge_service.py:370; unavailable gateway ui_bridge_service.py:993; ZMQ gateway ui_bridge_transport.py:223; in-process gateway ui_agent_bridge.py:2156; service ui_bridge_service.py:2026; capability capabilities.py:3412 | ui_agent_bridge.py:1667 |
| `list_actions` | 7 | contract ui_bridge_service.py:644; abstract gateway ui_bridge_service.py:377; unavailable gateway ui_bridge_service.py:999; ZMQ gateway ui_bridge_transport.py:232; in-process gateway ui_agent_bridge.py:2163; service ui_bridge_service.py:2040; capability capabilities.py:3461 | ui_agent_bridge.py:1678 |
| `list_windows` | 7 | contract ui_bridge_service.py:653; abstract gateway ui_bridge_service.py:384; unavailable gateway ui_bridge_service.py:1005; ZMQ gateway ui_bridge_transport.py:241; in-process gateway ui_agent_bridge.py:2167; service ui_bridge_service.py:2054; capability capabilities.py:3530 | ui_agent_bridge.py:1697 |
| `list_object_state_scopes` | 7 | contract ui_bridge_service.py:662; abstract gateway ui_bridge_service.py:391; unavailable gateway ui_bridge_service.py:1011; ZMQ gateway ui_bridge_transport.py:250; in-process gateway ui_agent_bridge.py:2171; service ui_bridge_service.py:2068; capability capabilities.py:3700 | ui_agent_bridge.py:1716 |
| `describe_object_state_field` | 6 | contract ui_bridge_service.py:679; abstract gateway ui_bridge_service.py:399; unavailable gateway ui_bridge_service.py:1018; ZMQ gateway ui_bridge_transport.py:262; in-process gateway ui_agent_bridge.py:2179; service ui_bridge_service.py:2094 | ui_agent_bridge.py:1742 |
| `mutate_object_state_field` | 7 | contract ui_bridge_service.py:696; abstract gateway ui_bridge_service.py:407; unavailable gateway ui_bridge_service.py:1025; ZMQ gateway ui_bridge_transport.py:277; in-process gateway ui_agent_bridge.py:2187; service ui_bridge_service.py:2112; capability capabilities.py:3788 | ui_agent_bridge.py:1755 |
| `get_document` | 7 | contract ui_bridge_service.py:713; abstract gateway ui_bridge_service.py:415; unavailable gateway ui_bridge_service.py:1032; ZMQ gateway ui_bridge_transport.py:292; in-process gateway ui_agent_bridge.py:2195; service ui_bridge_service.py:2133; capability capabilities.py:3821 | ui_agent_bridge.py:1793 |
| `get_state_surface` | 7 | contract ui_bridge_service.py:725; abstract gateway ui_bridge_service.py:423; unavailable gateway ui_bridge_service.py:1039; ZMQ gateway ui_bridge_transport.py:302; in-process gateway ui_agent_bridge.py:2203; service ui_bridge_service.py:2147; capability capabilities.py:3434 | ui_agent_bridge.py:1800 |
| `invoke_action` | 7 | contract ui_bridge_service.py:739; abstract gateway ui_bridge_service.py:431; unavailable gateway ui_bridge_service.py:1046; ZMQ gateway ui_bridge_transport.py:314; in-process gateway ui_agent_bridge.py:2211; service ui_bridge_service.py:2164; capability capabilities.py:3476 | ui_agent_bridge.py:1809 |
| `focus_window` | 7 | contract ui_bridge_service.py:751; abstract gateway ui_bridge_service.py:439; unavailable gateway ui_bridge_service.py:1053; ZMQ gateway ui_bridge_transport.py:341; in-process gateway ui_agent_bridge.py:2227; service ui_bridge_service.py:2195; capability capabilities.py:3545 | ui_agent_bridge.py:1878 |
| `navigate_window` | 7 | contract ui_bridge_service.py:763; abstract gateway ui_bridge_service.py:447; unavailable gateway ui_bridge_service.py:1060; ZMQ gateway ui_bridge_transport.py:353; in-process gateway ui_agent_bridge.py:2235; service ui_bridge_service.py:2209; capability capabilities.py:3565 | ui_agent_bridge.py:1883 |
| `close_window` | 7 | contract ui_bridge_service.py:779; abstract gateway ui_bridge_service.py:455; unavailable gateway ui_bridge_service.py:1067; ZMQ gateway ui_bridge_transport.py:365; in-process gateway ui_agent_bridge.py:2243; service ui_bridge_service.py:2223; capability capabilities.py:3594 | ui_agent_bridge.py:1906 |
| `snapshot_window` | 7 | contract ui_bridge_service.py:791; abstract gateway ui_bridge_service.py:463; unavailable gateway ui_bridge_service.py:1074; ZMQ gateway ui_bridge_transport.py:377; in-process gateway ui_agent_bridge.py:2251; service ui_bridge_service.py:2237; capability capabilities.py:3616 | ui_agent_bridge.py:1911 |
| `widget_tree` | 7 | contract ui_bridge_service.py:807; abstract gateway ui_bridge_service.py:471; unavailable gateway ui_bridge_service.py:1081; ZMQ gateway ui_bridge_transport.py:389; in-process gateway ui_agent_bridge.py:2259; service ui_bridge_service.py:2269; capability capabilities.py:3645 | ui_agent_bridge.py:1932 |
| `invoke_widget_action` | 7 | contract ui_bridge_service.py:819; abstract gateway ui_bridge_service.py:479; unavailable gateway ui_bridge_service.py:1088; ZMQ gateway ui_bridge_transport.py:401; in-process gateway ui_agent_bridge.py:2267; service ui_bridge_service.py:2283; capability capabilities.py:3676 | ui_agent_bridge.py:1942 |
| `validate_document` | 7 | contract ui_bridge_service.py:836; abstract gateway ui_bridge_service.py:487; unavailable gateway ui_bridge_service.py:1095; ZMQ gateway ui_bridge_transport.py:416; in-process gateway ui_agent_bridge.py:2275; service ui_bridge_service.py:2321; capability capabilities.py:3846 | ui_agent_bridge.py:1970 |
| `apply_document` | 7 | contract ui_bridge_service.py:853; abstract gateway ui_bridge_service.py:495; unavailable gateway ui_bridge_service.py:1102; ZMQ gateway ui_bridge_transport.py:431; in-process gateway ui_agent_bridge.py:2283; service ui_bridge_service.py:2340; capability capabilities.py:3866 | ui_agent_bridge.py:1980 |
| `list_snapshots` | 7 | contract ui_bridge_service.py:869; abstract gateway ui_bridge_service.py:503; unavailable gateway ui_bridge_service.py:1109; ZMQ gateway ui_bridge_transport.py:443; in-process gateway ui_agent_bridge.py:2291; service ui_bridge_service.py:2361; capability capabilities.py:3897 | ui_agent_bridge.py:2010 |
| `restore_snapshot` | 7 | contract ui_bridge_service.py:883; abstract gateway ui_bridge_service.py:511; unavailable gateway ui_bridge_service.py:1116; ZMQ gateway ui_bridge_transport.py:455; in-process gateway ui_agent_bridge.py:2299; service ui_bridge_service.py:2375; capability capabilities.py:3915 | ui_agent_bridge.py:2015 |
| `time_travel_head` | 7 | contract ui_bridge_service.py:897; abstract gateway ui_bridge_service.py:519; unavailable gateway ui_bridge_service.py:1123; ZMQ gateway ui_bridge_transport.py:467; in-process gateway ui_agent_bridge.py:2307; service ui_bridge_service.py:2402; capability capabilities.py:3938 | ui_agent_bridge.py:2037 |
| `list_branches` | 7 | contract ui_bridge_service.py:911; abstract gateway ui_bridge_service.py:527; unavailable gateway ui_bridge_service.py:1130; ZMQ gateway ui_bridge_transport.py:479; in-process gateway ui_agent_bridge.py:2315; service ui_bridge_service.py:2416; capability capabilities.py:3958 | ui_agent_bridge.py:2059 |
| `switch_branch` | 7 | contract ui_bridge_service.py:922; abstract gateway ui_bridge_service.py:534; unavailable gateway ui_bridge_service.py:1136; ZMQ gateway ui_bridge_transport.py:485; in-process gateway ui_agent_bridge.py:2319; service ui_bridge_service.py:2431; capability capabilities.py:3972 | ui_agent_bridge.py:2068 |
| `get_operation_status` | 7 | contract ui_bridge_service.py:934; abstract gateway ui_bridge_service.py:542; unavailable gateway ui_bridge_service.py:1143; ZMQ gateway ui_bridge_transport.py:497; in-process gateway ui_agent_bridge.py:2327; service ui_bridge_service.py:2442; capability capabilities.py:3994 | ui_agent_bridge.py:2087 |
| `selected_plate_workflow` | 7 | contract ui_bridge_service.py:950; abstract gateway ui_bridge_service.py:605; unavailable gateway ui_bridge_service.py:1150; ZMQ gateway ui_bridge_transport.py:326; in-process gateway ui_agent_bridge.py:2219; service ui_bridge_service.py:2178; capability capabilities.py:3501 | ui_agent_bridge.py:1847 |

Total: **181 restatements for 26 operations** (median 7), plus:

- **Failure answers restated per operation in the service:** 14 `_xxx_error` builders (`ui_bridge_service.py:2475-2713`) and 9 inline `error_result=lambda errors: …` closures, one per service method.
- **The result roster restated:** `UiBridgeOperationDispatchResult` (`pyqt_gui/services/ui_bridge_server.py:104-128`) unions the 23 result types the contracts already declare.
- **A behaviourless enum roster:** `UiBridgeFeature` (`ui_bridge_service.py:174-191`, 14 members) restates the operation groups; each contract re-lists its member (rule 1a).
- **Dispatch through lambdas:** every contract carries a `UiBridgeGatewayMethod` wrapper plus a `lambda gateway, connection, request: gateway.<name>(…)` (`ui_bridge_service.py:124-172`, 26 lambdas), so the contract's name is derived from a method it then forwards to.
- **A gateway subclass for one field:** `UiBridgeServerInProcessGateway.status` (`ui_bridge_server.py:205-228`) re-overrides the in-process status to add the server binding.
- **Three action providers restate one protocol:** `SessionOperationActionProvider` (`ui_bridge_session_actions.py:37`), `PipelineDebugToolbarActionProvider` (`ui_bridge_pipeline_editor.py:95`) and `ManagedWindowActionProvider` (`ui_bridge_windows.py:2817`) each write `catalog` as a map over `summary`, the stale-selection, stale-revision, availability and confirmation guards, and the accepted/rejected `UiActionInvokeResult` construction (three `_invoke_error`/`_result` copies).
- **U1 leftovers handed to U2:**
  - The datasets window title is still "Plate Manager" (`agent/ui_bridge_identities.py:101`, menu `pyqt_gui/main.py:723`) while the session view it renders is `DatasetListView`.
  - The bridge still advises polling every 500 ms: `UiActionInvokeResult.recommended_poll_interval_ms = 500` (`agent/dto/ui_bridge.py:1226`, set again at `ui_bridge_pipeline_editor.py:159`), although `Session` publishes push events (`Session.events_after`) that the bridge does not expose.
  - `UiBridgeBrowserPong.to_dict` (`ui_bridge_server.py:95-104`) hand-copies three fields (schema version, protocol version, instance id) that the status operation already returns.

## Target

```python
class UiBridgeOperation(ABC, metaclass=AutoRegisterMeta):     # registry key: wire name
    name: ClassVar[str | None]                                 # wire operations only
    request_type: ClassVar[type | None]; result_type: ClassVar[type]
    bridge_feature: ClassVar[str | None]                       # status tag, declared on group bases
    @classmethod
    def failed(cls, request, errors): ...                      # the operation's failure answer
    @classmethod
    def prepare(cls, service, request): ...                    # optional client-side check
    @classmethod
    def call(cls, service, connection, request): ...           # default: service.gateway.invoke
class UiBridgeGatewayABC:   def invoke(self, connection, operation, request): ...
class UiBridgeService:      def invoke(self, operation, request=None, connection=...): ...
class UiBridgeCapability(AgentCapabilityDeclaration):
    operation: ClassVar[type[UiBridgeOperation]]               # input, output, invocation derived
class UiActionProvider(ABC):                                   # catalog, guards, results once
    def action_ids(self); def describe(self, action_id); def dispatch(self, action, request)
```

- Every per-operation gateway and service method is deleted; the in-process bridge registers its implementation per operation (`@serves(Operation)`) and the in-process gateway calls `bridge.invoke(operation, request)`.
- Failure answers move onto the operations (shared by group bases where the result type is shared); the 14 service builders are deleted.
- `UiBridgeFeature`, `UiBridgeGatewayMethod*`, `UiBridgeOperationDispatchResult` and `UiBridgeServerInProcessGateway` are deleted; status features are derived from the registry.
- Operations composed on the client (`get_object_state_fields`, `wait_for_operation_receipt`) are operation classes without a wire name.
- A `session_events` operation reads the GUI session's event log with U1's `SessionEventsRequest`/`SessionEventBatch`; action results carry the session `event_sequence` instead of `recommended_poll_interval_ms`.
- `SessionView.title` owns the window title; `UiBridgeBrowserPong` is deleted.

## Guards

- No class deriving from `UiBridgeGatewayABC`, and not `UiBridgeService`, defines a method named after an operation; gateways define no public method but `invoke`.
- Every wire operation has exactly one in-process implementation, and every operation is reachable through `UiBridgeService.invoke` with no per-operation code.
- No `UiBridgeFeature`, `recommended_poll_interval_ms`, `UiBridgeGatewayMethod` or `UiBridgeBrowserPong` name under `openhcs/`.
- Every UI-bridge capability that names an `operation` takes its input and output contracts from it.

## Tests

- The guard file (`tests/unit/agent/test_ui_bridge_operation_family.py`): the AST guards plus one family test over the registry (decode, failure answer, ZMQ round trip through a fake client for every operation).
- The MCP contract fixture, regenerated only for the intended changes (operation-status input, session events tool, removed poll field).
- Existing gateway fakes and per-method service tests are rewritten against `invoke`.

## New-case experiments

- **A new bridge operation** (for example "list dock panes"): today a contract class with a gateway lambda, an abstract gateway method, three gateway implementations, a service method with its failure builder, a result-union member and a capability with forwarding lambda: eight edits in five files. After: one `UiBridgeOperation` subclass, one `@serves` implementation, and (if it is an MCP tool) one capability naming `operation`.

## Done when

The guards pass with zero exceptions; gateways and the service have one `invoke` each; capabilities derive from operations; the three action providers share one base; the MCP contract test, the touched agent, ui_bridge and pyqt_gui tests and the headless and GUI session journeys pass.
