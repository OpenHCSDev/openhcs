# G6: Domain-blind viewers

**Head audited:** `openhcs` `main` at `1c1059867` (#1172). **Rules:** [00-RULES.md](00-RULES.md). **Step 3.** Replaces C7.
**Architecture:** [04-ARCHITECTURE.md](04-ARCHITECTURE.md), "Viewers". *Builds:* `DeclaredAxis`, `ViewerSlotFamily` (napari and Fiji leaves), one `ViewerControlAction` family, one `ViewerFamily` class per viewer. *Uses:* G1's `Axis`/`AxisRole`, `AutoRegisterMeta`.

## What is wrong

**The viewer processes learn which axes exist from the producer's active axis family instead of from the payload, the placement vocabulary is a flat enum restated by two config enums, and each viewer restates the lifecycle control actions, the viewer identity and its forwarding (IDEN-1, MEMB-2, IMPL-2, IMPL-4).**

- **Exact-set rejection.** `AxisRoleModeDisplayConfig.role_modes_from_wire` (`core/config.py:281-306`) rebuilds the display config in the viewer process from `AxisFamily.active()` and raises unless the payload's `component_modes` names exactly the viewer process's family. Eight more `AxisFamily.active()` reads run in the viewer process: `viewer_component_system.py:107,127,384` (labels, ordinal normalisation), `napari_viewer_server.py:1024` (partition → LAYER), `:1306,2377` (fractional-Z stack), `napari_streaming_handlers.py:1426` (spatial labels). A payload streamed under any other family is rejected or mislabelled.
- **The wire carries no axis declarations.** `display_config` carries `component_modes` and `component_order` (names only); roles, labels and value kinds are re-derived on the receiving side.
- **Flat placement enum.** zmqruntime `ViewerComponentMode` (`viewer_protocol.py:285`) mixes napari (`stack`, `layer`) and Fiji (`window`, `channel`, `slice`, `frame`) slots; `NapariDimensionMode` and `FijiDimensionMode` (`config.py:309,447`) restate both subsets by hand, and every config default restates the Fiji role mapping (colour→CHANNEL, stack→SLICE, else FRAME, `config.py:491-534`). PolyStore's Fiji window grouping (`receivers/core/window_projection.py:24-165`) and napari route key (`receivers/napari/layer_key.py:51`) re-read the flat enum; only OpenHCS calls them.
- **Labels by role table.** `ViewerAxisLabelStrategy` and its four leaves (`viewer_component_system.py:97-160`) hardcode `Ch`/`Z`/`T` per role instead of reading a declared label.
- **Two control families restate the lifecycle.** `NapariControlMessageAction` (`napari_viewer_server.py:3036-3296`) and `FijiControlMessagePlan` (`fiji_viewer_server.py:1229-1495`) each declare shutdown, force-shutdown, clear-state, process-launch and settle; Fiji spells the first three as string literals. **Bug:** `FijiControlMessageAuthority.response_for` answers an unregistered message with SUCCESS (`fiji_viewer_server.py:1490`), so MCP navigate/viewport/measure requests to Fiji silently do nothing. Fiji carries three `FijiUnsupported*Plan` placeholders that restate the unknown-message error, and its pong advertises no control capabilities.
- **Identity and forwarding.** `ViewerType` (enum, `streaming_config_declarations.py:66`) points at `*ViewerDeclaration` leaves; `StreamingConfigBehaviorMixin` forwards six properties to it (`streaming_config_factory.py:185-209`), and `config_key`/`from_config_key` spell and reverse-search an f-string. `start_viewer`/`stop_viewer` are written twice (`napari_stream_visualizer.py:95-170`, `fiji_stream_visualizer.py:69-112`); `from_display_payload` is written twice (`config.py:412-435, 548-570`).
- **Import reach.** `agent/dto/viewer.py:44` imports `agent/dto/execution.py` for `ExecutionConnectionFields`; through `zmq_execution_client` that loads 203 openhcs modules, 16 of them `openhcs.microscopes`, plus `core.orchestrator`, into the napari server process.

## Target

```python
# openhcs/runtime/viewer_axes.py (imports only core.axes and the wire libraries)
@dataclass(frozen=True)
class DeclaredAxis:                       # on the wire inside display_config
    name: str; label: str; roles: tuple[type[AxisRole], ...]; value_kind: type[AxisValueKind]
    @classmethod
    def of(cls, axis: type[Axis]) -> DeclaredAxis: ...

class ViewerSlot(ABC):                    # one native placement slot
    wire_value: ClassVar[str]; roles: ClassVar[tuple[type[AxisRole], ...]] = ()
class ViewerSlotFamily(ABC):              # per viewer; leaves register by inheritance
    default_slot: ClassVar[type[ViewerSlot]]
    def slot_for(axis: DeclaredAxis) -> type[ViewerSlot]   # first slot owning one of its roles
    def named(wire_value) -> type[ViewerSlot]; def choice_enum(name) -> type[Enum]  # form boundary only
class NapariSlots(ViewerSlotFamily): Stack (default), Layer
class FijiSlots(ViewerSlotFamily):   Channel(ColourAxis), Slice(StackAxis), Frame(TimeAxis, default), Window
```

- The display-config wire section carries `declared_axes` (name, label, roles, value kind) beside `component_modes`/`component_order`. The viewer validates `component_modes` and `component_order` against the payload's own declared axes; it never reads `AxisFamily.active()`. Role queries (partition → separate layers, stack → fractional Z and spatial labels, labels, ordinal normalisation) read `DeclaredAxis`.
- `Axis.label` is declared on the axis (default `name.title()`); the microscopy family declares `Ch`, `Z`, `T`. `ViewerAxisLabelStrategy` and its leaves are deleted.
- Per-role mode fields stay (G1); their defaults come from the slot family, an axis with no matching field takes the family's slot for its roles, and `NapariDimensionMode`/`FijiDimensionMode` are views derived from the slot families (same member names, so saved configs load unchanged).
- The viewer process decodes viewer-side settings (`NapariDisplaySettings`, `FijiDisplaySettings`) once through one generic decoder; `from_display_payload` is deleted from `config.py`, and the viewer servers no longer import `openhcs.core.config`.
- zmqruntime: `ViewerComponentMode`, `ViewerComponentModeGroups`, `viewer_component_mode_value` and the mode-grouping helpers are deleted (lockstep PR, version bump). PolyStore: the Fiji window grouping and napari route key move to the OpenHCS viewer modules that call them (lockstep PR, version bump).
- **One control family** (`openhcs/runtime/viewer_control_actions.py`): `ViewerControlAction` keyed by the control message-type wire value, per-viewer registries (`NapariControlAction`, `FijiControlAction`), lifecycle mixins (shutdown, force-shutdown, clear-state, process-launch, settle) written once over a `ViewerServerPort`, one shared `UnknownControlAction` that answers ERROR, and pong capabilities derived from each registry for both viewers. The `FijiUnsupported*` plans are deleted (the shared ERROR answers them).
- **One `ViewerFamily` class per viewer** (`NapariViewer`, `FijiViewer`) owns backend, config key, title, visualizer, slot family and entrypoint; `ViewerType` becomes the boundary view derived from the registry; `ViewerDeclarationABC` and its two leaves are deleted; `StreamingConfigBehaviorMixin` reads the family directly. `start_viewer`/`stop_viewer` move into `ManagedViewerLifecycleMixin` once.
- `ExecutionConnectionFields` moves to `agent/dto/execution_connection.py`; `agent/dto/viewer.py` no longer imports `agent/dto/execution.py`.

## Guards

`tests/unit/test_g6_viewer_guards.py`:
1. Importing `openhcs.runtime.napari_viewer_server` and `openhcs.runtime.fiji_viewer_server` (fresh subprocess) loads no `openhcs.microscopes`, no `openhcs.core.orchestrator` and no `openhcs.core.config`.
2. No `AxisFamily` reference in the viewer modules (`runtime/*viewer*`, `napari_*`, `fiji_*`, `viewer_component_system`).
3. No `ViewerComponentMode` anywhere in `openhcs/` or the submodules' `src/`.
4. No `ControlMessagePlan`, `Unsupported*ControlPlan` or `NapariControlMessageAction` names; no `"shutdown"`/`"force_shutdown"`/`"clear_state"` literals in the Fiji server.
5. No `ViewerDeclarationABC`; `agent/dto/viewer.py` imports nothing from `agent.dto.execution`.

## Tests

- One family test over both viewers' control registries: lifecycle actions present, unknown message answers ERROR, capabilities derived from the registry.
- One new-case test: a non-microscopy family (`Scene` partition, `Band` colour, `Date` time, no stack) streams a display payload that a viewer decodes against its own declared axes, with Fiji slots C/T/FRAME and labels from declarations, while the process's active family is microscopy.
- Existing viewer tests that assert the exact-set rejection, `ViewerAxisLabelStrategy`, `ViewerComponentMode` members or the `FijiUnsupported*` plans are deleted or rewritten at the family level.

## New-case experiments

- *A new domain axis with no viewer role* (for example a `Replicate` with only `DefaultVariable`). Today: `mode_field_for_axis` raises and both viewers reject the payload unless the viewer process's family matches; three label leaves would need a fourth. After: zero edits; it takes each viewer's default slot and its declared label.
- *A new control message on Fiji.* Today: a plan class, plus the unknown path silently succeeds if forgotten. After: one leaf; forgetting it answers ERROR and the capability list omits it.
- *A third viewer.* Today: an enum member, a declaration leaf, a visualizer with its own start/stop, a config with hand-written mode fields and `from_display_payload`, a control family. After: one `ViewerFamily` leaf, one slot family, one settings dataclass and its control leaves.

## Done when

The guards pass; the exact-set rejection, `ViewerComponentMode`, `ViewerAxisLabelStrategy`, `FijiControlMessagePlan`, `NapariControlMessageAction`, `ViewerDeclarationABC` and the duplicated start/stop and `from_display_payload` are gone; Fiji answers unknown control messages with ERROR and advertises its registry; the viewer tests touched pass; no viewer process from the worktree remains.
