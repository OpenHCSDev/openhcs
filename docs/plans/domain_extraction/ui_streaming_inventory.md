# UI, application, MCP, and streaming inventory

Audit date: 2026-09-11. This is an evidence inventory and extraction plan,
not an authorization to edit production code. The inventory was made from the
production tree at `e867013a8eb188edcc63b5b0cdfd06f42a99b409`; the existing
dirty `paper/` work and other agents' documents were preserved. No live UI,
MCP, viewer, or ZMQ validation was run.

## Disposition

OpenHCS can be a specialization of a generic tensor/dataflow application, but
the alternate-family acceptance criterion has to be end-to-end. A change to
the component declaration cannot stop after `AllComponents`: it must update
the reflected form schema, source-binding choices, row previews, code
documents, ObjectState persistence, MCP schemas/requests, compilation, viewer
display payloads, and streaming validation in one declared process schema.

The strongest current leak is not the generic viewer transport. It is the
definition-time step shape: `AbstractStep` has separate
`napari_streaming_config` and `fiji_streaming_config` arguments and attributes
(`openhcs/core/steps/abstract.py:153-221`). The compiler and port scanner have
already moved in the right direction by iterating the registered
`StreamingConfig` types (`openhcs/core/pipeline/compiler.py:498-571`,
`openhcs/core/streaming_config_factory.py:181-208`). Step construction and
ObjectState field materialization must reach the same authority.

Napari and Fiji should be treated as reusable tensor/image client leaves.
Their display and process constraints are real client constraints, not a
reason to classify the clients as biology-only. OpenHCS can retain the
application-specific declarations, defaults, source adapters, function
catalog, and UI assembly around those leaves.

## Audit method, coverage, and exclusions

The inventory used current production source, the maintained architecture
front door (`docs/source/architecture/quick_start.rst`,
`nominal_ownership.rst`, and `abstraction_lattices.rst`), targeted `rg`/line
inspection, and the checked-out source of the relevant submodules. The
production scan covered:

* component and enum construction (`openhcs/components`,
  `openhcs/constants`);
* typed configuration, step construction, compiler streaming collection, and
  config persistence/document projection (`openhcs/core`);
* the PyQt runtime context, launcher, application shell, main window,
  window-factory registrations, forms, source-binding editor, image browser,
  preview/code providers, and ZMQ server browser (`openhcs/pyqt_gui`,
  `openhcs/gui_startup.py`);
* the function catalog lifecycle, agent context, config schema service, plate
  streaming request, MCP capability projection, and bootstrap (`openhcs/agent`,
  `openhcs/mcp`, `openhcs/runtime/function_catalog_preparation.py`);
* viewer component semantics, Napari/Fiji streaming leaves, viewer lifecycle,
  and ZMQ boundary code (`openhcs/runtime`); and
* the reusable checked-out foundations in `external/pyqt-reactive`,
  `external/PolyStore`, and `external/zmqruntime`.

Tests were excluded from the production inventory, per the assessment scope.
They remain required behavior gates below. NRA capability checks and the NRA
scan deadline are parent-owned. Broad microscope/source-format adapters,
pipeline presets, and biological function bodies are specialization leaves;
only their direct component consumers needed to identify the propagation
surface were included here. Archived architecture plans are context, not
current authority. No claim is made that a fresh process has loaded an
alternate schema, that an MCP client connected, or that a viewer accepted a
payload.

## Existing nominal foundations to preserve

| Responsibility | Current source evidence | Assessment |
| --- | --- | --- |
| Component membership/default constraint | `openhcs/components/framework.py:16-179` | `ComponentConfiguration[T]` already accepts any enum, validates membership and `group_by`/variable incompatibility, and derives remaining choices. Preserve it; move only the OpenHCS template binding at `:181-208` out of the generic owner. |
| Process-local component projections | `openhcs/constants/constants.py:101-221` | `AllComponents`, `VariableComponents`, `GroupBy`, `SequentialComponents`, and `StreamingComponents` are generated from the configured declaration. The cache, module identity, `__module__`/`__qualname__`, and pickle behavior are boundary semantics. |
| Viewer config registry | `openhcs/core/config.py:1014-1124` | `StreamingConfig` is an ABC with `AutoRegisterMeta`; config keys and supported viewers are derived from the registry. This is the right discovery authority, not a second viewer list. |
| Viewer leaf declarations | `openhcs/core/streaming_config_declarations.py:18-154` | `ViewerDeclarationABC` owns backend and visualizer construction, while `ViewerType` owns wire/config/output/title projections. It is a useful nominal seed, although the closed two-member enum and its consumers need to be treated as an application/client declaration boundary. |
| Shared streaming behavior | `openhcs/core/streaming_config_factory.py:89-179` | `StreamingConfigBehaviorMixin` has meaningful shared transport/runtime/surface behavior. Keep this MI; do not add a redundant generic wrapper around each viewer config. |
| Typed viewer display contract | `external/PolyStore/src/polystore/streaming/viewer_transport.py:37-84` | `ViewerDisplayConfigABC` and filename/metadata handler ABCs provide the reusable display/metadata boundary. |
| Viewer wire vocabulary and incompatibility groups | `external/zmqruntime/src/zmqruntime/viewer_protocol.py:49-176` | `ViewerWireField`, `ViewerComponentMode`, and `ViewerComponentModeGroups.require_all_supported` are generic wire/validation foundations. Unsupported operations should fail here or in a leaf-owned validator, not through consumer string branches. |
| Viewer process/lifecycle substrate | `external/zmqruntime/src/zmqruntime/streaming/server.py:29-85`, `streaming/process_manager.py:9-48`, `viewer_state.py:1-207` | The server, process manager, and centralized `(viewer_type, port)` state manager already form the reusable transport/lifecycle boundary. `viewer_type` is a wire identity at this layer; resolve semantic behavior through a declaration before using it. |
| UI provider contracts | `external/pyqt-reactive/src/pyqt_reactive/protocols/component_selection.py:8-100`; `protocols/form_config.py:10-57`; `protocols/preview_formatter.py:11-91` | Existing ABC/provider seams let a host supply components, functions, forms, and previews. Do not make pyqt-reactive import OpenHCS or introduce `Protocol` classes. Preview lookup already follows canonical declaration MRO (`preview_formatter.py:54-61`). |
| Generic window and server-browser infrastructure | `external/pyqt-reactive/src/pyqt_reactive/services/scope_window_factory.py:31-198`; `widgets/shared/zmq_server_browser_widget.py:87-240` | These are reusable composition points. Scope routes are currently first-match by registration (`:102-161`); audit every overlap/order dependency. If order is encoding nominal specificity, derive that choice from the existing nominal/MRO owner rather than blessing registration order as semantic authority. |
| Function catalog authority/lifecycle | `openhcs/agent/services/function_catalog_service.py:471-530`, `:608-630`; `openhcs/runtime/function_catalog_preparation.py:21-130` | The ABC catalog and bounded preparation operation are close to a reusable catalog service. The OpenHCS registry and thread labels are host-specific injections, not reasons for a second catalog registry. |
| MCP binding projection | `openhcs/mcp/server.py:512-1850`, `:2131-2167`, `:2368-2460` | ABC + `AutoRegisterMeta` binding types and generated capability declarations are already a projection over capability owners. Keep `AgentCapabilityDeclaration` as authority; do not hand-author a parallel MCP schema. |
| ObjectState/code persistence | `openhcs/pyqt_gui/config.py:351-494`; `openhcs/pyqt_gui/windows/config_window.py:96-137`, `:634-754` | UI config, editing, snapshots, transaction/rollback, and cache/document projection are existing persistence boundaries. Alternate schemas must pass through these objects rather than a new sidecar format. |

The orthogonal MI in `ViewerDisplayBatchContext` (axis semantics plus name
metadata, `openhcs/runtime/viewer_component_system.py:888-896`) is meaningful
and should remain compositional. MRO is appropriate for selecting the nearest
nominal formatter/provider; it is not a replacement for the declaration's
explicit component order, which is data-axis order.

## `AllComponents` change-propagation inventory

### Authority and derived enums

`ComponentConfiguration` is generic in shape, but
`create_openhcs_default_configuration()` still creates a five-member
`_ComponentTemplate` and fixes `WELL` as the multiprocessing axis,
`SITE` as default variable, and `CHANNEL` as default grouping
(`openhcs/components/framework.py:181-208`). The dynamic enum builder then
materializes all process-local enum classes from that configuration
(`openhcs/constants/constants.py:131-221`). A generic extraction must preserve
one declaration-owned source for membership, order, wire values, execution
axis, and defaults. It must not make `AllComponents`, a UI options list, a
viewer label map, and an MCP list into four authorities.

The enum builder's cache and pickle metadata mean the alternate family should
be selected before dependent modules are imported, with the same declaration
available to spawned workers and server processes. This audit does not assume
live in-process schema replacement or hot-swapping an already-created enum.

### Concrete and membership-dependent consumers

| Projection | Evidence | Current coupling and extraction requirement |
| --- | --- | --- |
| Viewer display forms and wire rehydration | `openhcs/core/config.py:254-379` and `:411-544` | `NapariDisplayConfig` and `FijiDisplayConfig` each carry `COMPONENT_ORDER = AllComponents.ordered_names()`, then list and map `site_mode`, `channel_mode`, `z_index_mode`, `timepoint_mode`, and `well_mode` individually. Their exact-key checks and `from_display_payload` constructors repeat the five-member schema. Generate the membership-dependent mode field projection from the component declaration while retaining Napari/Fiji-specific mode enums and extra fields. A new generic config wrapper that only renames these classes would be a mirror; use declarative leaves plus one shared projection instead. |
| Viewer labels/roles | `openhcs/runtime/viewer_component_system.py:676-692`, `:822-847` | Abbreviation and formatter dictionaries enumerate the five members; role resolution converts wire strings back through `AllComponents` and treats default group-by as color. Move label/role semantics to the component declaration or an explicit base-declared presentation contract. An unknown axis must be rejected or explicitly declared; do not guess a label/role in a generic fallback. Keep metadata storage and normalization generic. |
| Napari variable-size routing | `openhcs/runtime/napari_viewer_server.py:836-862` | `NapariSeparateLayersDisplayStrategy` requires `AllComponents.WELL` and forces it into `LAYER`. This is a client policy tied to a current OpenHCS axis, not generic tensor behavior. Declare a host-provided sample/route axis or explicit leaf policy; if no compatible axis/data type exists, fail with a typed incompatibility. |
| Source-binding editor choices | `openhcs/pyqt_gui/widgets/source_bindings_editor.py:350-367`, `:600-620`, `:1640-1658` | Choices and selector parsing iterate/construct `AllComponents`. The iteration is already dynamic, but the editor is directly coupled to the OpenHCS enum. Supply the declared component-key/value codec through the host provider so the same family drives the form and parser. |
| Image-browser plate synchronization | `openhcs/pyqt_gui/widgets/image_browser.py:55-60`, `:139-167`, `:1446-1476` | Streaming viewer fields and config types are correctly registry-derived, but the plate-view synchronization assumes `AllComponents.WELL`. Keep a well/plate adapter in OpenHCS; a generic image browser needs a declared selection-axis role or no such control. |
| Axis projection strategies | `openhcs/core/steps/function_io.py:178-184`, `:275-303`; `openhcs/core/source_metadata.py:445-476`, `:533-610` | Strategy registration is a useful enum-keyed nominal pattern, but current leaves carry fixed `TIMEPOINT`, `SITE`, `CHANNEL`, `Z_INDEX`, and `WELL` semantics. The extracted platform can retain the strategy ABC and MRO/registry lookup while moving physical/source interpretation into a family/source declaration. |
| Source identity/naming | `openhcs/core/source_projection.py:55-96`, `:188-192` | The OpenHCS address and filename identity use the five named coordinates. This is a downstream compatibility boundary, not a UI-only issue. Alternate family acceptance requires a generic keyed component map and an explicitly versioned OpenHCS legacy naming codec. |
| Other core consumers | `openhcs/core/source_binding_workspace.py:526-531`, `:1144-1211`; `openhcs/core/source_bindings.py:1132-1238`; `openhcs/core/orchestrator/analysis_consolidation.py:272-281`; `openhcs/core/source_image_provenance.py:1242-1425` | These are part of the propagation set even when not UI extraction targets. They must either consume the component declaration generically or remain clearly owned OpenHCS source/plate leaves. |
| Demos/presets | `openhcs/mcp/installed_demo.py:253-345`; `openhcs/demo/basic_pipeline.py:12`, `:82-83` | Explicit Napari/five-axis examples are product demos, not generic authorities. They need alternate-family compatibility coverage or an explicit OpenHCS-only exclusion after the declaration boundary is stable. |

The acceptance test is a fresh process with a differently sized, differently
ordered family whose values use neutral tensor/dataflow names (no microscopy
names and none of the existing five names). It must produce
the same coherent key set in UI schema/form/preview/code/persistence/MCP and
viewer payloads without editing each consumer. A family with a missing
sample/route axis must exercise the explicit unsupported-operation path rather
than receive a silent `Well` substitution.

## Streaming client/config inventory

### Already derived correctly

`StreamingConfig.supported_config_keys()`, `supported_viewer_types()`, and
`config_type_for_key()` derive ObjectState fields from the registered
`StreamingConfig`/`ViewerType` declarations (`openhcs/core/config.py:1092-1124`).
The compiler walks `StreamingConfig.__registry__` and discovers each config in
the snapshot (`openhcs/core/pipeline/compiler.py:498-571`). Port discovery does
the same (`openhcs/core/streaming_config_factory.py:181-208`). The image
browser builds its viewer fields and dataclass fields from those methods
(`openhcs/pyqt_gui/widgets/image_browser.py:139-170`), and the debug inspector
uses `StreamingConfig.supported_viewer_types()` (`openhcs/pyqt_gui/windows/debug_inspector_window.py:56-76`).
The MCP config schema similarly derives registered config keys/types
(`openhcs/agent/services/config_service.py:988-1020`). These are strong
examples to preserve.

### Repeated concrete knowledge to remove or contain

* `NapariStreamingConfig` and `FijiStreamingConfig` are concrete leaves at
  `openhcs/core/config.py:1130-1157`, and `ViewerType` is a closed two-member
  identity/config-key enum at `openhcs/core/streaming_config_declarations.py:70-154`.
  The leaf declarations are appropriate; the consumers must not grow a
  second `if napari / elif fiji` table when a third client is added.
* `AbstractStep` is the contrary case: its signature, docstring, and instance
  attributes name both concrete configs (`openhcs/core/steps/abstract.py:165-221`).
  Refactor step definition/config reflection so registered streaming leaves
  are materialized through their declaration-owned config fields. Verify the
  ObjectState/lazy dataclass machinery before choosing a field factory; do not
  hide the problem in a generic dictionary that loses field paths, type
  annotations, or provenance.
* `PlateFileStreamRequest` defaults to `ViewerType.NAPARI.config_key` and the
  CLI help gives `napari_streaming_config` as its example
  (`openhcs/agent/dto/plate.py:375-428`,
  `openhcs/mcp/dev_client_commands/plate.py:495-520`). This is an OpenHCS
  product default, but the generic request should obtain a declared default
  client and validate the requested key before constructing a leaf. The
  service currently resolves a key through `StreamingConfig` and instantiates
  it (`openhcs/agent/services/plate_streaming_service.py:286-293`); add
  owner-defined operation/data compatibility validation at this boundary,
  rather than consumer-side string dispatch.
* User-facing viewer-set text is repeated in
  `openhcs/pyqt_gui/windows/managed_windows.py:218` and in capability
  descriptions such as `openhcs/agent/capabilities.py:2688-2694` and
  `:2814-2825`. Titles/help can be host projections of registered declarations;
  they should not be a second capability list or assume Napari/Fiji are the
  only clients.

### Viewer boundary and client constraints

The reusable boundary is already split sensibly: PolyStore owns the typed
display-config contract; ZMQRuntime owns wire normalization, component modes,
shared-memory/server/process machinery, and viewer lifecycle; OpenHCS owns
Napari/Fiji display classes, stream handlers, visualizer process managers, and
server leaves. The OpenHCS runtime imports the generic contracts rather than
the reverse (`openhcs/runtime/viewer_component_system.py:12-28`,
`openhcs/runtime/napari_viewer_server.py:25-57`). Keep that direction.

Napari's `NapariVariableSizeHandling` and Fiji's `FijiDimensionMode` express
legitimate client-specific choices. Their validator must state which component
modes/data types/shapes the client accepts. `ViewerComponentModeGroups` already
has a fail-loud unsupported-mode projection; extend this owner-level pattern
for rank/shape/control limitations. A consumer may resolve a wire identity at
the boundary, but semantic selection must call the typed declaration/registry,
not compare strings in every service.

## PyQt application, forms, and startup

### Generic seams already available

`pyqt-reactive` supplies ABC provider contracts for component/function
selection, form-generation configuration, code generation, logs/server scans,
preview formatting, a scope-window factory, and a generic ZMQ browser. The
OpenHCS adapter registers these at startup in
`openhcs/pyqt_gui/services/reactor_providers.py:293-332`:

* `OpenHCSComponentSelectionProvider` obtains `GroupBy` and component keys from
  the OpenHCS orchestrator (`:195-268`);
* `OpenHCSFunctionSelectionProvider` uses the injected catalog (`:271-290`);
* `OpenHCSCodegenProvider`, log discovery, server scanning, and the WellFilter
  preview formatter remain host-specific (`:48-192`, `:326-332`).

This is the intended dependency direction. Extract reusable window, manager,
form, and server-browser mechanics to pyqt-reactive or a tensor-application
layer, then leave only OpenHCS domain behaviors and assembly choices in the
adapter. Do not move OpenHCS config or catalog imports into pyqt-reactive.
`FormGenConfig` is a configuration seam, not a second schema authority.

`MainWindowSpecDefinition` is a reusable declaration-shaped record
(`openhcs/pyqt_gui/services/main_window_workflows.py:299-317`), but
`build_main_window_specs()` imports and enumerates the OpenHCS concrete window
set (`:320-367`). `OpenHCSUiWindowId` is likewise a closed application identity
set (`openhcs/pyqt_gui/services/ui_window_ids.py:23-66`). Preserve these as
the current OpenHCS composition, while extracting reusable mechanics from the
window classes. A generic shell should receive existing nominal window/action
declarations and irreducible application choices; do not create a second
manifest that copies PlateManager, PipelineEditor, ImageBrowser, or other
window semantics.

`OpenHCSWindowCreationAuthority` deliberately owns OpenHCS scope-to-window
semantics and exact `GlobalPipelineConfig`/`UIConfig` tabs and persistence
(`openhcs/pyqt_gui/services/window_handlers.py:48-138`, `:149-203`). The
generic `ScopeWindowRegistry` should remain a route/factory mechanism while
shared route/window mechanics are extracted. Its routes are currently matched
first by registration; audit each overlap. If registration order encodes
nominal specificity, derive that selection from the existing MRO/nominal owner
instead of treating registration order as a second semantic authority. Do not
make the generic factory know OpenHCS config classes.

### Application and configuration construction

`UIConfig` and `PyQtGuiRuntimeContext` are typed process-level policies
(`openhcs/pyqt_gui/config.py:351-419`). Cache load/save and direct endpoint
projection already use typed `ConfigCache`/`ConfigDocumentAuthority`
(`:439-494`). `OpenHCSPyQtApp.setup_application()` registers the global/UI
ObjectState roots, sets the global configuration context, and installs the
OpenHCS provider set (`openhcs/pyqt_gui/app.py:178-247`). These are valuable
life-cycle boundaries, but the application name, config root types, storage,
catalog service, and icon are OpenHCS assembly concerns.

The launcher still has a concrete host and a configuration construction gap:
`parse_arguments()` advertises a custom config path, while
`load_configuration()` logs it and returns `GlobalPipelineConfig()` instead of
reading that file (`openhcs/pyqt_gui/launch.py:132-216`). A generic launcher
should consume the existing typed document/cache loading authority through
the application binding; the OpenHCS specialization should define
compatibility and failure policy. This
audit does not propose silently implementing the currently incomplete path.

`gui_startup.py` already has useful ABCs and a nominal startup event owner
(`:33-126`) and a first-paint readiness boundary (`:129-260`). The child UI and
main entry point are OpenHCS-branded and invoke `python -m openhcs.gui_startup`
with OpenHCS-specific text/environment keys (`:459-725`). Extract the
progress-controller/event protocol only if another host needs it; inject
application identity, labels, child entry point, icon, and config loader. Do
not put OpenHCS branding in a generic startup package.

The main window's server scan is already streaming-registry based
(`openhcs/pyqt_gui/main.py:580-597`). Its menus and concrete actions are not:
`setup_menu_bar()` enumerates OpenHCS products and analysis actions
(`openhcs/pyqt_gui/main.py:670-838`). A generic shell should consume declared
actions/windows and let OpenHCS contribute this menu.

## MCP and function-catalog boundary

`FunctionCatalogServiceABC` is a good catalog authority: search, catalog,
detail, and function-reference methods are typed (`openhcs/agent/services/function_catalog_service.py:471-530`).
`FunctionCatalogPreparation` owns one cancellable, status-projecting
preparation operation (`openhcs/runtime/function_catalog_preparation.py:21-130`).
The reusable form is lifecycle + injected catalog; OpenHCS's
`RegistryService.prepare_in_current_process()` and processing registry remain
the specialization. The GUI constructs `ZMQFunctionCatalogService`, while the
MCP context lazily supplies either endpoint or hosted catalog services
(`openhcs/pyqt_gui/app.py:145-152`; `openhcs/mcp/context.py:37-100`, `:268-283`).

MCP config schemas already derive registered streaming config keys and type
representations from `StreamingConfig` (`openhcs/agent/services/config_service.py:988-1020`).
Generated MCP bindings iterate their ABC registries and generated capability
declarations (`openhcs/mcp/server.py:2368-2460`). These must continue to see
an alternate component/viewer family through the same declaration owner.
Config-field help, mutation, and code-document operations should remain
reflection/ObjectState projections, not copied lists.

The fail-soft bootstrap is structurally reusable: typed failure phase/payload,
health tool, and stdio reservation are in `openhcs/mcp/bootstrap.py:36-187`.
The server name, failure hint, tool names, capability-profile choices, and
OpenHCS imports are host-specific (`:18-33`, `:123-165`, `:190-223`). Factor a
generic bootstrap only around injected server identity, instructions,
capability surface, and build/run callbacks. Do not make a generic bootstrap
know the OpenHCS function catalog or viewer set.

## Proposed owner boundaries and dependency direction

### Component-family declaration owner

Extend the existing `ComponentConfiguration` authority and its declaration
binding (extracting its module only if the same owner remains authoritative); do
not create a parallel component metadata owner. It should answer, in
declaration order:

* component identity and stable wire value;
* execution/multiprocessing role and variable/grouping defaults;
* value-domain/selection behavior;
* display label/abbreviation/role where the role is genuinely component
  semantics; and
* compatibility/version information for persisted and wire projections.

`AllComponents` and the derived enum views may remain compatibility projections
for existing APIs, but UI, source, compiler, viewer, code, and MCP consumers
must query this owner. MRO may choose the most-derived registered strategy or
formatter; explicit declaration order controls tensor axes. An OpenHCS
declaration supplies its current defaults and legacy source/name codecs.

### Viewer-client declaration owner

Extend the existing `ViewerDeclarationABC`/`ViewerType`/`StreamingConfig`
relationship so one registered leaf owns its wire identity, config type,
display-config projection, backend, visualizer, title/output/config keys,
supported data types/modes, and incompatibility validation. Derive the config
field/schema/image-browser chooser/compiler/port/MCP projections from that
registry. Keep Napari/Fiji as reusable leaves with explicit client constraints;
their OpenHCS defaults and optional runtime integrations remain adapter-owned.

Do not introduce a generic `ViewerConfigWrapper` that simply forwards to
Napari/Fiji. The current transport behavior MI is meaningful; the display
semantics and client mode enums are distinct leaf responsibilities.

### Generic UI/application host boundary

Keep pyqt-reactive's ABC contracts, reflection form service, ObjectState-backed
editor machinery, window factory, and ZMQ browser below the application layer.
Introduce an application assembly seam only where needed to inject irreducible
config roots/loaders, application identity, startup presentation, providers,
icons/branding, and service construction. Derive window/action specs and
provider surfaces from their existing nominal declarations rather than copying
them into a parallel manifest. OpenHCS owns the current config tabs,
source-binding provider, function catalog adapter, log policy, and product
menus, while reusable main-window mechanics move below that assembly. Use
meaningful MI for orthogonal shared hooks where it improves the contract or
MRO; do not add empty marker mixins.

### MCP/catalog host boundary

Keep capability declarations and their generated binding projection as the
MCP authority. A generic capability server/bootstrap can consume an injected
catalog/context/profile and application identity; OpenHCS supplies its
functions, config service, UI bridge, plate service, and viewer controls. A
viewer/config schema must be declared once and projected to both GUI and MCP.

### Transport boundary

The intended direction is:

```text
ObjectState / metaclass-registry / pycodify / ArrayBridge
        + PolyStore viewer contracts + ZMQRuntime wire/lifecycle
        + pyqt-reactive UI contracts
                         |
                         v
        tensor/dataflow component + viewer declarations
        and generic config/compiler/catalog projections
                         |
                         v
        reusable tensor-domain viewer clients
        (Napari/Fiji adapters and any future clients)
                         |
                         v
        OpenHCS application adapters and assembly
        (defaults, source codecs, function catalog, UI, MCP,
         selection/configuration of viewer clients, OpenHCS ZMQ topology)
```

The lower layers must not import OpenHCS. Existing `OpenHCSZMQConfig` is an
appropriate host extension of `zmqruntime.ZMQConfig`
(`openhcs/runtime/zmq_config.py:17-110`). Existing OpenHCS viewer/runtime
modules may depend on ZMQRuntime and PolyStore, not the reverse.

## Projection targets for NRA-assisted refactoring

These describe desired runtime factoring outcomes, not operations already
implemented by NRA. The companion `nra_leverage.md` records which concrete DSL
operations and simulations were verified. The declarations below must retain
their current owners rather than become a parallel metadata language:

1. **Component family projection.** One declaration record can generate the
   process-local enum compatibility views, component selector options, source
   identity keys, axis labels/roles, viewer `component_order`, mode-field
   schema, MCP field schema, and exact-key wire validation. The record remains
   owned by the component declaration; generated Python/code documents are
   projections, not authority.
2. **Viewer leaf projection.** One registered viewer declaration can generate
   the ObjectState config key/type lookup, display-name/title/output keys,
   image-browser chooser, compiler/port-scan discovery, MCP request/schema
   metadata, managed lifecycle identity, and capability validation entry point.
   Client-specific fields/mode constraints stay in the leaf declaration.
3. **Application assembly projection.** Existing window/action, configuration,
   and provider declarations should drive their generic installation machinery.
   The host supplies only irreducible product choices such as branding and
   selected roots. Do not add a manifest that copies the already-declared
   window/config/provider set or move domain semantics into pyqt-reactive.
4. **Catalog projections.** The existing callable registry/catalog and
   pycodify codegen path are already a DSL-like projection. Extend declaration
   metadata only where a schema/help field is genuinely owned by the callable;
   do not add a catalog copy for UI or MCP.

Prioritize (1) and (2) only after a minimal alternate-family process proves
that all projections agree. Generated dataclass fields must preserve
annotations, lazy resolution, field paths, ObjectState provenance, and code
round trips; a dynamic dictionary is not an equivalent replacement.

## Recommended factoring sequence

1. Write the alternate component/viewer declaration fixture in a fresh process
   and trace schema, form, preview, code, persistence, compiler, MCP, and
   streaming payloads. Record each first failing boundary.
2. Move OpenHCS defaults out of the generic component configuration owner and
   make every membership-dependent projection consume the owner. Preserve
   enum identity/pickle and versioned legacy wire/code input behavior.
3. Replace the concrete Napari/Fiji fields in `AbstractStep` with declaration-
   owned materialization that remains visible to ObjectState, lazy config
   resolution, code generation, and compiler snapshots. Then remove the
   duplicated five-axis maps from display configs in favor of a shared
   declaration projection while retaining client-specific fields and modes.
4. Replace viewer labels, role selection, plate/well assumptions, and fixed
   server-manager viewer text with owner-provided labels/roles/policies or
   OpenHCS-only adapters. Unsupported client operations must fail explicitly.
5. Extract only the application-shell/startup/bootstrap seams needed by a
   second host. Keep OpenHCS windows, actions, config tabs, source providers,
   catalog, and capability profile in OpenHCS assembly.
6. Run the live gates below, then use NRA for the separately owned capability
   and extraction checks. Do not call a lexical cleanup complete until an
   alternate declaration has traversed the real boundaries.

## Validation gates to run later

The following are required gates, not results of this audit.

### Declaration and process identity

* In a fresh interpreter, load an alternate family with no existing five-axis
  names, changed cardinality, changed declaration order, and changed execution
  axis. Assert the generated component views, defaults, labels, and wire values
  agree.
* Spawn a worker/server using the same declaration and verify enum identity,
  pickling, and schema-version diagnostics. Exercise missing/unsupported roles
  rather than adding compatibility aliases in consumers.

### UI schema, forms, previews, code, persistence

* Offscreen Qt startup through the repository `.venv` discovers the alternate
  component and viewer fields in config forms, source-binding selector choices,
  image-browser controls, and debug/viewer actions.
* Render and apply the same config through ObjectState, reset/inheritance,
  preview formatting, code-document generation/normalization, and reload from
  the cache/document. Verify field paths and revision/provenance remain
  authoritative; do not claim success from a stale in-process object.
* Verify alternate-family row previews use a base-declared/default formatter
  behavior (or fail because a required formatter is absent) and do not require
  a `WellFilterConfig`/`well` field.

### Catalog and MCP

* Start the catalog preparation operation and confirm the function catalog
  remains derived from the callable registry and can be consumed by the
  generic function-selection provider.
* In a fresh MCP stdio process, inspect generated config schema, registered
  viewer/config choices, field help, code-document endpoints, and explicit
  unsupported viewer/component operations. Verify fail-soft bootstrap payloads
  retain the configured application identity and phase.

### Streaming and viewer/ZMQ boundaries

* For each registered viewer leaf, send a payload containing the alternate
  component order, values, metadata labels, and mode map through the actual
  PolyStore/ZMQRuntime boundary. Check exact-key validation, normalization,
  shared-memory cleanup, acknowledgements, and lifecycle state.
* Exercise a supported and an incompatible data type/mode/rank/shape for
  Napari and Fiji. The result must be an owner-defined structured error, not a
  consumer-side string branch or silent axis substitution.
* Fresh-process GUI server discovery must enumerate ports from the streaming
  registry, and changing the registered viewer set must update the image
  browser, compiler, MCP schema, managed lifecycle, and ZMQ scan together.

### Real UI handoff

Use the supported UI bridge/MCP path in a fresh process to inspect the live
overview, ObjectState scopes/fields, forms, code documents, viewer chooser,
window state, and viewer payload/state. Capture a small alternate-family
fixture with unequal axis cardinalities and verify visible labels and selected
routes. This is the live validation gate; unit-only or static results are not
equivalent. No such interaction was performed in this audit.

## Non-goals and risks

* No production code, tests, submodule code, or other agent document was
  changed by this inventory.
* No attempt was made to make one interpreter host unrelated component schemas
  simultaneously. Startup-time declaration selection and fresh-process
  restart/session boundaries are sufficient for this extraction phase.
* Removing fixed component names does not prove arbitrary ndarray rank/shape
  support. Callable/artifact data capabilities and viewer client constraints
  remain separate declarations.
* A generated schema is acceptable only as a projection of a typed owner. Do
  not retain generated output as a hand-edited registry or add consumer-side
  string dispatch.
* Avoid numeric ordering abstractions: MRO is for nominal specificity; tensor
  axis order is an explicit declaration. Avoid redundant wrappers/classes when
  existing ABCs, registries, composition, and meaningful MI already answer
  the semantic question.
