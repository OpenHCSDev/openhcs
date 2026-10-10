# Target architecture: a domain-blind kernel

**Head audited:** `openhcs` `main` at `ddf27f31c`. **Rules:** [00-RULES.md](00-RULES.md). Six read-only audits produced the evidence (axes and compiler; payloads and sources; viewers and runtime; processing semantics; authoring surfaces; delegation to the first-party libraries). Every file:line below was verified in code.

## The thesis

OpenHCS is a tensor dataflow compiler and runtime. Arbitrary functions over n-dimensional data compile into a parallel, process-isolated plan. Graphical forms, Python and MCP author the same plan, and outputs stream to viewers. Microscopy is one domain that instantiates it. The kernel names no domain member. A domain plugs in by declarations only.

This is the correct-maintenance standard applied one level up. When the kernel names `WELL`, `CHANNEL`, `Z_INDEX`, `"plate"` or a CellProfiler concept, it supplies an answer the domain should declare: a required relation restated outside the mechanism that would derive it. **Every hardcoded member reference is slop, and every one is derived from the declared axis family.**

## What is already generic

- The compiler works in `axis_id`: `AxisCompilationRequest` (`core/pipeline/compiler.py:150`), `ProcessingContext.require_axis_id`, `CompiledExecutionBundle.axis_ids`. It covers per-axis compilation, `CompiledStepPlan`, the artifact graph, memory and device checks, sequential combinations and lanes.
- `RuntimePlaneAxis` and its strategy family (`core/runtime_plane_projection.py:46-140`). Runtime stores are keyed by `axis_id` (`runtime_stores.py:668`). The slice projection, alignment, array and tabular payload families. The `ComponentSelector`/`MetadataSelector`/`SourceSelector` selectors.
- PURE_2D/PURE_3D already mean "per slice of the declared stack axis" and "the whole stack" (`funcstep_contract_validator.py:1202`).
- The `ArtifactType` family (`artifacts.py:97`), object labels, relationships and measurements. These have zero axis-member references.
- Declaration-driven authoring: MCP tools from `AgentCapabilityDeclaration`, config windows from dataclasses over ObjectState, step forms from signatures, component pickers injected into pyqt-reactive.
- Viewer render paths: `ViewerComponentLayout` and the Fiji C/Z/T mapping by declared mode. `fiji_viewer_server.py` has no `AllComponents` reference.
- `component_group_scope` and the execution server ask for the parallel axis by role (`is_multiprocessing_axis()`, `MULTIPROCESSING_AXIS`).

## The root defect: axes cannot be declared

1. **The component family is hardcoded.** `components/framework.py:195-209` (`_ComponentTemplate`) fixes well, site, channel, z_index and timepoint. `get_openhcs_config` (`constants/constants.py:66`) always returns it. A domain has nowhere to declare its own family.
2. **The mechanism manufactures identity slop.** `get_openhcs_config()` builds a new Enum class on every call. Verified: two calls give different classes, and `config.multiprocessing_axis == AllComponents.WELL` is `False`; only `.value` is equal. So identity falls back to `.value` strings (`constants.py:114,121`; about 12 conversion sites such as `path_planner.py:244`). It runs on every step validation (`funcstep_contract_validator.py:715,823`; `compilation_session.py:331`).
3. **Five enums restate two sets.** `VariableComponents`, `SequentialComponents` and `GroupBy`-minus-`NONE` are identical, and `StreamingComponents` equals `AllComponents` (`constants.py:156-217`).
4. **Import-time binding:**
   - class bodies name members (`core/steps/function_io.py:201-229`, `source_metadata.py:1231`, `virtual_workspace_metadata.py:358`);
   - dataclass annotations bind one family (`config.py:702,760`);
   - per-member config fields (`config.py:285-327`, `439-541`).

   A second domain fails at import, before any logic runs.

## The axis family (foundation; surface G1)

Each relation is encoded once:

| Relation | Encoding |
|---|---|
| Identity | each axis is a nominal class |
| Membership | an axis belongs to a role through a capability mixin; the family registers its axes by inheritance |
| Implementation | behaviour lives on the role (NGFF descriptor, viewer slot, ordering, value kind) |

```python
class AxisRole(ABC):
    cardinality: ClassVar[Cardinality] = Cardinality.MANY
class PartitionAxis(AxisRole):  cardinality = Cardinality.ONE        # parallel, filtered, lane ownership, reduction key
class StackAxis(AxisRole):      ngff = NgffAxis("z", "space")        # ordered planes; "plane" = slice along it
class ColourAxis(AxisRole):     ngff = NgffAxis("c", "channel")
class TileAxis(AxisRole):       ngff = NgffAxis("field", "field")
class TimeAxis(AxisRole):       ngff = NgffAxis("t", "time")
class DefaultVariable(AxisRole): ...
class DefaultGroupBy(AxisRole): cardinality = Cardinality.AT_MOST_ONE
class LabelValued(AxisValueKind): ...;  class OrdinalValued(AxisValueKind): ...

class Axis(metaclass=AutoRegisterMeta):            # members of a family
    name: ClassVar[str]
class AxisFamily(metaclass=AutoRegisterMeta):      # the domain entry point
    @classmethod
    def with_role(cls, role: type[AxisRole]) -> tuple[type[Axis], ...]: ...   # validates cardinality

# microscopy domain package
class Microscopy(AxisFamily):
    class Well(Axis, PartitionAxis, LabelValued):          name = "well"
    class Site(Axis, TileAxis, DefaultVariable, OrdinalValued): name = "site"
    class Channel(Axis, ColourAxis, DefaultGroupBy, OrdinalValued): name = "channel"
    class ZIndex(Axis, StackAxis, OrdinalValued):           name = "z_index"
    class Timepoint(Axis, TimeAxis, OrdinalValued):         name = "timepoint"
```

- **Derived views:** component order, the parallel axis, the defaults, `AllComponents` and its subset views, the Zarr axis descriptors, the viewer default modes, the viewer config `axis_modes`, and the partition-filter target.
- **The only way the kernel asks:** `family.with_role(StackAxis)`. The five enums become one member type plus subset views. `_ComponentTemplate` and the per-call enum construction are deleted.
- **Activation:** one active family per process, selected by the domain entry point before the kernel is imported. Workers are process-isolated, so this is enough. Several families in one process wait until config typing is generic over the family.
- **"Plate" is not an axis.** It is the dataset scope: `dataset_root`, `DatasetScope`, and the `GLOBAL` reduction scope that replaces `FunctionStepExecutionScope.PLATE` (`callable_contract.py:192`).

## The tensor payload (surface G3; replaces K1)

- **Axes are declared.** The payload carries `axes: tuple[AxisSpec, ...]`. Each spec is a declared axis or a spatial dimension, with its roles. This replaces:
  - the single `source_channel_axis` (`runtime_image_values.py:325-432`);
  - the `spatial_axes_yx` assumption that the last two axes are YX (`:382-407`, `aligned_image_payload.py:337`);
  - `ImageShapeRole` rank guessing (`image_shapes.py:50-150`).
- **Space is N-d.** `SourceSpatialDomain` becomes N-d over the axes with a spatial role; YX is the 2-D instance. Spatial axis names (`CENTER_X/Y/Z`, the IJV `y/x`) derive from it.
- **"Bare array or carrier"** is decided once at the function boundary. That removes the accessor switches reached from 513 call sites.
- **Stack logic follows the role.** Hardcoded Z (`source_image_provenance.py:1596,1769`; `source_projection.py:861-1050`; `source_metadata.py:1096`) follows `StackAxis` instead.
- **Undeclared outputs.** A bare array returned without declaration takes its axes from a domain-declared default-axes-by-rank table, and `ImageShapeRole` becomes a view of that table.
- **Codecs stay image-specific.** `image_file_serialization` remains a kernel-pluggable codec family.

## Sources and formats (surface G4)

- **Microscope handlers implement a `DatasetSource` protocol:** `axis_values(axis)`, `available_backends()`, `resolve_metadata_artifact(ref)`, an optional filename-parser capability, and calibration through `Calibrated`/`TileAxis`.
- **`SourcePlaneStoreAdapter` moves into the kernel.** It is the generic source-adapter family, and it lives in `microscopes/bioformats_adapter.py:488` today.
- **The five per-member projection strategies collapse.** `source_metadata.py:1231-1308` becomes one class driven by each axis's declared metadata aliases and fallback.
- **The "openhcsdata" format becomes kernel-native.** Its filename derives from the declared axis order plus per-axis prefixes the domain declares, so `OpenHCSMetadataHandler` legitimately belongs to the kernel. The `_w{key}` (`path_planner.py:2389`) and `_s _w _z _t` (`source_projection.py:214`) codecs are derived from those declarations.
- **Domain-only:** the microscope handlers, plate layouts, the well row/column codec, the omero root rule (`path_planner.py:2413`), the `Microscope` enum (deleted; the handler registry keys are the identity), plate metadata writing and analysis consolidation (domain post-execute hooks).

## Processing semantics (surface G5)

- **The contract family owns execution.** `ProcessingContractDeclaration` owns `execute`, and the `ProcessingContract` enum (`unified_registry.py:1228`) becomes a derived view. The per-member `registry.execute_pure_*` forwarding and the `Flexible` re-dispatch through the enum are deleted. The rank-2 auto-classification probes (`:2306,2358`) take their rank from the declared stack axis.
- **Functions declare roles, not members.** `@required_axis_roles(ColourAxis)` replaces `@required_variable_components(VariableComponents.CHANNEL)`. Those uses are colocalization, color, alignment (channel), tracking (time), thresholding and morphology (stack), and flatfield (`observation_axis=SITE`, a tile/replicate role).
- **The measurement dialect is an ABC in the kernel; CellProfiler is an instance in interop.** It declares sample identity fields (CP: `image_number`), row axis fields (CP adds bin, scale, Zernike) and label variants (CP: unedited, small-removed). These leave the kernel:
  - ImageNumber logic (`equivalence/measurement_rows.py:198-258`, `runtime_measurements.py:1223,1909`, `steps/abstract.py:63`);
  - `from_cellprofiler_xyz` (`source_metadata.py:929`);
  - `CROP_MASK` (`artifacts.py:1811`).

  `MeasurementScope.IMAGE/EXPERIMENT` become `SAMPLE/RUN`, and "image" is the CP dialect's spelling. Per-member side tables (`equivalence/keys.py:789`, `equivalence/cells.py:113`) move onto the members.

## Viewers (surface G6, then library L7)

- **The wire carries declared axes.** It carries `DeclaredAxis(name, label, roles)`. Each viewer owns a `ViewerSlotFamily` that maps roles to native slots (Fiji: colour→C, stack→Z, time→T, otherwise FRAME; several axes in one slot combine values in declared order).
- **Display configs become mappings.** `NapariDisplayConfig`/`FijiDisplayConfig` become `axis_modes: Mapping[Axis, Mode]` with defaults from the roles. This deletes:
  - the per-member `*_mode` fields;
  - `COMPONENT_ORDER`;
  - the exact-set rejection (`config.py:345-349,517-521`);
  - ABBREVIATIONS and METADATA_FORMATTERS (`viewer_component_system.py:762-772`).
- **Validation uses the payload's own declared axes.**
- **One control family for both viewers.** `ViewerControlAction`, keyed by the message-type enum, has lifecycle mixins over a `ViewerServerPort`, a shared ERROR action for unknown messages, and capabilities derived for both viewers. It replaces `NapariControlMessageAction` and `FijiControlMessagePlan`, and it fixes the bug where **Fiji answers unknown control messages with SUCCESS** (`fiji_viewer_server.py:1490`).
- **One `ViewerFamily` class per viewer** owns backend, config key, title, visualizer, slot family and control leaves. `ViewerType` and the three-hop property forwarding (`config.py:1051-1085` → `streaming_config_factory.py:185` → `streaming_config_declarations.py:137`) become derived views.
- **Extraction comes after.** The servers then move to a new domain-blind `streamviewer` library (L7). The first cut: `agent/dto/viewer.py` must stop importing `agent/dto/execution.py`, a chain that today pulls 206 openhcs modules, including the microscopes, into the napari server.

## Runtime (surface G7)

zmqruntime already supplies the generic execution server, client, progress stream and lifecycle. The OpenHCS side renames over generic semantics:

| Today | Generic name |
|---|---|
| `plate_path` | `dataset_root` |
| `owned_wells` | `owned_partitions` |
| `wells` | `axis_values` |
| `well_filter` | `partition_filter` (`WellFilterConfig` → `PartitionFilterConfig`) |
| `EXECUTION_PLATE_ID_FIELD` | the zmqruntime field |

Also on the OpenHCS side:
- The lane identity tuple, copied into `emit` 9 times, comes from `ProgressExecutionContext.identity_for_event`.
- The 21 string-tagged worker IPC messages become a typed message family.
- `zmq_orchestrator_environment.py:65` (which imports `microscopes.omero`) becomes a domain-registered hook.

## Authoring surfaces (surface G8)

- **The plate manager becomes a container manager** whose noun the domain supplies. Generic model: dataset (root plus `DatasetSource`) → axes → roles → labels.
- **MCP DTOs:**
  - `well=` becomes `component_filters: Mapping[axis, values]`, validated against the family;
  - `microscope_type` is declared once on a `ContainerTarget` base as `source_format`, its choices taken from the handler registry;
  - the `well_filter` alias fallback in `agent/dto/execution.py:219` is deleted.
- **The image browser.** Its plate grid becomes a `GridView(family.with_role(GridAddressed))`, hidden when no axis has the role, and coordinate decoding moves onto the role. WELL carries two roles that must separate: partition and grid.
- **Per-member strategies become families:**
  - `.cppipe` import (`pipeline_editor.py:969`) becomes a `PipelineImporter` family keyed by suffix, with CellProfiler registering from interop;
  - the CellProfiler scope marker becomes a `ScopeSubKind` family.
- **Domain-only:** the 96-well default grid, the MetaXpress merge, the installed neurite demo, and the CellProfiler/MetaXpress LLM context sections (registered from the domain package; the registry already allows it).

## First-party libraries (surfaces L1 to L7)

Generic work that OpenHCS does itself moves to the library that owns the concept. Each move is a library PR, merged and tagged, then an OpenHCS PR that bumps the pin and deletes the local copy, with no re-export. About 5.5k lines leave `openhcs/`.

| ID | Library | Takes |
|---|---|---|
| L1 | metaclass-registry | `core/registry_strategies.py` (506 lines, 60 importers); the cache family from `process_local_cache.py` |
| L2 | python-introspect | `to_jsonable` (becomes the one encoder next to the existing `dataclass_from_mapping` decoder, which replaces `AgentDtoJsonCodec` and `DebugJsonCodec`); `public_api`; a `lazy_exports` helper replacing `__getattr__`/`__dir__` copied verbatim across five libraries |
| L3 | zmqruntime | the process-launch policy (now in `pyqt_reactive/process_launch.py`); execution transport config; `plate_id`/`WELLS` renamed to `subject_id`/`axis_values` (0.5, with the PolyStore and pyqt-reactive bounds bumped in the same train); the 45 hand-written `to_dict`/`from_dict` replaced by the L2 codec |
| L4 | pyqt-reactive | the editable table from `source_bindings_editor.py:125-1374`; an open, registered `PathCacheKey` family (it restates OpenHCS keys today); deletion of OpenHCS's verbatim copy `core/path_cache.py` |
| L5 | arraybridge | an `ArrayOperations.for_memory(...)` namespace; the six per-backend processor files (5,608 lines) are written once against it, with numeric parity checked per backend |
| L6 | pycodify, ObjectState | the nested-enum formatter fix (pycodify `formatters.py:77-87`), path factoring and `PythonSourceLiteral`; `objectstate.codegen` for the LazyDataclass formatter |
| L7 | new `streamviewer` | zmqruntime's viewer protocol and state, PolyStore's streaming receivers, and the napari/Fiji servers, component system and controls (about 12k lines) |

A separate compiler-kernel library is not warranted. It would have one consumer, so the kernel stays a package inside OpenHCS.

## Package layout

```
openhcs/kernel/        axes, payload, sources (protocol), compiler, runtime, artifacts, measurements (abstract), storage, config
openhcs/authoring/     GUI, MCP, agent surfaces over kernel declarations
openhcs/domains/microscopy/   axis family, handlers, formats, plate views, consolidation, presets
openhcs/domains/cellprofiler/ interop, CP backends, measurement dialect, importer
```

The layout moves last (P2). Every earlier surface already writes its new modules into it.

## Witness

A second domain must be declarations only. The CI witness is a test that declares a non-microscopy family, compiles and runs a small pipeline over a synthetic dataset, and streams it to a headless viewer. For example, remote sensing: `Scene(PartitionAxis)`, `Band(ColourAxis)`, `Tile(TileAxis)`, `Date(TimeAxis)`, with no stack axis. It must pass with zero kernel edits. A ratchet counts domain member references in kernel modules, and the count only goes down.
