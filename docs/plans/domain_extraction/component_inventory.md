# AllComponents domain-extraction component inventory

**Status:** audit and planning only; no production source or test files were changed.
**Repository:** /home/ts/code/projects/openhcs. **Audit date:** 2026-09-11.

## Finding in brief

ComponentConfiguration already is the generic configuration authority. It
accepts an enum, declared order, multiprocessing member, and declared defaults
(openhcs/components/framework.py:16-92,121-179). The current OpenHCS template is
one domain-owned declaration of the five application components (:181-208).
Other format, microscope, and UI leaves may legitimately name roles for their
own contracts; that does not make them generic membership authorities.
constants._create_enums() then derives process-local AllComponents,
VariableComponents, GroupBy, SequentialComponents, and StreamingComponents from
that configuration (openhcs/constants/constants.py:131-221). This inventory
does not propose a second configuration system or a parallel component table.

The extraction blockers are downstream consumers which turn that existing
declaration into fixed OpenHCS fields or algorithms:

1. The compiler still calls a WellFilterConfig/WellFilterProcessor, names
   compiler variables wells, emits an all_wells zarr field, and resolves step
   filters through well-specific provenance. The process axis is obtained
   dynamically, but the filtering contract is not.
2. Sequential compilation stores bare positional Cartesian-product tuples and
   later zips them to a filtered component list. Producer and consumer currently
   agree on the same sequential configuration; the design is nevertheless a
   positional correspondence dependency that must be proven for changed order
   and cardinality or replaced by named coordinate records.
3. Source binding projection constructs an address with exactly
   well/site/channel/z_index/timepoint and injects a channel label in a generic
   projection strategy. A site leaf also infers a default from the presence of
   Z/timepoint fields.
4. Canonical address and OpenHCS metadata persistence have five separate
   fields, while metadata and cache layers use generated enums as their key
   identity. This is both a fixed-domain serialization boundary and a
   process-global identity boundary, not evidence that configuration should be
   rebuilt.
5. Viewer configs use five separate mode fields and the Napari separate-layer
   strategy forces well. The viewer is a projection, so its component modes,
   labels, and role capabilities need to be derived from the declared layout.

Microscope and file-format parsers necessarily know their native layout. They
are leaf owners, not generic consumers, and should retain their native C/Z/T,
row/column, folder, or filename grammar behind the parser/handler contract.
A native codec may remain a fixed, explicit domain output; it need not be
generalised merely to extract the engine. Where a format uses the canonical
address, construction should cross a declaration-driven boundary and fail
explicitly when a new domain has no declared format capability. The compiler
must not infer capability from a member name.

## Audited contract and method

The maintained architecture front door was read before source inspection:

- docs/source/architecture/quick_start.rst:33-52,164-184,286-293 defines the
  declaration -> ObjectState -> snapshot/session -> typed plan -> runtime path,
  says declarations own semantics, and separates variable_components, group_by,
  and ProcessingContract locality.
- docs/source/architecture/system_overview.rst:35-95 defines the compiler,
  worker, runtime-store, and materialisation boundaries.
- docs/source/architecture/nominal_ownership.rst:1-64 requires one nominal
  owner, ABC roots, registry selection, and owner-side specialisation.
- docs/source/architecture/abstraction_lattices.rst:16-53,133-173 identifies
  parallel tables, nominal mirrors, caller-side dispatch, and unnecessary
  registries as failure shapes.

No AGENTS.md exists under the repository parent (verified with
find .. -name AGENTS.md -print). The worktree contains unrelated dirty paper/
changes; they were preserved. Tests, archived plans, and benchmark fixtures
were not treated as production architectural owners. Test names are only
mentioned in the validation plan below.

The reproducible searches used for the inventory were:

~~~text
rg -l 'AllComponents\.[A-Z][A-Z0-9_]*|VariableComponents\.[A-Z][A-Z0-9_]*|GroupBy\.[A-Z][A-Z0-9_]*|SequentialComponents\.[A-Z][A-Z0-9_]*|StreamingComponents\.[A-Z][A-Z0-9_]*' openhcs --glob '*.py' | sort
rg -o 'AllComponents\.[A-Z][A-Z0-9_]*|VariableComponents\.[A-Z][A-Z0-9_]*|GroupBy\.[A-Z][A-Z0-9_]*|SequentialComponents\.[A-Z][A-Z0-9_]*|StreamingComponents\.[A-Z][A-Z0-9_]*' openhcs --glob '*.py' | wc -l
rg -il '\b(well|wells|site|sites|channel|channels|z_index|z_indexes|timepoint|timepoints)\b' openhcs/core openhcs/runtime openhcs/microscopes openhcs/interop openhcs/agent openhcs/pyqt_gui | sort
~~~

In this checkout the strict enum-member expression search reports 258
expressions in 51 Python paths. The broader role-word search reports 76 paths;
many are legitimate biology, microscope, UI, progress, or documentation
leaves. The path inventories at the end preserve the complete strict search
result and distinguish reviewed shortlist entries from lexical candidates not
selected for a generic refactor.

## Authority and ownership chain

The intended chain is:

~~~text
ComponentConfiguration (declared enum/order/roles/defaults)
  -> process-local generated enums (derived selection views)
  -> typed component values, scopes, source bindings and contracts
  -> nominal owner leaves (source metadata, microscope, storage, viewer, algorithm)
  -> compiler plans and runtime/artifact/materialisation projections
  -> string-keyed wire or persisted adapters
~~~

The generated enums are not a safe live registry. constants.py:132-140 uses a
one-entry cache, and :154-183,200-221 creates and publishes enum classes once
per process with pickleable module/qualname identity. AllComponents membership
and order are therefore frozen at first startup for that process. Changing the
domain means selecting a different declaration before importing enum consumers
in a fresh process; it does not mean hot-switching a live process. Separate
simultaneous domains would require an explicit future process/context boundary
and are outside this audit.

Good existing generic mechanisms to preserve are:

- ComponentSet (openhcs/core/component_set.py:18-139) for ordered unique
  component sets and config-derived defaults. Its required_last()/last() are
  intentionally order-sensitive and need explicit order tests.
- OpenHCSComponentValues (openhcs/core/components/component_values.py:15-155)
  for complete, declaration-ordered, enum-keyed values and string-keyed wire
  projection. Its exact cardinality and member-name projection are
  serialization constraints, not permission for consumers to add a fixed
  member list.
- SourceComponentProjectionStrategy
  (openhcs/core/source_metadata.py:444-529) and its registered leaves for
  metadata aliases/defaults, plus SourceSetAssembler
  (openhcs/core/source_binding_workspace.py:245-305) for match-method selection.
- RuntimeExecutionAxisScope and RuntimeValueStore for typed runtime scope and
  artifact lookup (openhcs/core/component_group_scope.py:300-405,
  openhcs/core/runtime_stores.py:114-129,487-510).
- ZarrComponentAxisProjection (openhcs/core/steps/function_io.py:177-271) for
  registered storage-axis leaves ordered by their declared NGFF order.

These mechanisms are declaration-driven but currently have fixed OpenHCS leaf
sets around them. The correct change is to extend the owning leaf/contract or
make the projection consume a declared map, not to add a consumer-side
if component == ... table.

## Findings by semantic boundary

### 1. Configuration and process identity: authority versus frozen identity

ComponentConfiguration is already the right generic owner. Its
get_remaining_components() preserves declared order and excludes only the
configured multiprocessing axis (framework.py:79-118); factory defaults are
positional only when the caller omits explicit defaults (:147-179). The current
OpenHCS template is intentionally domain-owned (:181-208). Do not replace these
with a second AllComponents declaration.

constants.py:154-183 derives all companion enums from configured member names,
values, and order. :310-332 derives defaults and multiprocessing selection from
the same config. This is the source of truth for process-local enum identity,
but it also means persisted or pickled values cannot silently cross a process
started with a different enum declaration. A future custom-domain gate must
start a fresh process, configure the declaration, then import the constants. It
must verify member names, values, order, enum identity, and pickle/transport
behaviour. There is no assumption of live hot switching.

### 2. Compiler and execution-axis assumptions (highest priority)

openhcs/core/pipeline/compiler.py is the primary extraction target:

- :471-495 filters SequentialComponents by discovered cardinality, then zips
  the filtered component sequence to a bare current_combination tuple. The
  tuple has no component keys. Producer and consumer currently use the same
  sequential configuration, so no order-change corruption was reproduced;
  the association is nevertheless a positional agreement dependency and is
  structurally fragile under changed order/cardinality.
- :762-805 builds those bare tuples with itertools.product and stores them in
  context.pipeline_sequential_combinations; :1321-1335 copies each tuple into
  every per-axis context. The owner should emit a named coordinate record
  (component -> value, retaining declared order) and derive a runtime filter
  from that record. A missing/one-value axis should be removed by key, not by
  positional zip.
- :591-608 asks the configured multiprocessing axis for values but stores them
  under all_wells in zarr config. The algorithm is already generic; the field
  name and downstream schema are not.
- _axis_values_to_process, :1009-1044, reads effective_config.well_filter_config,
  calls WellFilterProcessor, and logs “wells”. _resolve_step_axis_filters,
  :1721-1778, repeats the same WellFilterConfig type, provenance field, and
  processor. These are compiler hardcodes even though get_multiprocessing_axis()
  is dynamic.
- _calculate_worker_assignments, :1500-1515, names its input wells, rejects
  duplicate well IDs, sorts values, and assigns modulo worker slots. The stable
  assignment algorithm is reusable after renaming the contract to an
  execution-axis record and making value ordering an explicit owner policy.

The existing app selection limitation must remain distinct from this finding:
WellFilterConfig and the desktop/ZMQ request fields are application-facing
selection APIs. Their existence does not show that ComponentConfiguration
cannot express a different axis. Refactor compiler consumption around the
configured axis while retaining a compatibility adapter for current well-named
UI/API fields until their external wire schema is versioned.

openhcs/core/components/multiprocessing.py:27-83 is already a generic
coordinator, but the compiler has a separate assignment/filter path. Treat it
as a possible duplicate owner to reconcile, not as a reason to add another
coordinator.

openhcs/core/utils.py:348-376,386-445,452-570 is not generic despite its
claims: WellFilterProcessor owns well grammar, row:/col:/range handling, and an
Opera Phenix fallback (:583-641). Generic include/exclude/count resolution can
be a process-axis policy; row/column grammar belongs to a declared
plate-layout/process-axis leaf. No generic caller should infer that an
arbitrary component supports row/column or Opera naming.

### 3. Source metadata and source-binding workspace

The strategy root is a sound owner boundary, but the current leaves are the
five-domain implementation:

- openhcs/core/source_metadata.py:532-620 declares well/site/channel/Z/time
  aliases, defaults, and collection fields. These are owner leaves and should
  be replaced/extended when the domain changes.
- SiteSourceComponentProjection.project, :560-579, checks for
  AllComponents.Z_INDEX and AllComponents.TIMEPOINT before defaulting site to
  \"1\". That is cross-role inference in a leaf. If this relationship is
  required, declare it as a capability/relationship on the owner; do not let a
  generic consumer infer it from membership.
- openhcs/core/source_bindings.py:1114-1132,1225-1238 has generic
  requires_step_input_component_stack alongside hardcoded
  requires_step_input_channel_stack. Keep the generic method and make the
  channel convenience property an owner/compatibility surface.
- openhcs/core/source_binding_workspace.py:516-538 injects a channel label
  from PrimaryPlaneBindingProjection. The label association is channel
  semantics and should be declared by the relevant component/format leaf.
- :1120-1183 constructs each missing address with well, site, channel, Z, and
  timepoint. :1185-1247 has a dedicated _source_set_well() and tests whether
  grouping metadata is well identity. :1249-1272 is the desired
  declaration-driven pattern: iterate declared components and project each
  through the owner strategy.
- MetadataSourceSetAssembler, :309-450, and OrderSourceSetAssembler, :453-495,
  are legitimate matching leaves. ORDER is explicitly positional: aliases are
  paired by candidate index and result count is min(...). Preserve this only as
  the declared SourceBindingMatchMethod.ORDER contract; do not let positional
  order leak into metadata matching or canonical component identity.
- _expand_candidate_source_axes, :1040-1091, correctly zips declared source
  stack components to source-axis indices. Its component sequence is a source
  binding declaration, not AllComponents membership inference; tests must
  protect that distinction.

### 4. Canonical address, persistence, and artifacts

openhcs/core/source_projection.py:54-98 has the clearest fixed-domain leak:
OpenHCSPlaneAddress.from_values() accepts five separate positional/name fields
and constructs a five-member tuple. :174-210 hardcodes the canonical filename
regex and _s, _w, _z, _t order. Numeric normalisation also special-cases
AllComponents.WELL (:65-74). This class is an OpenHCS canonical-address/filename
owner, not a generic component consumer. Keep the generic coordinate owner
separate from the OpenHCS filename codec: the former can own a
declaration-driven coordinate schema, while the latter retains a versioned
legacy five-field filename adapter.
OpenHCSComponentValues remains the typed identity and wire-map owner.

openhcs/core/virtual_workspace_metadata.py:148-183 declares separate CHANNELS,
WELLS, SITES, Z_INDEXES, and TIMEPOINTS fields. Its
VirtualWorkspaceSourceProjectionEntries._projection_record, :292-349, requires
the same five named address fields and calls from_values(). The metadata adapter
should persist a versioned component-keyed projection for a new domain (with
schema/version and explicit migration reader for old documents), rather than
silently dropping unknown components or populating a fixed mirror. The
component/value declarations remain the schema authority.

openhcs/microscopes/openhcs.py:788-873 repeats the fixed persisted dataclass
fields and serialises each named component separately; :891-923 reads those
fields back. _extract_metadata_from_disk_state/merge helpers, :1158-1230,
already iterate generated components, but :1139-1156 projects five separate
fields. This is a storage schema owner and needs a versioned dynamic projection
plus legacy read/write projection while old files remain supported.

openhcs/core/metadata_cache.py:14-52,63-94 is a useful generic cache keyed by
generated components, but its process-local enum identity and metadata
string-key conversion are boundaries that must be tested. It must not become a
second list of domain names.

Artifact plans are mostly correctly typed:
openhcs/core/artifacts.py:2230-2321 stores group_component, variable_components,
and component domains through ComponentSet/ComponentGroupScope; :2812-2884
does the same for input projections. :712-724 asks provenance for varying
values across tuple(AllComponents), which is generic when the set is the current
declared domain. Keep this owner chain and ensure serialised artifact keys carry
component values as strings with a declaration/schema identity, not enum object
identity from another process.

openhcs/core/steps/function_io.py:177-271 is a proper strategy root. Its current
leaves at :274-307 are fixed NGFF mappings (time -> t, site -> field, channel ->
c, Z -> z) and a channel qualifier. They are storage-format owners, not generic
inference. A custom domain must provide its own registered axis leaves or
explicitly fail capability validation; do not silently map the first four
members to NGFF axes.

openhcs/core/pipeline/path_planner.py:2815-2846 is a storage-path owner but
build_dict_pattern_path() is explicitly channel-specific and inserts _w after
the well. It should consume the declared group component and a format/path
leaf. The artifact-input loop at :1254-1265 zips declared input edges and
contract inputs; that positional correspondence is valid only because the
contract declares input order, and should remain typed/validated rather than
being duplicated by a component table.

### 5. Runtime, progress, viewer, and analysis projections

Runtime stores and scopes are generic when addressed by AllComponents, but
runtime/progress wire models still expose application-specific names:

- openhcs/core/orchestrator/analysis_consolidation.py:262-293 requires
  AllComponents.WELL, removes it from coordinate segments, and returns well_id.
  Analysis consolidation may legitimately require a plate/process identity, but
  that requirement must be declared by the analysis output owner and resolved
  from configured multiprocessing axis, not silently imposed on all artifacts.
- openhcs/runtime/zmq_compilation.py:68-85,154-169 and
  openhcs/runtime/zmq_execution_server.py:274-287,570-617,702-725,870-905
  carry wells, owned_wells, and _wells_for_execution even though the server
  queries MULTIPROCESSING_AXIS. These are external transport and UI
  compatibility fields. A generic internal axis record can feed a versioned
  compatibility projection; do not change wire meaning silently.
- openhcs/runtime/zmq_progress.py:74-203 and
  openhcs/core/progress/types.py:523-745 use total_wells/owned_wells in
  transport payloads. core/progress/projection.py:556-560 also derives a
  sorted axis list from that field. Treat this as a wire schema migration and
  preserve axis_id as the generic internal identity.
- openhcs/core/utils.py:80-135 has a separate thread-activity decorator that
  guesses a well from kwargs or positional argument 2. This is an independent
  positional/literal consumer and must either consume the typed execution-axis
  context or remain explicitly app-only.

openhcs/core/config.py:254-379 (NapariDisplayConfig) and :392-539
(FijiDisplayConfig) have site_mode, channel_mode, z_index_mode, timepoint_mode,
and well_mode fields, a five-entry component_modes() map, and payload readers
that index those names. The existing layout payload is a projection of display
configuration. Extraction should factor role-specific typed fields/carriers
from the declaration-derived layout while preserving ObjectState paths, field
types, inheritance, and code round-trip; it must not replace the typed state
with an untyped dict. Retain a versioned five-field reader for old payloads.

openhcs/runtime/viewer_component_system.py:676-692 has a five-entry display
abbreviation/formatter map. :822-847 correctly asks the layout and declared
role authority for colour selection; preserve that pattern and move labels and
formatters to component owner declarations.
openhcs/runtime/napari_viewer_server.py:831-855 forces a well layer in
NapariSeparateLayersDisplayStrategy; this should use a declared
display/process-axis role. openhcs/core/steps/stream_component_semantics.py:62-95,
240-278 is mostly the desired generic projection and should continue to consume
the declared layout.

### 6. Source/microscope and algorithm leaves

The following are actual owners of native semantics and should not be made into
generic compiler knowledge:

- openhcs/microscopes/bioformats_adapter.py:386-475,1060-1091,1235-1310 owns
  OME C/Z/T and NGFF c/z/t/field mapping. It currently calls the fixed
  canonical address and supplies fixed labels; adapt that boundary when the
  canonical schema changes.
- openhcs/microscopes/imagexpress.py:121-220,339-438 owns ZStep/TimePoint
  folder grammar and the ImageXpress filename contract.
- openhcs/microscopes/opera_phenix.py:270-345,457-543 owns row/column,
  site/channel/z/timepoint, and its positional native combination tuple.
- openhcs/microscopes/omero.py:98-140,291-327 owns OMERO plate/channel/Z/T
  retrieval and virtual filename projection.
- openhcs/microscopes/microscope_base.py:582-620 is a generic base and is
  therefore different: it requires SITE and CHANNEL and defaults Z. Move those
  requirements to the handler/parser capability declaration; a base handler
  must query the canonical contract.
- CellProfiler backend files which mention VariableComponents/GroupBy
  (processing/backends/cellprofiler/alignment.py, colocalization.py, color.py,
  infrastructure.py, morphology.py, thresholding.py, tracking.py, worms.py)
  are algorithm/module leaves. Their requirements must be declared by the
  callable/module contract; they must not be mined by the compiler as a
  membership table.
- Presets and demos explicitly choose current domain roles. They are authoring
  examples, not generic consumers, and should only be changed when the public
  declaration API or the example's scientific intent changes.

## Deterministic transformations suitable for NRA batching

These are repeated, mechanically recognisable transformations. They are good
codemod/batch candidates only after the owning contract is established; a batch
must not turn a positional workaround into a new mirror.

| Transformation | Repeated sites | Required invariant/owner |
| --- | --- | --- |
| Sequential component list + Cartesian tuple -> named coordinate | compiler.py:471-495,762-805,1321-1335 | SequentialProcessingConfig owns component order; runtime record carries component keys and values. |
| Configured process axis + filter -> selected execution contexts | compiler.py:1009-1044,1721-1778; core/utils.py:364-661; materialization_flag_planner.py:26-65 | process-axis filter policy owns grammar; compiler consumes one resolved typed axis selection. |
| Declared component values -> canonical plane address | source_binding_workspace.py:1141-1163; source_projection.py:80-98; microscope adapters | OpenHCSPlaneAddress/format owner owns schema and legacy adapter; no five positional fields in generic code. |
| Address/source values -> collection labels and metadata | source_metadata.py:532-620; openhcs.py:842-871,1158-1230; metadata_cache.py:31-50 | component strategy/metadata owners define field identity; persisted dynamic data is a versioned projection, with explicit legacy readers, not a second schema authority. |
| Component identity set -> stable ordered identity/path key | source_matching.py:418-545; source_image_provenance.py:1746-1775; function_output_identity.py:498-506,941-959 | declared component order is preserved; value sorting is used only where explicitly declared as presentation policy. |
| Runtime scope component map -> artifact input/output query | component_group_scope.py:300-405; artifacts.py:2230-2321,2812-2884; runtime_stores.py:487-510 | typed scope/artifact plan remains the authority; no raw string fallback. |
| Registered component -> NGFF/viewer axis | function_io.py:177-307; viewer_component_system.py:822-875; stream_component_semantics.py:62-95 | each algorithm/storage/viewer capability is owner-declared; no inferred axis by enum position. |
| Execution axis -> progress/worker transport | zmq_compilation.py:68-169; zmq_execution_server.py:274-905; zmq_progress.py:74-203; progress/types.py:523-745 | internal axis_id is generic; old wells fields are explicit compatibility projections and require schema versioning. |
| Artifact input contract -> edge plan | path_planner.py:1254-1265 | input order is a declared callable/artifact contract and must be validated with strict cardinality. |

## Dependency and serialization constraints

1. Keep ComponentConfiguration as the declaration owner. Generated enum classes
   are derived views; do not add a handwritten membership map, duplicated
   display table, or fallback chain.
2. Preserve ABC roots and existing registry selection. Component, source,
   storage, and viewer leaves declare their strategy_key, capabilities,
   normalisation, role, and native serialization. Use MRO/registry selection
   for specialisation rather than caller-side enum ladders or priority numbers.
3. Treat component member name/value/order as separate identities. In-memory
   values use process-local enum identity. String-keyed wire mappings use
   component values. A new member name/value or reordered declaration needs a
   schema/compatibility decision; it is not an in-place mutation of a running
   process.
4. Persist a schema/version plus dynamic component-keyed maps for new OpenHCS
   metadata, source projections, viewer modes, and addresses. Keep explicit
   legacy readers/writers for current five-field documents and filenames; never
   silently map a missing custom component to a current named field.
5. Keep source bindings, microscope handlers, compiler plans, artifacts, and
   runtime values as distinct owners. A handler owns physical layout; bindings
   own semantic selection/identity; compiler resolves declarations; workers
   consume frozen plans.
6. A domain may have no implementation for a capability (for example an NGFF
   axis, row/column filter, or native filename projection). Fail at capability
   validation with the owner and requested operation named. Do not infer that
   “third member” means Z or that every domain has a channel.
7. Preserve declared component order where it carries meaning (stack axes,
   source stacks, coordinate identity). Lexical sorting may remain a
   presentation/worker-balancing policy only when its owner explicitly declares
   it. ORDER source matching and contract input order are explicit positional
   contracts and must not be conflated with component membership order.
8. The current desktop/ZMQ well selection fields can remain compatibility
   surfaces while compiler consumes a typed configured-axis selection. This is
   an app/API migration, not a replacement for generic config capability.

## Validation gates (fresh-process, custom-domain first)

The eventual implementation should add a small custom-domain fixture with
entirely different names, cardinality, order, and roles, for example PRIMARY,
DEPTH, BATCH (three members, reordered from the current domain), then a second
fixture with two members and a different multiprocessing member. No generic
test should mention well, site, channel, z_index, or timepoint; those names
belong only in legacy/format-leaf compatibility tests.

Required gates:

- **Startup/identity:** in a fresh subprocess, select the custom
  ComponentConfiguration before importing constants; assert exact generated
  enum names/values/order, defaults, multiprocessing and derived companion
  enums. Pickle a value/address/compiled plan and load it in a matching fresh
  child; reject a mismatched declaration/schema explicitly. Do not test live
  hot switching.
- **Typed values and source:** construct complete and partial
  OpenHCSComponentValues, ComponentSet, SourceAxisMetadataScope, and source
  bindings with custom names; assert no missing member, duplicate, or order
  reversal. Exercise both metadata and explicit ORDER matching and verify
  positional pairing is present only when the declared match method is ORDER.
- **Compiler:** select a non-first multiprocessing role; compile with one, two,
  and three variable/sequential components and cardinalities 1/2/3; assert
  named sequential coordinates, correct filtering, worker assignment, zarr
  configuration, and no all_wells/WellFilterConfig dependency in generic
  plans. Assert an undeclared layout/filter capability fails loudly.
- **Artifacts/runtime:** create scopes and artifact plans with reordered custom
  components, query/store them through RuntimeValueStore, materialise and
  rehydrate them, and assert exact component/value identity and deterministic
  declared order.
- **Serialization:** round-trip dynamic metadata/source-projection documents,
  viewer mode payloads, canonical addresses, filenames, and artifact transport
  with custom keys. Separately verify old five-field OpenHCS/legacy microscope
  documents still read through an explicit compatibility adapter.
- **Viewer/progress/transport:** build a custom layout with owner-declared
  labels, roles, and axis capabilities. Assert generic viewer/progress routes
  use axis_id and custom keys; legacy well-labelled payloads remain confined to
  compatibility projections.
- **Algorithm capability:** register a custom owner leaf that declares exactly
  the required operation (for example a storage axis or numeric coordinate
  normaliser). Assert generic compiler/runtime code calls that declaration;
  removing the leaf produces a named capability error rather than a fallback.
- **Static gate:** after implementation, run the strict enum-member search and
  targeted role-word search from this document. New generic consumers must not
  add named member access, separate per-component fields, or fallback strings.
  Remaining named occurrences must be classified as a declaration leaf,
  compatibility adapter, explicit external wire schema, example, or
  documentation.

## Complete strict enum-member candidate paths

This is the complete 51-path result of the strict expression search in this
checkout. R means reviewed as a generic/refactor candidate; L means reviewed as
a domain/algorithm/format leaf or explicit owner; G means reviewed as generic/
intentional enum use; E means example, migration, or documentation surface.
Files with no strict member expression but essential to the same boundary are
listed separately below.

### R - reviewed generic/refactor candidates

- openhcs/core/config.py
- openhcs/core/orchestrator/analysis_consolidation.py
- openhcs/core/pipeline/compiler.py
- openhcs/core/pipeline/path_planner.py
- openhcs/core/source_binding_workspace.py
- openhcs/core/source_bindings.py
- openhcs/core/source_image_provenance.py
- openhcs/core/source_metadata.py
- openhcs/core/source_projection.py
- openhcs/microscopes/microscope_base.py
- openhcs/microscopes/openhcs.py
- openhcs/pyqt_gui/widgets/image_browser.py
- openhcs/runtime/napari_viewer_server.py
- openhcs/runtime/viewer_component_system.py

### L - reviewed owner leaves or capability declarations

- openhcs/core/steps/function_io.py
- openhcs/interop/cellprofiler/module_declarations.py
- openhcs/interop/cellprofiler/pipeline_import.py
- openhcs/microscopes/bioformats_adapter.py
- openhcs/microscopes/imagexpress.py
- openhcs/microscopes/omero.py
- openhcs/microscopes/opera_phenix.py
- openhcs/processing/backends/analysis/consolidate_analysis_results.py
- openhcs/processing/backends/cellprofiler/alignment.py
- openhcs/processing/backends/cellprofiler/colocalization.py
- openhcs/processing/backends/cellprofiler/color.py
- openhcs/processing/backends/cellprofiler/infrastructure.py
- openhcs/processing/backends/cellprofiler/morphology.py
- openhcs/processing/backends/cellprofiler/thresholding.py
- openhcs/processing/backends/cellprofiler/tracking.py
- openhcs/processing/backends/cellprofiler/worms.py

### G - reviewed generic or intentional enum use

- openhcs/constants/constants.py
- openhcs/core/components/validation.py
- openhcs/core/invocation_artifacts.py
- openhcs/core/orchestrator/orchestrator.py
- openhcs/core/pipeline/funcstep_contract_validator.py
- openhcs/core/steps/function_execution.py

### E - reviewed examples, presets, migration, or documentation

- openhcs/agent/services/llm_context_service.py
- openhcs/demo/basic_pipeline.py
- openhcs/demo/synthetic_data.py
- openhcs/demo/synthetic_plate_pipeline.py
- openhcs/mcp/installed_demo.py
- openhcs/processing/presets/mfd_specs.py
- openhcs/processing/presets/pipelines/cy5_axon_cell_body_crop_analysis.py
- openhcs/processing/presets/pipelines/cy5_ctb_cell_count.py
- openhcs/processing/presets/pipelines/czi_brain_axon_cellbody.py
- openhcs/processing/presets/pipelines/imx_96_well_neurite_outgrowth_pipeline_cpu.py
- openhcs/processing/presets/pipelines/imx_96_well_neurite_outgrowth_pipeline_gpu.py
- openhcs/processing/presets/pipelines/loose_operaphenix_neurite_outgrowth.py
- openhcs/processing/presets/pipelines/loose_operaphenix_neurite_outgrowth_metaxpress.py
- openhcs/processing/presets/pipelines/neuroncyto_ii_crossover_neurite_outgrowth.py
- openhcs/utils/pipeline_migration.py

The strict list contains intentional GroupBy.NONE sentinel uses and explicit
current-domain declarations. Those are not generic membership violations by
themselves. The high-priority items are the R paths and the fixed-role
mechanisms above.

## Additional boundary files without strict enum-member expressions

These paths were reviewed or shortlisted because they carry component values,
positional records, separate fields, process-axis names, or serialization
identity despite not containing AllComponents.<MEMBER>:

- Declaration/value core: openhcs/components/framework.py,
  openhcs/core/component_set.py,
  openhcs/core/components/component_values.py,
  openhcs/core/components/multiprocessing.py,
  openhcs/core/components/parser_metaprogramming.py,
  openhcs/core/component_group_scope.py,
  openhcs/core/metadata_cache.py,
  openhcs/core/source_workspace_projection.py.
- Compiler/storage/runtime: openhcs/core/pipeline/materialization_flag_planner.py,
  openhcs/core/compiled_step_plan.py,
  openhcs/core/runtime_stores.py,
  openhcs/core/runtime_measurements.py,
  openhcs/core/measurement_row_materialization.py,
  openhcs/core/runtime_slice_projection.py,
  openhcs/core/steps/function_output_identity.py,
  openhcs/core/steps/function_artifact_materialization.py,
  openhcs/core/virtual_workspace_metadata.py,
  openhcs/core/utils.py.
- Process/transport/progress: openhcs/core/orchestrator/worker_lanes.py,
  openhcs/core/orchestrator/worker_execution.py,
  openhcs/core/progress/types.py,
  openhcs/core/progress/projection.py,
  openhcs/core/progress/runtime_tree.py,
  openhcs/runtime/zmq_compilation.py,
  openhcs/runtime/zmq_execution_server.py,
  openhcs/runtime/zmq_progress.py,
  openhcs/runtime/napari_streaming_handlers.py.
- Source/format/UI: openhcs/microscopes/bioformats.py,
  openhcs/microscopes/microscope_interfaces.py,
  openhcs/microscopes/opera_phenix_xml_parser.py,
  openhcs/microscopes/tiff_metadata_mixin.py,
  openhcs/core/plate_file_inventory.py,
  openhcs/core/plate_image_inventory.py,
  openhcs/pyqt_gui/widgets/source_bindings_editor.py,
  openhcs/pyqt_gui/widgets/shared/plate_view_widget.py,
  openhcs/pyqt_gui/widgets/config_preview_formatters.py.

The broad role-word search intentionally returns many more leaves (algorithm
parameters, image pixel channel axes, CellProfiler Analyst columns, agent
guidance, and UI labels). They remain candidate matches until their owner is
confirmed; they are not evidence that a generic compiler should import them.
