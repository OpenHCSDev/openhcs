# Domain-independent processing and UI extraction

Assessment and planning goal started 2026-09-11. No production refactor is
authorized by this plan alone. Existing manuscript and NRA work is preserved.

## Intended outcome

OpenHCS remains a functioning specialization of a shared processing application.
Its component declarations, domain configuration, function catalog, source
integrations, and enabled streaming clients provide the application-specific
semantics. Generic processing and UI code does not know which members exist in
`AllComponents`.

Changing the component family and its declared policies must propagate through
forms, code authoring, source identity, compilation, runtime, materialization,
and streaming without edits to generic consumers. This is a declaration-change
acceptance criterion, not permission to silently reinterpret existing saved
data or dynamically replace enum classes in a running interpreter.

The component configuration system already supports an arbitrary enum and
declared execution/grouping defaults. Preserve this authority. The main work is
factoring compiler and downstream assumptions so they consume it consistently.
Do not replace it with a new central table that copies the same semantics.

Fiji and Napari are reusable tensor/image clients. Their installation in a
microscopy application does not make their transport, UI, or rendering
mechanisms intrinsically biological. Their actual dimensional and rendering
constraints must remain explicit at the client boundary.

## Evidence and review artifacts

- [Component and compiler inventory](component_inventory.md)
- [UI, application, MCP, and streaming inventory](ui_streaming_inventory.md)
- [NRA capabilities and dry-run evidence](nra_leverage.md)
- [NRA scan scope, timing, and results](nra_scan_evidence.md)

These inventories are architectural evidence, not runtime registries. Production
behavior must continue to derive from the actual declarations. File counts and
search matches are candidate coverage measures, not counts of proven defects.

## Baseline

- OpenHCS HEAD: `e867013a8eb188edcc63b5b0cdfd06f42a99b409`.
- NRA HEAD: `5f96c76358fe7c3be53af8d325bc513d693168e4`, with substantial
  pre-existing uncommitted native-proof work. This assessment uses that working
  tree, not a claim about a published NRA version.
- `rg --files openhcs -g '*.py'` found 675 Python paths.
- The refined lexical member-access search over `AllComponents`,
  `VariableComponents`, `GroupBy`, `SequentialComponents`, and
  `StreamingComponents` found 258 occurrences in 51 candidate files. This
  includes legitimate domain declarations and `GroupBy.NONE`; it misses literal
  names, positional records, imported aliases, and dynamically assembled names.
  The initial looser search returned 52 paths because it also admitted leading
  underscores. The component inventory preserves the refined query and full
  classified path list.
- A Python AST import census of external package source found no direct
  `openhcs` imports, including imports under `TYPE_CHECKING`. The census excluded
  directories named `tests`, `.venv`, `build`, `docs`, and `examples`; dynamic
  imports and string references were not covered. Existing generic packages
  already provide useful dependency boundaries.

## Existing authorities to preserve

| Question | Current owner or foundation | Extraction consequence |
| --- | --- | --- |
| Which components and defaults are configured? | `components/framework.py:ComponentConfiguration` | Reuse the existing configuration, separate its OpenHCS default binding from generic consumers. |
| How are effective settings resolved? | ObjectState and nominal nested configuration | Preserve inheritance, provenance, reset, snapshots, and saved/transient edit semantics. |
| What pipeline did the user author? | `PipelineDocument`, `PipelineConfig`, `FunctionStep` | GUI, code, MCP, and importers continue to share one declaration model. |
| What does a function require and produce? | `CallableContract`, processing and artifact declarations | Capability constraints belong here, not in a compiler list of known functions or axes. |
| What will execute? | `CompilationSession`, `CompiledStepPlan`, `CompiledExecutionBundle` | Derive plans once; workers do not reinterpret mutable configuration or infer domain identity. |
| Which values exist? | Nominal runtime values and their store | Preserve artifact identity and provenance while removing fixed-coordinate assumptions. |
| How is an implementation selected? | Existing ABCs, nominal registration, and MRO selection | Reuse the existing lattice; extra classes or registries are not inherently improvements. |
| How do widgets, storage, arrays, transport, and source generation work? | pyqt-reactive, PolyStore, ArrayBridge, ZMQRuntime, pycodify | Keep generic infrastructure in its existing owning package where that responsibility already belongs. |

## Extraction sequence

### 1. Characterize declaration propagation and bootstrap

Build a small alternate component family in tests with no microscopy member
names. Vary membership, declaration order, component value domains, grouping
defaults, and execution-axis selection. Exercise it through fresh process
startup rather than mutating an already-imported module global.

Trace failures along configuration -> source projection -> compilation ->
execution -> UI/streaming. Add fixtures at real boundaries, preserving the
current OpenHCS baseline. Do not make stubs that supply the exact fixed fields
the test is supposed to show are unnecessary.

The application's selected declaration/configuration must be bound before
dependent enum classes, lazy config classes, and catalog registrations are
constructed. The startup/process identity design is an early prerequisite;
stage 5 verifies its complete persistence and transport behavior. An alternate
application must not eagerly import biology leaves that access absent members
just to discover the generic catalog or build a form.

### 2. Factor coordinate identity and source projection

Build on the existing component-value and source-binding authorities. Remove
generic dependencies on a five-field record, microscopy-specific value
normalization, and filename spelling. Native microscope formats may still name
their actual vendor coordinates inside their source declaration/adapter.

Example: `OpenHCSPlaneAddress` already stores a component collection, but its
constructor treats `WELL` specially and `from_values` enumerates five members
(`core/source_projection.py:55-96`). This needs semantic factoring, not just a
class rename. The codec for a physical source format can remain domain-specific.

### 3. Factor compiler and runtime consumers

Preserve already-generic execution-axis resolution. Audit dependencies reached
by compiler phases, not only direct references inside `compiler.py`.

In particular, `compiler.py:1015-1045` reads the configured execution axis but
also consumes `WellFilterConfig`/`WellFilterProcessor` semantics. Distinguish
generic axis selection from plate-coordinate selection syntax, then make the
compiler consume the resolved selection contract. Do not rename every local
`well` variable and call the compiler generic.

Follow the same authority through grouping, source universe, function patterns,
sequential state, artifact routing, worker assignment, materialization, and
result aggregation. A declaration that changes the execution component must
change all these projections coherently.

Sequential compilation is a concrete correspondence boundary: the producer
stores Cartesian value tuples while the consumer reconstructs their component
keys from configuration/cardinality (`compiler.py:471-495,762-805`). Both
currently derive their sequence from the configuration, and the consumer checks
the width; this assessment has not reproduced a misassociation. Carrying the
declared keys with the values would remove the need for those paths to
independently reconstruct their correspondence.

### 4. Derive UI and display surfaces

Factor reusable application shell/editor/manager behavior from OpenHCS catalog,
configuration, source, and presentation choices. Use existing reactive form and
configuration projection machinery; do not author another application-specific
schema language or hand-maintained widget list.

Display settings currently use `AllComponents.ordered_names()` while also
listing `site_mode`, `channel_mode`, `z_index_mode`, `timepoint_mode`, and
`well_mode` individually (`core/config.py:255-538`). Membership-dependent fields,
code serialization, wire conversion, and effective defaults must derive from
the same declarations, rather than each surface carrying its own member list.

Reusable widgets belong in pyqt-reactive. A generic processing application
shell may need a processing-layer owner above those widgets; do not make
pyqt-reactive depend on the processing compiler merely to move all UI files out
of OpenHCS. Packaging decisions follow the semantic dependency analysis.

### 5. Carry declarations across process and persistence boundaries

Ensure UI, execution server, workers, and viewers agree on the selected schema
and stable serialized identities. Existing enums are process-local globals
created from `get_openhcs_config()` in `constants/constants.py:130-229`.
Preserve spawn/pickle identity while separating the OpenHCS application binding.

Saved Python pipelines, sessions, source metadata, output naming, and streaming
messages need explicit compatibility tests. Keep any required legacy decoding
at a versioned input boundary; it must not become a permanent second runtime
authority or a fallback chain inside generic consumers.

### 6. Extract packages after boundaries work

Move coherent mechanisms only after the alternate component family runs through
them and imports point in the intended direction. Use NRA for dependency-aware
module extraction and consumer/import changes where its preconditions are met.

The OpenHCS application retains biology/microscopy leaves and its product
assembly. A media application remains a separate follow-on; it is not necessary
to build Silverstack/Nuke/Resolve integrations to validate this extraction.

## Acceptance gates

1. **Membership blindness:** no generic imports or dispatch on specific
   component members, names, fixed tuple positions, or per-member field lists.
   Domain-owned codecs/functions are distinguished by actual dependency
   boundaries, not exempted through an ever-growing file-name allowlist.
2. **Declaration-only change:** alternate membership and order update UI options,
   source identities, compiled plans, output identities, and viewer axes without
   generic source edits. Include added and removed components, unequal
   cardinalities, missing combinations, alternate execution/grouping choices,
   and textual component values whose identity must not be normalized as plate
   coordinates. Invalid declarations must be rejected by their actual owner.
3. **Execution equivalence:** existing bounded OpenHCS fixtures preserve
   numerical results, per-component association, artifact provenance, and
   selected outputs. Exercise grouping, dictionary function patterns, sequential
   processing, and intermediate/final materialization together.
4. **Process identity:** fresh spawned workers/server and restart/session reload
   resolve the same component declarations; mismatched schemas are diagnosed at
   their boundary rather than silently reordered or coerced.
5. **Real UI:** interact through supported MCP with generated forms, nested
   defaults, reset/inheritance flashing, row previews, code round trips, selection,
   compile/run, and viewer handoff. Capture screenshots with differently sized
   axes and recognizable values. Unit tests alone do not establish this gate.
6. **Viewer capability:** Napari and Fiji derive routing/axes from declarations;
   genuine client dimensional limitations produce owner-defined validation.
   Client-specific image constraints are not erased to make tests pass.
7. **Compatibility:** existing saved code/configs/sessions and source formats
   remain usable or have an explicit tested migration at their input boundary.
8. **Performance:** compare cold/warm compile, UI construction, spawn, and
   representative execution on the same fixture/environment. Avoid per-pixel or
   per-frame schema discovery; resolve declaration projections at their existing
   setup/compilation boundaries.

## Scope distinctions

- Schema selection before application startup is the first target. Simultaneous
  unrelated domain schemas within one interpreter or live schema replacement
  is a separate design requirement, not assumed here.
- Physical array shape and callable rank constraints are distinct from filename
  component membership. Removing five named components does not prove arbitrary
  tensor-rank support. Existing `PURE_2D`/`PURE_3D` declarations and image/label
  artifact behavior need an explicit later capability review.
- Declared data-axis order is meaningful data semantics. MRO governs nominal
  implementation specificity; it should not replace tensor coordinate order.
- The goal is removal of distributed knowledge, not maximizing class count,
  interface count, file splits, or automated-edit percentage.
- NRA findings and simulations guide the work. Unknown proof or a scan deadline
  stays unknown; neither becomes evidence of architectural correctness.

## Review rules for agent-proposed abstractions

Inventory entries may propose a boundary, but that does not automatically
justify a new type. Before adopting one:

- Identify the existing declaration that already answers each question. Extend
  or extract that owner instead of surrounding it with a copied description.
- Separate source-format, component, viewer, and application policy. A single
  universal manifest must not become a second representation of every owner.
- Put repeated implementation in a shared nominal ancestor where its contract
  belongs; use meaningful MI for orthogonal behavior. Delegation and manifests
  are not inherently preferable to inheritance.
- Treat first-match route tables as potential semantic ordering. If selection
  means nominal specificity, derive it through the existing MRO-based owner;
  do not bless arbitrary insertion order because it is called routing.
- Base-declared defaults are explicit behavior. Unknown-axis guesses and
  consumer fallback chains are not a substitute for missing declarations.
- Keep reusable window/editor/client mechanics outside the OpenHCS domain
  assembly. Only the genuinely application-specific choices and leaves remain.

## Assessment result and implementation handoff

The source-backed inventory and staged plan are prepared. The three independent
Luna extra-high-reasoning audits were reconciled against the existing ownership
model. The master sequence above governs the implementation order; the
individual inventories supply evidence and applicable tooling, not competing
architectures.

The first implementation slice should establish an alternate component family
through the existing configuration authority, then factor the source-coordinate
and compiler-selection contracts reached by that fixture. Do not start by
moving arbitrary classes into smaller files or inventing a new configuration
framework.

NRA leverage is concrete but bounded:

- Bounded source-context scans completed with all 79 detectors; the compiler
  scope identified materialization-backend ownership coupling.
- Two real OpenHCS closure-extraction simulations derived import/dependency
  edits across five and seven files, respectively, with parse-valid projected
  output and `applied=false`. These are mechanics probes, not prescriptions to
  perform those particular file splits.
- The preserved recipes both passed the CLI's `--codemod-validate-plan` command
  in a separate parent check, using a 60-second budget.
- Initial full-package scans exceeded their deadlines. The subsequent NRA
  performance batch completed full-package cold and warm scans within the
  agreed budgets; see the follow-up in [scan evidence](nra_scan_evidence.md).
  Dynamic enum-family recovery and the current native-proof class-member
  preflight failure remain separate gaps. A complete detector scan does not
  establish unrestricted automatic factoring.

Cross-reference checks found 127 qualified Python source paths across the
reports. The only absent paths were the two explicitly simulated destination
modules, which were intentionally not created. Internal Markdown links resolve.
The refined candidate searches and counts were independently reproduced.

Implementation decisions to settle with the first slice are the exact typed
membership-dependent field projection, application binding before enum/config
construction, and preservation/migration of existing serialized identities.
The acceptance gates define how those choices must be tested; an architectural
inventory does not substitute for running them.

No OpenHCS production code or submodule code was changed. No release, live UI
validation, numerical equivalence run, or end-to-end domain extraction was
performed in this assessment. Existing manuscript and NRA implementation work
remains untouched.
