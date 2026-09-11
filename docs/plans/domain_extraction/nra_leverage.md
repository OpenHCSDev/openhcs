# NRA leverage audit for domain-independent extraction

Assessment date: 2026-09-11. This is a bounded audit of the dirty working
trees, not an authorization to refactor OpenHCS. No NRA apply command was run
against OpenHCS and no production file was changed by these probes.

## Scope and evidence boundary

The NRA checkout was `/home/ts/code/projects/nominal-refactor-advisor`, at
`5f96c76358fe7c3be53af8d325bc513d693168e4` with substantial pre-existing
uncommitted native-proof work. The OpenHCS checkout was at
`e867013a8eb188edcc63b5b0cdfd06f42a99b409` and was also dirty. Both worktrees
were preserved. `find .. -name AGENTS.md -print` found no applicable AGENTS
file below the NRA checkout.

The NRA README, `docs/source/api/getting_started.rst`, generated codemod
catalog, current DSL examples, and `PAUSED_NRA_GOAL.md` were read. The paused
goal explicitly says that the current native-proof foundation is unfinished;
current source and tests outrank that handoff. Detector output is an
observation/candidate source only. It is not proof that a transformation is
safe or that behavior is equivalent.

The following claims are therefore deliberately separated:

* **Preflight passed** means NRA source-reproved the operation's declared
  structural preconditions and dependency/annotation facts.
* **Simulation passed** means NRA produced a projected source state, a
  parse-valid AST-span diff, and `applied=false`. It does not execute that
  state.
* **Behavior verified** requires independent OpenHCS tests, fresh-process
  checks, and real UI/runtime checks. None of those were claimed by these NRA
  probes.

## CLI and DSL inventory

The command below was run from the NRA checkout:

```bash
./.venv/bin/nominal-refactor-advisor --detector-capabilities \
  > /tmp/nra_capabilities.json
```

It exited 0 and reported exactly 79 declaration-derived detector capability
records. Relevant observations and executable-recipe bridges include:

| Detector/concept | What is actually available |
| --- | --- |
| `closed_parameter_conveyor` / `declared_carrier_expansion` | `SemanticCarrierConcept`; candidate operations are closed-carrier collapses only when the complete product flow is source-proved. |
| `parallel_mirrored_leaf_family`, `type_keyed_behavior_projection`, `exact_tiny_method_role`, `exact_leaf_method_ancestor_promotion` | `ClassFamilyAuthorityConcept`; strict exact method/MRO operations exist. |
| `manual_class_registration`, `numeric_literal_dispatch` | Auto-register/class-family strategy concepts; executable recipes are limited to their declared registry/dispatch shapes. |
| `autoregister_explicit_priority_ordering`, `inherited_autoregister_config_boilerplate` | MRO/config cleanup recipes exist for their exact AutoRegister declarations. |
| `enum_keyed_derived_map_facade` | A narrow enum map/query descent operation exists. |
| collector boilerplate, declarative detector classes, direct renderers | Specialized collector/class-family recipes exist; these are not generic UI decomposition recipes. |

The operation registry was introspected with the current checkout. The
relevant typed fields were:

```text
move_symbols_to_module: target rationale destination_path symbol_qualnames
relocate_symbols_to_module: target rationale destination_path symbol_qualnames
relocate_symbols_to_new_module: target rationale destination_path symbol_qualnames destination_source
move_symbol_closure_to_module: target rationale destination_path root_symbol_qualnames maximum_moved_symbol_count
extract_symbols_to_new_module: target rationale destination_path symbol_qualnames destination_source
extract_symbol_closure_to_new_module: target rationale destination_path root_symbol_qualnames maximum_moved_symbol_count destination_source
factor_exact_dataclass_field_authority: target rationale base_name evidence_field_name
promote_exact_dataclass_fields_to_existing_authority: target rationale evidence_field_name
factor_exact_method_role: target rationale base_name
promote_exact_leaf_methods_to_ancestor: target rationale
factor_parallel_mirrored_leaf_family: target rationale
promote_class_members_to_ancestor: target rationale destination member_names
project_function_parameter: target rationale projection_source attribute_path parameter_name
project_function_local: target rationale projection_source attribute_path local_name
collapse_closed_parameter_conveyor: target rationale
collapse_declared_carrier_expansion: target rationale
descend_type_keyed_behavior_projection: target rationale supported_execution
descend_enum_keyed_derived_map_facade: target rationale
derive_enum_subset: target rationale projection_target
derive_dataclass_payload_projection: target rationale projection_target
derive_dataclass_field_name_collection_projection: target rationale projection_target
derive_dataclass_key_value_sequence_projection: target rationale projection_target
derive_dataclass_constructor_projection: target rationale projection_target
```

The CLI supports plan validation/composition, source selectors, preflight,
simulation, projected-finding continuation, and bounded goal exploration:

```text
--codemod-plan --codemod-validate-plan --codemod-compose-plans
--codemod-compose-sequence --codemod-synthesize-plan
--codemod-synthesize-class-plan --codemod-plan-out
--codemod-source-index --codemod-resolve-selector --codemod-target-source
--codemod-preflight --codemod-simulate --codemod-project-findings
--codemod-refactor-goal --codemod-goal-max-stages
--codemod-goal-max-states --codemod-goal-max-branches --codemod-apply
```

All target probes used `--scan-budget-seconds 60`, omitted `--include-tests`,
and used an explicit OpenHCS `--context-root` with
`--no-auto-context-root`. A context root is needed for repository import and
consumer derivation; declaring only a file can make the proof partial or fail
context admission.

The recorded chained-plan example was also exercised without scanning or
editing a checkout:

```bash
./.venv/bin/python docs/examples/call_binding_extraction.py \
  > /tmp/nra_call_binding_plan.json
./.venv/bin/nominal-refactor-advisor \
  --codemod-plan /tmp/nra_call_binding_plan.json \
  --codemod-validate-plan \
  > /tmp/nra_call_binding_normalized.json
./.venv/bin/nominal-refactor-advisor \
  --codemod-compose-sequence /tmp/nra_call_binding_plan.json \
  /tmp/nra_call_binding_plan.json \
  > /tmp/nra_call_binding_composed.json
```

All three commands exited 0. Validation produced two stages named
`stage-1-extract_symbol_closure_to_new_module` and
`stage-2-extract_symbol_closure_to_new_module`; composing the same sequence
twice produced four stages. This validates JSON round-trip and ordered
projection mechanics, not that the example is applicable to OpenHCS.

## Confirmed OpenHCS dry runs

### UI action-model extraction

This is the most directly relevant positive probe. The source already has a
small generic-looking action dispatch service, and its Qt/widget consumers
refer to the route model. The exact plan is preserved beside this document as
`nra_widget_action_models_extraction.json`; the probe used the identical NRA
scratch copy `.codex-temp/openhcs_widget_action_models_extraction.json`:

```json
{
  "recipes": [
    {
      "recipe_id": "openhcs-widget-action-models-extraction-probe",
      "operations": [
        {
          "operation": "extract_symbol_closure_to_new_module",
          "file_path": "openhcs/pyqt_gui/widgets/shared/services/widget_action_dispatch.py",
          "root_symbol_qualnames": [
            "WidgetActionDispatchResult",
            "WidgetActionRoute"
          ],
          "maximum_moved_symbol_count": 8,
          "destination_path": "openhcs/pyqt_gui/widgets/shared/services/widget_action_models.py"
        }
      ]
    }
  ]
}
```

The exact bounded commands were:

```bash
./.venv/bin/nominal-refactor-advisor \
  /home/ts/code/projects/openhcs/openhcs/pyqt_gui/widgets/shared/services/widget_action_dispatch.py \
  --context-root /home/ts/code/projects/openhcs \
  --no-auto-context-root --scan-budget-seconds 60 \
  --codemod-plan .codex-temp/openhcs_widget_action_models_extraction.json \
  --codemod-preflight --json \
  > /tmp/nra_openhcs_widget_action_preflight.json

./.venv/bin/nominal-refactor-advisor \
  /home/ts/code/projects/openhcs/openhcs/pyqt_gui/widgets/shared/services/widget_action_dispatch.py \
  --context-root /home/ts/code/projects/openhcs \
  --no-auto-context-root --scan-budget-seconds 60 \
  --codemod-plan .codex-temp/openhcs_widget_action_models_extraction.json \
  --codemod-simulate --json \
  > /tmp/nra_openhcs_widget_action_simulate.json
```

Both commands completed with exit 0. Preflight reported:

```text
is_clean=True, report_count=1, preflight_failed=False
status=passed, message="Module symbol move dependency closure is clean"
requested=['WidgetActionDispatchResult', 'WidgetActionRoute']
moved=['_ActionT', '_WidgetT', 'WidgetActionSyncCallable',
       'WidgetActionAsyncCallable', 'WidgetActionCallable',
       'AsyncActionRunner', 'WidgetActionDispatchResult', 'WidgetActionRoute']
derived=['_ActionT', '_WidgetT', 'WidgetActionSyncCallable',
         'WidgetActionAsyncCallable', 'WidgetActionCallable', 'AsyncActionRunner']
imports=['Awaitable', 'Callable', 'Enum', 'Generic', 'TypeVar',
         'dataclass', 'inspect']
unresolved=[], ambiguous=[], annotation_mode=stringized -> stringized,
annotation_evaluation_is_preserved=True
```

Simulation reported `applied=False`, `applied_rewrite_count=5`,
`parse_validation.backend=ast_span`, and `parse_valid=True`. The projected
changed paths were exactly:

```text
openhcs/agent/ui_bridge_actions.py
openhcs/pyqt_gui/widgets/pipeline_editor.py
openhcs/pyqt_gui/widgets/plate_manager.py
openhcs/pyqt_gui/widgets/shared/services/widget_action_dispatch.py
openhcs/pyqt_gui/widgets/shared/services/widget_action_models.py (new)
```

The diff moves the two route/result classes plus their six source-local typing
aliases into `widget_action_models.py`, imports the route model into the two
widgets, moves the `TYPE_CHECKING` callable alias in `agent/ui_bridge_actions`,
and leaves `dispatch_widget_action` in its original service module. No
destination file was created in the real worktree:

```text
test ! -e .../widget_action_models.py  # exit 0
git status --short -- <all five paths>  # no output
```

This confirms useful NRA leverage for a small, closed UI-service module split:
closure discovery, import aliases, guarded imports, consumer rewrites, new
module creation, and parse validation. It does not prove Qt signal/lifecycle,
async scheduling, widget behavior, or that the service belongs in a different
package. Those require the UI acceptance gates below.

### Runtime artifact carrier extraction

As a second positive module-boundary **mechanics probe**, the exact same
operation was run
for the typed runtime carrier `RuntimeArtifactLocation` in
`openhcs/core/runtime_stores.py`, with destination
`openhcs/core/runtime_artifact_location.py`. The plan is preserved beside this
document as `nra_runtime_artifact_location_extraction.json`; the probe used
the identical NRA scratch copy `.codex-temp/openhcs_runtime_location_extraction.json`:

```json
{
  "recipes": [{
    "recipe_id": "openhcs-runtime-location-extraction-probe",
    "operations": [{
      "operation": "extract_symbol_closure_to_new_module",
      "file_path": "openhcs/core/runtime_stores.py",
      "root_symbol_qualnames": ["RuntimeArtifactLocation"],
      "maximum_moved_symbol_count": 4,
      "destination_path": "openhcs/core/runtime_artifact_location.py"
    }]
  }]
}
```

Preflight completed with `is_clean=True`, one passed report, one requested and
one moved symbol, no derived/source-local dependencies, imports `Any`,
`Mapping`, and `dataclass`, and preserved `stringized` annotation semantics.
Simulation completed with `applied=False`, `applied_rewrite_count=7`, and
`ast_span` `parse_valid=True`. It projected the new module, the source
re-export, and four runtime/interop consumer import updates. The destination
was absent and the five relevant pre-existing source files had no new git
changes. Again, this is only a source/import proof, not runtime artifact
equivalence. It is not the recommended first OpenHCS refactor: the carrier
still owns a `backend: str` and `to_dict()` transport projection, so putting it
in a smaller file does not remove that semantic debt. Review generated relative
imports, persisted class paths/`__module__` compatibility, pickle/spawn
behavior, and serialization before considering this kind of move.

## What each transformation can and cannot do

### Module moves and imports

`extract_symbol_closure_to_new_module` and
`relocate_symbols_to_new_module` are the strongest inspected module-move
operations. The positive probes exercised the extracting/preserving form;
relocation was not run here. The closure operation derives transitive movable declarations, external imports,
annotation evaluation policy, source re-exports, repository-local consumer
imports, and a destination revision contract. It fails on unresolved or
ambiguous dependencies, non-movable declarations, destination collisions,
annotation-policy changes, and a closure over the explicit maximum symbol
count. The preserving form leaves a same-name source import; relocating the
symbol removes the old source binding and is stricter about remaining source
references. Explicit symbol moves do not infer a closure.

The positive probes show that this is suitable for already bounded OpenHCS
services/carriers. It is not a package extraction oracle: the context root
must contain the complete consumer universe, and dynamic imports, generated
source, runtime plugin loading, string references, and external behavior are
outside the proof. The runtime probe generated package-relative imports in the
source and nested consumers (for example `.runtime_artifact_location`,
`..runtime_artifact_location`, and `....core.runtime_artifact_location`), while
the UI probe used absolute package imports. Review import style/lint and
canonical module identity, not just parse validity.

### Parameter promotion and carrier collapse

`project_function_parameter` and `project_function_local` are lexical
rewrites. They project reads through an authored access path while rejecting
rebinding/capture hazards; they do not change signatures or callers for the
user. `replace_function_signature` and `replace_declared_call_arguments` are
separate typed operations, with exact declaration/call selection and authored
expressions. NRA does not infer a new component carrier merely because several
parameters look similar.

`collapse_closed_parameter_conveyor` and
`collapse_declared_carrier_expansion` can collapse a complete, closed,
declaration-typed product flow into an existing nominal authority. The source
proof requires complete/injective mappings, dominating carriers, a closed call
family, no escaping/rebinding/mutation/open aliases, a closed public boundary,
and positive measured compression. `replace_fields_with_carrier` likewise
requires explicit field projections and an authored carrier field declaration.
These are candidates only after the OpenHCS authority and all consumers have
been made typed; they are not a shortcut for removing `AllComponents` members.

### Hierarchy, MRO, and multiple inheritance

The following operations are real but intentionally narrow:

* `factor_exact_method_role` creates one generated role authority containing
  the exact shared methods and adds it as a base to a source-proved cohort,
  then removes those duplicated methods from the participants. Method bodies
  must be receiver-closed and headers/MRO must be lossless.
* `promote_exact_leaf_methods_to_ancestor` moves exact methods into an already
  existing common authority and requires strict MRO ownership checks.
* `promote_class_members_to_ancestor` moves selected direct members only when
  source/destination are same-file actual ancestor classes and all collision,
  comments, name-mangling, local-reference, and descendant MRO hazards pass.
* `factor_parallel_mirrored_leaf_family` requires at least two AutoRegister
  roots and a complete parallel leaf cohort; its role product has a minimum of
  three roles and exact shared method sources. It is not an arbitrary “make a
  mixin” operation.
* Direct base replacement and redundant/intermediate authority collapse exist
  for declared class relationships, but they do not prove behavioral
  equivalence of arbitrary Python multiple inheritance.

Consequently, NRA can assist a declaration-owned ABC/MRO/MI refactor after
OpenHCS has established the exact family. It cannot discover a safe generic
processing hierarchy from a large `QWidget`, infer cooperative `super()`
semantics, or decide whether a new base belongs to the application or to
`pyqt-reactive`.

### Enum and member-consumer factoring

`descend_enum_keyed_derived_map_facade` handles one exact shape: a co-located
enum and map-owner classmethod returning `dict[Enum, Value]`, a generated
reverse query over `.items()`, and direct map/key consumers. It inserts an enum
property, moves the reverse query, rewrites direct consumers, and removes the
facade only after strict binding, annotation, and consumer checks. It does not
factor arbitrary enum/member uses or generate a replacement component enum.

`derive_enum_subset` is source-derived and exhaustive: it adds a classmethod to
an existing enum authority and rewrites one proven mirrored literal subset to
call that authority. The operation requires a real enum authority and exact
mirror projection. The dataclass projection operations similarly derive
exhaustive payload/field-name/key-value/constructor projections from an
existing dataclass authority. They do not authorize manually maintained
stringly registries.

`descend_type_keyed_behavior_projection` is also specialized. It requires an
AutoRegister family, a declared `ClassVar[type[Target]]` root contract,
injective projection leaves, an exact MRO registry lookup shape, and
receiver-closed behavior. Native execution names such as `classmethod`, `type`,
and `mro_registry_value` must be explicitly admitted. This is not evidence
that OpenHCS `AllComponents` or streaming enums match the shape.

The current detector implementation also explains one important negative
result: `_unique_direct_enum_classes` in `detectors/_systemic.py` and
`_enum_member_names_by_class` in `detectors/_base.py` reason about top-level
`class X(Enum)` declarations. OpenHCS `AllComponents` is dynamically built by
`Enum(...)` in `constants/constants.py:_create_enums()` (called by the
configuration bootstrap); a zero enum
finding in a focused scan therefore does not prove membership blindness. Any
future detector/recipe needs declaration-derived family recovery for that
factory, followed by source and runtime tests, rather than an OpenHCS-specific
name detector or a mirrored registry.

The literal-dispatch operation currently rewrites module functions only. A
method target is rejected until the closed-axis authority is extracted or
owned at the class boundary. This matters for compiler/UI methods: a numeric or
string switch finding alone is not a proof of safe polymorphism.

## Recommended staged use for OpenHCS

These are planning stages, not an instruction to apply them now.

### Stage 0: characterize the declaration boundary

First run the alternate-component-family, fresh-process, persistence, and
spawn-worker experiments in the domain-extraction README. Keep
`ComponentConfiguration`, `AllComponents`, `ObjectState`, compiler plans,
runtime stores, and existing ABC/registration/MRO contracts as the authority.
NRA cannot generate or validate the alternate `get_openhcs_config()` enum
family, process identity, or UI behavior. Its detector output must not be used
as a replacement for these tests.

### Stage 1: typed coordinate/source projection

Audit `core/source_projection.py:55-96` and `core/config.py:255-538` before
authoring a codemod. `OpenHCSPlaneAddress` treats `WELL` specially and the
display configuration names five modes individually; this is a semantic
boundary, not a mechanical rename. If exact repeated dataclass fields are
proven, use the dataclass field-authority operation. If an existing typed
carrier already owns the fields, use the promote operation. Otherwise author a
declaration change and tests first. Do not use a stringly member list or ask
NRA to infer it.

### Stage 2: compiler and downstream consumers

The parent bounded scan found one semantic boundary in the focused compiler
scope (`MaterializationBackend` external-enum-case recovery at
`PipelineCompiler._configure_input_conversion_if_needed` and
`MaterializationFlagPlanner._resolve_materialization_backend`), but its report
contained no executable plans. This is an audit lead, not a codemod proof.
Reprove those declarations and their downstream consumers against the current
source before choosing `project_function_parameter`, explicit call-argument
rewrites, or a carrier collapse. Follow grouping, source-universe, function
patterns, sequential state, artifact routing, worker assignment, materializer,
and aggregation together. A static candidate must not be treated as execution
equivalence.

`project_function_parameter`, explicit declared-call argument rewrites, and
closed-carrier collapse are possible only after the typed source/coordinate
authority from Stage 1 is in place. NRA will not turn this finding into a
generic compiler by itself.

### Stage 3: UI and display surfaces

After the component/source and compiler boundaries are behaviorally established,
the positive `widget_action_models` simulation is a mechanics example for a
possible ownership migration; it is not inherently the next refactor. Keep Qt
ownership and signal/lifecycle behavior in the owning UI layer; move only
closed route/result declarations when the source and UI architecture review
identifies that boundary. Use one `CodemodPlanDocument` for edits that must
resolve against one source snapshot. If a later operation targets the newly
created module, compose an ordered `CodemodPlanSequence`; each stage is
resolved against the previous projected source and reindexed at the boundary.
Review the five-file projected diff, then run fresh-process UI/MCP interaction
and async dispatch tests before any apply.

The existing generic foundations (`pyqt-reactive` forms/layout/manager/table
infrastructure and OpenHCS adapters) should remain declaration-owned. A
successful module move does not by itself justify moving the mechanism to a
different package.

### Stage 4: process, persistence, and runtime carriers

First prove selected-schema startup, spawn/restart, serialization, and
artifact-provenance behavior. The `RuntimeArtifactLocation` simulation
demonstrates closure imports, source re-export, and discovered consumer imports
as mechanics. It is not a first refactor: its `backend: str` and `to_dict()`
transport projection still need a semantic owner review. Preserve
`RuntimeValueStore`, `ArtifactKey`, and runtime declaration ownership; do not
replace them with a second registry. Review generated relative imports,
persisted class paths/`__module__`, pickle/spawn behavior, and serialization
before considering this kind of move.

### Cross-cutting exact class-family/MI operations

At whichever master stage owns the typed authority (coordinate/source,
compiler, or UI), consider the exact method/field authority or MRO operations
only after a complete family is declared. Require the operation's source proof
and then run independent `ABC`/MRO/MI tests, including registration order and
descendant lookup. Do not factor a large widget or compiler class because it
has similarly named methods.

### Cross-cutting enum/projection operations

At whichever master stage owns the enum or dataclass declaration, use enum/map
descent, enum subset derivation, or dataclass projections only when the exact
owner, exhaustive projection, and consumer shape pass source reproof.
`AllComponents`, `VariableComponents`, `GroupBy`, and
`StreamingComponents` remain declarations selected by the application's
configuration; no detector finding licenses a parallel mirrored registry.

### Stage 5: package extraction and cleanup

After the owning component, compiler, UI, and process boundaries pass their
master-plan gates, use closure moves for coherent modules, then run exact
projected-finding continuation and import direction checks. Apply only with
revision-checked batches after review. Deletions, aliases, compatibility
imports, and generated-code changes should be separately staged and tested;
they are not implied by a successful extraction simulation.

## Planning, proof, and equivalence gates

NRA plan documents represent one source snapshot. A plan sequence intentionally
creates state boundaries, so later selectors can resolve declarations created by
earlier stages. Composition checks both operation orders and marks a pair
unproved when source-order composition differs. The workflow trajectory runner
explores compatible batches, rescans exact projected states, rejects new
finding debt/guard violations, and calls a trajectory `proved` only when the
bounded search is complete, has no obstacles, and has exactly one terminal
state. A timeout, partial projected scan, multiple terminals, or no terminal is
incomplete/ambiguous—not clean.

The useful NRA gates for each proposed batch are:

1. source selector resolves exactly the intended declaration(s);
2. operation preflight passes dependency, binding, annotation, MRO, and
   collision checks;
3. simulation has a reviewed unified diff and `ast_span` parse validation;
4. projected source is rescanned with a complete admitted context root;
5. terminal architecture guards and finding debt are clean;
6. revision-checked apply is performed only after the independent gates pass.

NRA does not execute OpenHCS, compare numerical arrays/artifacts, validate
Qt signal lifetimes, prove `ObjectState` provenance/undo, prove process
spawn/pickle identity, or validate Napari/Fiji/MCP transport. OpenHCS must add
those gates separately:

* alternate membership/order and unequal-cardinality declaration tests in a
  fresh process;
* compiler/runtime equivalence for grouping, source universe, function
  patterns, sequential state, materialization, artifacts, and worker assignment;
* saved code/config/session compatibility and versioned legacy decoding at the
  input boundary;
* real UI/MCP interactions with generated forms, nested defaults, resets,
  code round trips, compile/run, and viewer handoff;
* spawn/restart/persistence identity and streaming client capability checks;
* cold/warm compile, UI construction, spawn, and representative execution
  performance comparisons.

## Bounded-run limits and current status

The full OpenHCS package contains 675 Python paths. Parent-agent scans of the
full package, with tests excluded and a 60-second bound, ended
`deadline_incomplete` during `parse_python_module`; this is not a clean result.
Narrow explicit-context scans completed quickly (3.859 s, 4.228 s, and 7.466 s
for the reported focused scopes), running all 79 detectors. The recorded
reports were `/var/tmp/openhcs-domain-audit-kAEAj/nra-component-context.json`,
`nra-consumer-boundary.json`, and `nra-compiler-boundary.json`. The first two
focused scopes had zero findings; the compiler scope had the one semantic
boundary described above and no synthesized plans. Those focused results are
complete only for their admitted paths/context and do not prove package-wide
absence.

The positive module simulations also used the 60-second bound and completed,
but their projected states are static source states. NRA cost scales with AST
parsing, declaration indexes, MRO/import indexes, repository consumers, and
projected rescans; a broad package context can therefore hit the deadline even
when a narrow closure is clean. Keep candidate authoring narrow, then rerun a
complete context proof before claiming coverage.

The scratch closure probe used `.codex-temp/nra_probe_source.py` and
`.codex-temp/nra_probe_plan.json` (created with `apply_patch`) and was run as:

```bash
./.venv/bin/nominal-refactor-advisor .codex-temp \
  --codemod-plan .codex-temp/nra_probe_plan.json \
  --codemod-preflight --json > /tmp/nra_probe_preflight.json
./.venv/bin/nominal-refactor-advisor .codex-temp \
  --codemod-plan .codex-temp/nra_probe_plan.json \
  --codemod-simulate --json > /tmp/nra_probe_sim.json
./.venv/bin/nominal-refactor-advisor .codex-temp --no-cache \
  --parse-workers 1 --analysis-workers 1 --scan-budget-seconds 60 \
  --codemod-synthesize-plan --codemod-simulate --json \
  > /tmp/nra_synth_probe_60.json
./.venv/bin/nominal-refactor-advisor .codex-temp --no-cache \
  --parse-workers 1 --analysis-workers 1 --scan-budget-seconds 60 \
  --codemod-refactor-goal semantic_carrier \
  --codemod-goal-max-stages 2 --codemod-goal-max-states 8 \
  --codemod-goal-max-branches 8 --json > /tmp/nra_goal_probe.json
```

The first two commands exited 0 with clean preflight and a parse-valid
`extract_symbol_closure_to_new_module` diff; simulation reported
`applied=false` and did not create its destination. Synthesis exited 0 with
`records=0`, `candidates=0`, `rejected=0`, `unsupported=0`, and no planning
horizon. The bounded goal exited 0 with `stop_reason=achieved`,
`status=proved`, `visited=1`, `transitions=0`, and `terminals=1`. These results
validate CLI mechanics only, not OpenHCS architecture.

A focused NRA regression command (tests are not production evidence) produced:

```bash
./.venv/bin/pytest -q \
  tests/test_small_method_factoring_plans.py \
  tests/test_exact_dataclass_field_authority_operation.py \
  tests/test_existing_dataclass_field_authority_operation.py \
  tests/test_enum_keyed_query.py \
  tests/test_type_keyed_native_contract.py --maxfail=1
```

Result: `46 passed in 4.29s`. Adding
`tests/test_class_member_move_operation.py` to the focused command reached 55
passes and one failure in
`test_promotes_selected_members_to_existing_ancestor_as_one_operation`: the
current dirty native-proof code failed closed with
`CodemodOperationPreflightError` (`Object capture remains open:
unproved_execution_effects` / `unadmitted_import`). This is a limitation of
the current NRA checkout's proof gate, not evidence that class-member
promotion is behaviorally unsafe or safe in OpenHCS.

## Bottom line

NRA currently provides high-value, source-reproved leverage for bounded module
extraction and exact declaration-owned transformations. The two OpenHCS
simulations prove that it can derive closure/import/re-export edits for a small
UI service model and a typed runtime carrier without mutating the worktree.
It does not provide automatic domain extraction, alternate-schema generation,
Qt/runtime/process equivalence, or proof from detector findings alone. Treat
the positive batches as candidate mechanical stages after the declaration and
behavior gates pass, and keep AllComponents/ABC/MRO/MI semantics on their
typed declaration owners rather than introducing stringly mirrored registries.
