# Measurement declaration checkpoint (#133, #204)

Implementation owner: Zeno. Integration owner: OpenHCS issue-batch coordinator.
Worktree: `/home/ts/wt/openhcs-exact-label-selection-20260929`.
Base: `openhcsdev/main` at `32d070c26` (merged PR255), integrated normally through
`85d8b2ae7`. The preceding checkpoint merged `589c33a12` through `684e4bbd3`,
and `de23449a4` through `21c15ad41` before that.
The output-policy checkpoint used `283b21275`.
The earlier checkpoint used `98d9b9d23`; the runtime checkpoint integrates new
main through normal merge `9f5d444515`. No parent/main-worktree edits, rebases,
resets, installed-source edits, or gitlink changes.

Closes #133. References #204; its paired-channel and actual GUI acceptance remain
open. This is a source-verified draft, not an installed/live-readiness claim.

## Current-main subject journey: prepared; refreshed live gate pending

The newly reported frozen-author failure is precisely #133: a typed `PURE_3D`
measurement output can carry a feature owner and source lineage without declaring
what it measures. The original attempt remains untouched. No author source,
science, pixels, parameters or references were needed or inspected for this
continuation; no replay or author coaching occurred.

The existing synthetic integration journey declares its own `CountFeature`
and nominal feature owner, CSV materialization and `MainFlowStackOutputSpec`
for both row variants. The existing `MainFlowArtifactContractProvider` binds
their stack/group lineage to the actual current image **input**. The corrected
declaration is a `dataclasses.replace` of the invalid
one, adding **only** `ImageMeasurementSubjectRelation(CountedImage.ref())`.
Both variants render/parse through `PipelineDocumentAuthority`; the test asserts
the reconstructed feature owner and real provider's input-qualified scope before
the headless compile boundary; the subject remains the exact image **output**
ref. The invalid callable still raises if entered. The valid case
uses the real compiler and orchestrator and checks both image and measurement
outputs and four counted synthetic pixels. These revised integration assertions
are prepared, **not yet rerun** at current main.

### Parent review: output-qualified lineage fixture repaired

The parent correctly identified an independent invalid declaration in checkpoint
`94595f271`: generic `ArtifactSpec.output` with
`SourceStackLineageSourceRelation(CountedImage output ref)` does not make a legal
group-scope input. The earlier four output-policy probes did not exercise that
boundary. Their passing result was not evidence that this valid-subject variant
could reach execution or CSV. No such readiness is claimed.

A bounded source-only probe using the actual `CallableContract`,
`NormalizedFunctionItem`, `ArtifactDeclarationStepContext` and
`MainFlowArtifactContractProvider` reproduced the failure:
`Callable 'count' output group-scope relations reference undeclared inputs`
with the exact `CountedImage` OUTPUT ref. Switching both variants to the existing
`MainFlowStackOutputSpec` yields three observed outcomes in the final probe:

1. The original generic output-qualified lineage still fails the real
   `CallableContract.group_scope_inputs` boundary.
2. The corrected input-qualified lineage passes that boundary while its missing
   measurement subject still fails output-owner validation.
3. Adding only `ImageMeasurementSubjectRelation(CountedImage.ref())` passes both
   boundaries and retains the exact OUTPUT subject separately from INPUT lineage.

The first probe confirmed the red witness, then used a nonexistent
`ArtifactSpec.measurement_subject()` test API. That probe error was corrected to
`MeasurementsArtifactType.require_output_subject`; it was not a runtime defect.
The final probe passed in 0.58 seconds without invoking the callable. It uses
minimal metadata, not CSV/row/native execution, and is explicitly source-contract
evidence. The actual integration fixture retains its feature owner, CSV options,
roundtrip and compile/execute assertions for the released-slot gate.

NRA/refactor-audit finding: IDEN-1 separates invocation source/group ownership
from measurement subject; IMPL-4 reuses the output declaration's existing binding
hook instead of restoring consumer inference. Only the journey fixture and this
receipt are edited. No guard relaxation, new owner/registry, parent PR255 file
edit, source-binding edit, installed-root use or production-code change occurred.

Actual lightweight checks at this checkpoint:

- All nine imported package paths resolve inside this worktree, using the required
  existing interpreter and eight recorded submodule `src` paths. PolyStore
  `1209068f5` and ZMQRuntime `0f9e840a9` were synchronized from existing local Git
  objects only: no dependency download, donor source edit or installation change.
- Four direct, real output-policy checks passed: native-return and ordinary
  adapter-recorded owners each reject a missing subject despite the declared
  feature owner and source lineage, then accept the subject-only correction.
  This is owner-hook behavior evidence, **not** compile/execution/CSV evidence.
- AST parse and in-memory Python compilation passed for all **24 changed Python
  files** against current main; `git diff --check` passed. Focused guards verify
  common kind validation precedes payload-policy validation with no exemption
  branch, and the removed `manages_artifact_outputs` has no source/test callers.
- The original exact two-producer paired execution remains enabled, together
  with omitted-selector ambiguity/single-producer cases and real unscoped and
  asymmetric `RuntimeArtifactInput` regressions. No assertion, channel check,
  selector, source policy or production owner was weakened in this continuation.

NRA/refactor-audit coverage is **focused source/caller/AST inspection**, not a
complete NRA scan or native proof. Actual owner evidence: IMPL-1/4/10 puts output
invariants on the artifact kind and native/recorded obligations on their declared
policy; the compiler calls `ArtifactPlanKeySelector` and runtime reuses
`MeasurementsArtifactType.require_output_subject`. IDEN-1 keeps feature ownership,
source lineage and measurement subject independent; schema/CSV is not a subject.
MEMB-1/2 and IDEN-5 derive the catalog selector from the existing binding's
`require_parameter_name`, with no copied roster/store. IDEN-7/BOUND-2 keeps exact
producer/group selection before typed contextual compatibility; empty/asymmetric
additional constraints do not alter global source-image matching semantics.
The retained new-kind experiment declares one new artifact kind, requires
**zero compiler/consumer changes**, and covers all three output policies,
independent input management and both contract/compile boundaries. Its prior
20-case passing evidence, including legitimate heterogeneous CP ownership, is
historical below, not relabeled as a current-main rerun.

The parent explicitly granted the finite source-live slot after freezing and
closing the original blind runtime and its finite installed acceptance attempt.
The worker acquired `validation.lock` nonblocking for the admission check.
It exited **78**: available RAM **14.08 GiB** exceeds the initial 11 GiB floor,
but `/home` available disk **19.7195 GiB** is below the required 20 GiB floor.
The general resource guard's rounded 20.0 GiB is not an admission proof.
No build/test/MCP/JVM/GUI process started; the admission process exited and
released its lock. Previously recorded worker-owned disposable scratch is
already empty (4 KiB directory), so no other owner's artifacts were removed.

Remaining named dependency: parent resource admission needs at least 0.3 GiB
additional available disk plus build margin. This worktree still lacks the
current-main `_tabular_native` extension (`find_spec` returns `None`). No native
build, environment startup, installation or managed-skill change occurred.
After admission, validate the two subject variants first, then the unweakened full
six-case declaration journey and focused paired-source cases. Installed/live
verification and merging remain with the parent; optional CI or broader paired
research is not a prerequisite for shipping the reviewed #133 checkpoint.
Parent owns the separate #254 payload ABI/PURE_2D follow-up, including only
`FunctionChainInvocationExecutor.main_flow_call_argument` in the shared runtime
file. This worker's measurement strategy/input-loader scope does not collide;
no cherry-pick of that unpublished follow-up or installed-root validation occurs.

## Frozen-harness compile incident: triaged, regression retained

The original server5793 request `4f8e1d55-07f0-4bde-9f37-d24c0ea398f9`
failed at 20:24:35 UTC with `MeasureCells_4_measurements` group `"1"` having no
declared group-scope source. The original saved technical request's source hash
matches the server's `5fb62ebed47d`: it produces exact `Cells` under channel group
`"2"`, but explicitly dispatches its size/shape measurement under group `"1"`.
The real module already declares the exact labels-owned group lineage and object
subject. This is an invalid authored grouping, **not missing backend projection**.

The new real-declaration/planner regression preserves that failure and proves
matching-group and declaration-derived controls compile: **3 passed**. Combined
with the output-policy review cases, **23 passed** in 1.87 seconds after current
main integration. No production relaxation, frozen replay or installation change
was made. Original request/variant identities, owner trace, pattern IDs and
acceptance boundaries are preserved in
`docs/plans/measurement_group_scope_triage_20260929.md`. This technical case stays
on #204/PR205; it does not resolve the separate paired runtime/live gate.

## Implemented

- Measurement output validation belongs to `MeasurementsArtifactType`. Compilation
  requires a subject relation before invoking the callable. Schema-bearing rows and
  CSV materialization do not imply a measurement subject.
- Compile and runtime resolve subjects through the original relation owners. The
  error identifies the output and explains image, object, and artifact relations.
- The finalized callable contract projects its declared `artifact_output_policy`.
  Every policy runs the artifact kind's common declaration invariants, then its
  native-return or adapter-recorded payload obligation. The old blanket exemption
  and `manages_artifact_outputs` field are deleted, with all callers cut over.
  Input management remains an independent capability. CellProfiler's policy
  requires the existing module measurement owner rather than a table-wide subject;
  its original row policy and recording boundary still validate actual subjects.
- CellProfiler catalog bindings project `require_parameter_name()`, not the optional
  raw `parameter_name`. The existing `select_object_sets_to_measure` selector is
  discoverable separately from the runtime-owned scalar `labels` parameter.
- Catalog guidance explains exact-name tuples and consumed compile-time selectors.
  No selector registry, artifact store, fallback, or ambiguity relaxation was added.
- The secondary module already declares `InputGroupLineageSourceRelation` from its
  primary-label input to its image input. Runtime input matching now projects typed
  scope identities using that exact relation's source bindings and the existing
  `SourceImageSetIdentityPolicy` / `SourceImageSetIdentityCompatibility` owners.
  This permits declared paired-channel context without a global channel exception.
  Missing relations or unrelated visible bindings retain exact coordinate checks.
- All three production input constructors forward their existing compiled source
  binding plan: native callable loading, adapter record access, and binding requests.
  Producer address/group selection, stack-plane projection, and ambiguity checks
  remain authoritative; the old duplicate fixed-coordinate loops are deleted.

## Focused evidence

Using `/home/ts/code/projects/openhcs/.venv/bin/python` with this worktree and all
eight recorded submodule `src` directories on `PYTHONPATH`; all nine imported
package paths were verified inside this worktree. Submodules were initialized to
their recorded gitlinks without installed-source changes.

### Architectural review follow-through

Review: https://github.com/OpenHCSDev/openhcs/pull/205#issuecomment-5897282604.
The review correctly identified a consumer-owned exemption in the previous
checkpoint. Its earlier audit claim below was too strong: skipping every kind
hook was not an adequate expression of CP's heterogeneous table obligation.

- Red witness at the pre-fix body: the new materialization-bearing output kind
  produced **4 failed, 4 passed**, 1.65 seconds. All four adapter-recorded cases
  silently bypassed its invariant; native-return cases rejected the declaration.
  Contract and compile boundaries, with input management both on and off, expose
  the same defect. Corrected declarations also compile without executing a callable.
- `tests/unit/test_artifact_output_ownership.py` now exercises the same new kind
  under native, generic adapter-recorded and CP-recorded policies without any
  compiler/consumer edit for that kind. It also checks single-subject requirements,
  common conflicting-subject rejection, CP's required module row owner, and the
  nominal policy boundary. The real `CellProfilerInvocationContractProviderFactory`
  derives a primary module contract with its original measurement owner and no
  table-wide subject. Real `compile_function_pattern` admits that contract;
  replacing only its recording owner with native returns rejects it.
- Final output-policy file: **20 passed**. The preceding five-file run covering
  output policy, native artifact outputs, all runtime-store regressions, catalog
  friction and artifact identity reconstruction: **153 passed**, 4.95 seconds
  (17 policy cases before the final three nominal-boundary cases were added).
- `test_function_patterns.py` plus `test_function_step_execution_plan.py`:
  **80 passed** in the 95-case run including the then-15 policy cases. Four generic
  adapter measurement fixtures previously omitted subjects; they now declare valid
  artifact subjects while retaining their exact component/projection assertions.
- Three selected planner cases: **3 passed, 96 deselected**, 1.92 seconds.
  Exact managed group lineage and main-flow preservation retain their assertions.
- Existing `test_track_objects_record_builder_uses_nominal_image_table_ownership`:
  **1 passed, 393 deselected**, 5.08 seconds. The actual module row builder emits
  mixed image/object tracking rows with their declared per-row owners. This is
  provider-free record-building evidence, not complete pipeline/live execution.
- Existing adapter output runtime-context regression:
  **1 passed, 91 deselected**, 1.71 seconds. The separate adapter component-output
  chain regression also passes; no MCP/JVM/GUI process or environment was started.
- All checks use the required interpreter, worktree and recorded submodule paths.
  Latest guard: **11.5 GiB available RAM**, historical swap warning at 11.9 GiB.
  These are bounded source/unit checks, not a second heavy validation slot. No
  installed source, shared environment, skill, or frozen runtime was modified.

- Initial published checkpoint: 12 catalog/identity tests and 6 focused native
  subject tests passed.
- Full focused rerun: `pytest -q tests/unit/test_function_artifact_outputs.py
  tests/unit/agent/test_mcp_cellprofiler_function_contract_friction.py
  tests/unit/test_cellprofiler_artifact_identity_reconstruction.py
  tests/integration/test_measurement_declaration_journey.py -k 'not paired'`:
  **85 passed, 1 deselected**, 9.33 seconds (80 unit, 5 real headless journey cases).
- The real `PipelineDocumentAuthority` and `FunctionStepDocumentAuthority`
  render/parse routes preserve `select_object_sets_to_measure=("Cells",)`.
  `InProcessCompileInspectionGateway.compile` selects exactly the secondary
  producer (source step 1) for runtime `labels`; authored selectors are consumed.
- The same-source two-producer journey then runs the real orchestrator and
  verifies the secondary label area is larger than the primary area, the returned
  measurement subject is `Cells`, and integrated DNA intensity includes the grown
  secondary region rather than just the four bright primary pixels. Feature
  retrieval uses the existing CellProfiler measurement dialect.
- The paired DNA/actin-channel case also passes roundtrip and compile, but its
  earlier continuous run failed at the secondary step's primary-label input.
  It remains an unweakened regression, deselected in that historical run;
  see the remaining acceptance section. No xfail or fallback was added.
- Omitted selection with two producers fails closed with the original useful
  ambiguity diagnostic; omitted selection with one producer compiles.
- Missing and conflicting native subjects fail before execution. The real
  headless compiler rejects schema-bearing `DataclassMeasurementColumnarRows`
  with CSV options but no subject. The corrected image-subject declaration
  compiles and executes, returning an image-owned table with four counted pixels.
- Runs used nonblocking batch validation `flock` and CPU-only mode. The resource
  guard most recently reported 14.7 GiB available RAM and a warning for historical
  11.5 GiB used swap. No broad suite, JVM, MCP server, or extra GUI was started.
  The final run completed and released the lock before Euler's H003 restart;
  no further heavy validation was started after the resource-priority instruction.

Runtime checkpoint after the explicit scope extension:

- `pytest -q tests/unit/test_runtime_value_store.py --tb=short`: **48 passed**,
  1.53 seconds, provider-free and without a JVM, GUI, or MCP server. New cases
  exercise paired-channel matching, both adapter consumers, conflicting fixed
  site/z/time coordinates, another well or exact producer path, missing source
  declarations, missing context relations, a relation to an unrelated source,
  an absent producer site plane, and unresolved multiple-record ambiguity.
- Replaying the published matching body on the same new fixture rejects channel
  1 versus 2; the new body selects its exact producer. This is provider-free
  reproduction of the precise owner fault, not complete paired execution.
- Attempting the complete six-case headless journey under nonblocking `flock -n
  -E 75` returned **75 (lock busy)**, without starting pytest. Euler's H003 slot
  remains reserved. Paired runtime acceptance is pending this run, not claimed
  from the 48 focused store checks. No deselection is planned for it.
- The resource guard reported 11.6 GiB available RAM; its warning was historical
  11.5 GiB used swap. Only lightweight source/unit checks proceeded.

Coordinator scope-preservation witness, followed through:

- Ordinary exact unscoped inputs and producer-only, consumer-only, shared-partial,
  and disjoint-partial fixed scopes were explicitly tested through
  `RuntimeArtifactInput.records`, not only through a predicate. They already
  passed because the earlier projection retained the exact axis key.
- A genuinely empty projected-context witness uses a context-carrying object-label
  artifact and an existing source declaration whose plane membership projects
  the axis key. The published candidate then reproduced **four failures**:
  unscoped, producer-only, consumer-only, and disjoint-partial inputs lost their
  exact address-matched record because `bool(shared_keys)` was false. This proves
  a focused runtime failure for the witness, not its prevalence in real pipelines.
- Artifact admission now derives shared additional constraints from the typed
  scope owners, compiled variable-axis projection, and declared image-set policy.
  No shared additional constraint is vacuously satisfied after producer/address/
  group selection. Otherwise the existing typed predicate checks their values.
  The artificial shared axis key was removed from this additional-context test.
- `SourceImageSetIdentityCompatibility` is **unchanged**. Each projected-context
  case asserts it still rejects identities with no shared evidence; exact artifact
  admission has a different, already-proven identity boundary. Wrong well and
  producer paths still fail before this additional-constraint check.
- `pytest -q tests/unit/test_runtime_value_store.py --tb=short`: **56 passed**,
  1.67 seconds in the final run including the exact-address negative assertions.
  Original conflicting spatial/time,
  exact producer/group, retained-plane, and ambiguity assertions still pass.
- Only `core/runtime_stores.py`, its typed scope owner, and their tests were
  modified for this witness. No source-binding owner, shared artifact declaration,
  CellProfiler adapter, or #214 diagnostic-output field was modified in this step.

## Essential anti-pattern audit: actual ownership evidence

This is a focused source/caller and AST audit against the current archived
refactor-audit pattern catalog, **not a complete NRA semantic/proof scan**. All
eleven changed production files in the earlier runtime checkpoint were parsed against its merged main: zero added
`match`, `isinstance`, `getattr`/`hasattr`, or 6+-term boolean-chain AST nodes.
That guard detects listed shapes, not every possible semantic ownership defect.

| Pattern IDs | Owner, projection, and new-case evidence |
| --- | --- |
| IMPL-1/2/3/4, MEMB-1/2 | The finalized compiler calls the selector's public validation contract. `ArtifactOutputPolicy` runs every kind's common hook, then the policy dispatches to the kind's native-return or adapter-recorded obligation. `MeasurementsArtifactType` owns common relation coherence and the native subject requirement; CP declares its distinct module-row-owner obligation. The new-kind materialization rule requires one declaration and zero compiler/consumer changes, and executes under all three owners. No kind/name roster or concrete-adapter switch was added. |
| IMPL-5/12/13, TIME-1/3 | `ArtifactSpecRelation.measurement_subject_for_output` resolves original relation-owned subjects once. The output-plan accessor, kind requirement, and native runtime all delegate; the former output-plan extraction body and runtime missing-subject body were deleted in place. The output-plan method remains a domain accessor, not an old reader or compatibility alias. |
| IDEN-1/2/5, BOUND-2/7, MEMB-3/4 | `SettingToKeywordBinding.require_parameter_name()` owns selector identity, separately from `runtime_parameter_name`. The only production `CellProfilerArtifactBindingSummary` constructor projects that owner; its selector field is now required. No selector store, guessed names, raw-row decoder, or attribute-name probe exists in the change. The catalog regression derives every registered binding and exercises new derived-name input and explicit-name output declarations without editing the projection. |
| IDEN-1/7, IMPL-4/10, IMPL-5/12 | Recording ownership no longer answers whether common compile invariants may run. The blanket early return and output flag were removed, not relocated; native/adapter policies have distinct kind-dispatched payload obligations. CP requires its already-declared `measurement_feature_owner`, leaving actual heterogeneous row validation with the original module row policy and `add_measurements`. Common conflicting-subject checks stay on the kind. The new-case matrix varies input management independently, and the real CP provider/admission plus mixed tracking-row builder pass. |
| AGENT-2/3/6/7, TIME-5/9 | No second mechanism, format converter, test-only production switch, or dormant feature was added. One pre-existing cardinality fixture received a valid artifact-level subject so its original missing-return assertion remains meaningful. The paired-channel failure is retained, not hidden by weaker expectations; publication proceeds with that exact acceptance gap stated. |
| IDEN-1/6/7, BOUND-2, MEMB-1/2/3, IMPL-5/12, TIME-1/3 | Exact compiled producer/address selection and contextual source compatibility answer different questions. `RuntimeArtifactInput` derives context membership from `edge.spec.source_context_sources()` and the referenced original source bindings, then delegates matching to the existing typed identity predicate. `RuntimeExecutionAxisScope` owns its typed-coordinate projection. No literal channel/site/z/time matching roster, new registry, global ignore flag, alternate reader, or copied predicate was added. All three constructors are migrated; two actual adapter consumers and fail-closed new cases execute. The replaced fixed-coordinate loops are gone. |
| IDEN-7, BOUND-2, IMPL-5 | Artifact admission asks whether an already-selected producer violates any shared additional coordinate constraint, not whether unknown plane identities prove correspondence. The four failing empty/asymmetric witnesses distinguish these questions. `ComponentSet.intersection`, scope-owned `source_components`, and policy-owned `identity_components()` derive the applicable constraint domain. No copied compatibility matcher or weakened global empty-identity semantics was introduced. |

Caller review covered the default invocation declaration provider (returns the
finalized `CallableContract`), every call to the new output-validation hook and
shared subject resolver, all production measurement-subject accessors, and the
catalog DTO constructor/consumers. Structural `extract_artifact_declarations`
still checks relation references without prematurely applying native runtime
requirements to partially reconstructed CellProfiler contracts. Real compile
inspection reaches the finalized validation boundary and fails before execution.

Review follow-through at `dd02a00f6` plus the latest normal main merge covered all
output-policy constructors, decorator calls, compiler hooks and four production
recording consumers. `rg` finds no remaining `manages_artifact_outputs` use in
production or tests; there is no compatibility alias. The nine production files
changed for this review were AST parsed: zero added `match`, attribute-name probes
or 6+-term boolean chains; one added `isinstance` is the nominal output-policy
declaration boundary, tested for invalid/abstract policies. This is focused
source/caller/new-case coverage, not complete NRA detector or native-proof coverage.

Runtime caller review also covered `records`, static/dynamic `all_records`,
`_records`, `_validate_selected_records`, `_axis_value`, `projected_values`,
`composed_value`, all three production `RuntimeArtifactInput` constructors, and
the existing secondary input relation declaration. Compiled group selection and
variable-component projection are unchanged: existing complete-producer-group
and transposed-stack tests still pass, while the new missing-site-plane test fails
closed. This checks this runtime surface; it is not a global provenance audit.

New-case runtime edit count: a context relation and a source declaration supply
membership, with zero changes to the matching consumer or a component roster.
Tests show a visible binding cannot substitute for a missing relation, and a
relation cannot borrow membership from an unrelated source. Partially scoped
identities continue using the existing compatibility predicate, not a new
equality algorithm.

New-case edit count: one owner declaration for a new setting binding, zero new
catalog/compiler branches; the registered/new-binding regression exercises this.
A new subject relation exposes its existing `measurement_subject()` capability;
both compile and runtime use it unchanged. A new output kind supplies its own
validation hook, with zero edits to the generic compiler consumer. The
duplicate-resolution removal is factoring; no pure file move is claimed.

## Remaining acceptance

- The original paired-channel journey failed **before measurement**, while
  secondary consumes `Nuclei`: the exact record has fixed channel 1 scope,
  but `RuntimeArtifactInput._matches_execution_scope` compares it with the
  secondary source's channel 2 scope and rejects it. Address, axis, and producer
  identity match. Reproduce with `pytest -q
  tests/integration/test_measurement_declaration_journey.py -k paired --tb=short`
  under the serialized validation lock after coordinator handoff. Zeno is the
  active runtime-fix owner under the explicit scope extension. The focused fix is
  present and store regressions pass, but complete paired execution remains
  unverified. No `core/source_bindings.py`, `core/source_binding_workspace.py`,
  source preparation, ROI, viewer, or #211 authorization method/test was modified.
- Scheduling: parent #151/#212 acceptance and installation are complete.
  Confucius now owns the heavy runtime lock and frozen installation. Zeno will run
  the full six-case headless journey only after an explicit serialized handoff.
  No race for fresh environments, GUI, JVM, or installed-baseline changes is authorized.
- Parent also owns the cold-inspection deletion in
  `InProcessCompileInspectionGateway`; Zeno does not edit that method or its
  catalog-initialization call. The pending continuous regression is strengthened
  to verify the secondary declaration's exact source-context relation and the
  primary/secondary records' actual typed channel coordinates, in addition to
  the existing exact selector and measured-secondary-region assertions. These
  additional assertions are syntax-checked only until the worker slot is handed
  off; no end-to-end success is inferred from source review.
- Source-only explanation of the apparent grouped/ungrouped distinction: group
  coordinates are selected by the compiled edge, while the previous predicate
  compared fixed coordinates on either side. Binding-owned channel identities
  expose this failure with `GroupBy.NONE`; a channel selected as a producer group
  takes another existing path. No Euler data, output, pipeline, or run
  configuration was opened to infer its particular success mechanism.
- Coordinator-authorized actual UI code-document/live installation validation.
  Source tests do not establish installed readiness. Worker must not install or
  merge, and must not inspect Euler's blind input or output.
- #204's corrected diagnosis is catalog discoverability, retaining the original
  failure and acceptance verbatim in `issue204_catalog_diagnosis_20260929.md`.
  Same-source runtime selection is proven; paired-channel runtime and actual
  GUI interaction remain open, so #204 is not claimed closed.

Draft PR: https://github.com/OpenHCSDev/openhcs/pull/205.

## Changed paths

- `openhcs/agent/dto/functions.py`
- `openhcs/agent/services/function_catalog_service.py`
- `openhcs/core/artifact_key_selection.py`
- `openhcs/core/artifacts.py`
- `openhcs/core/callable_contract.py`
- `openhcs/core/function_patterns.py`
- `openhcs/core/runtime_adapters.py`
- `openhcs/core/component_group_scope.py`
- `openhcs/core/runtime_stores.py`
- `openhcs/core/steps/function_runtime.py`
- `openhcs/interop/cellprofiler/runtime/adapter.py`
- `openhcs/interop/cellprofiler/runtime/artifact_binding.py`
- `openhcs/interop/cellprofiler/runtime/module_execution.py`
- `openhcs/interop/cellprofiler/runtime/output_record_request.py`
- `openhcs/interop/cellprofiler/runtime/output_recording.py`
- `tests/unit/test_artifact_output_ownership.py`
- `tests/unit/test_function_patterns.py`
- `tests/unit/test_function_runtime_source_projection.py`
- `tests/unit/test_function_step_execution_plan.py`
- `tests/unit/test_path_planner_materialization.py`
- `tests/unit/agent/test_mcp_cellprofiler_function_contract_friction.py`
- `tests/unit/test_function_artifact_outputs.py`
- `tests/unit/test_runtime_value_store.py`
- `tests/integration/test_measurement_declaration_journey.py`
- `docs/plans/issue133_204_measurement_contract_checkpoint_20260929.md`
- `docs/plans/issue204_catalog_diagnosis_20260929.md`
- `docs/plans/measurement_group_scope_triage_20260929.md`

Owned disposable test output was `/home/ts/.cache/agent-scratch/openhcs-issue-measurement-20260929`,
owner Zeno, purpose tiny synthetic plate and bounded pytest temporary outputs.
Removed its 608 KiB after preserving evidence and the fully self-seeding source
reproducer. Generated arrays and logs are regeneratable; no source or saved
sessions were stored there. No owned large scratch artifacts were created. Viewer-bind and ROI
materialization implementation surfaces remain with their assigned owners.

Current-main local build prerequisite: `a0263e82a1` adds the required
`_granularity_reconstruct` extension, reached by intensity -> shape -> zernike ->
granularity imports. A fresh source import failed with `ModuleNotFoundError`
before a test could execute. Zeno owns the bounded worktree-only build using the
existing `setup.py build_ext --inplace` declaration, with native intermediates
under `/home/ts/.cache/agent-scratch/openhcs-issue-measurement-20260929/native`.
This does not install packages or modify the shared environment or installed
source. The existing build completed in 2.33 seconds with 97,264 KiB maximum
resident memory. Intensity, primary, secondary, and the generated native extension
all import from this worktree; available RAM before the build was 10.8 GiB.
Removed the 136 KiB owned disposable native intermediates after this successful
import check. They are regeneratable. The generated ignored `.abi3.so` stays in
this worktree for source validation. This is import/build evidence, not a complete
headless or installed journey. The strengthened missing-source regression retains
the context relation and removes only its source declaration: one focused case
passes, with 47 unrelated cases deselected in that one-test check.
