# Measurement declaration checkpoint (#133, #204)

Implementation owner: Zeno. Integration owner: OpenHCS issue-batch coordinator.
Worktree: `/home/ts/wt/openhcs-exact-label-selection-20260929`.
Base: `openhcsdev/main` at `a0263e82a1`, fetched and merged normally on 2026-09-29.
The earlier checkpoint used `98d9b9d23`; the runtime checkpoint integrates new
main through normal merge `9f5d444515`. No parent/main-worktree edits, rebases,
resets, installed-source edits, or gitlink changes.

Closes #133. References #204; its paired-channel and actual GUI acceptance remain
open. This is a source-verified draft, not an installed/live-readiness claim.

## Implemented

- Measurement output validation belongs to `MeasurementsArtifactType`. Compilation
  requires a subject relation before invoking the callable. Schema-bearing rows and
  CSV materialization do not imply a measurement subject.
- Compile and runtime resolve subjects through the original relation owners. The
  error identifies the output and explains image, object, and artifact relations.
- The finalized callable contract delegates adapter-recorded outputs to the
  existing runtime adapter owner (`manages_artifact_outputs`). Native returns use
  the artifact-kind requirement. This distinction is required: CellProfiler
  primary/secondary modules record heterogeneous measurements themselves.
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
eleven changed production files were parsed against current merged main: zero added
`match`, `isinstance`, `getattr`/`hasattr`, or 6+-term boolean-chain AST nodes.
That guard detects listed shapes, not every possible semantic ownership defect.

| Pattern IDs | Owner, projection, and new-case evidence |
| --- | --- |
| IMPL-1/2/3/4, MEMB-1/2 | The finalized compiler calls `ArtifactPlanKeySelector.validate_artifact_output_declarations`; each spec delegates to `spec.artifact_type.validate_output_declaration`. Only `MeasurementsArtifactType` owns the subject requirement. No kind/name roster or external type switch was added. A future output kind supplies its rule on its declaration; compile/runtime consumers need no new branch. |
| IMPL-5/12/13, TIME-1/3 | `ArtifactSpecRelation.measurement_subject_for_output` resolves original relation-owned subjects once. The output-plan accessor, kind requirement, and native runtime all delegate; the former output-plan extraction body and runtime missing-subject body were deleted in place. The output-plan method remains a domain accessor, not an old reader or compatibility alias. |
| IDEN-1/2/5, BOUND-2/7, MEMB-3/4 | `SettingToKeywordBinding.require_parameter_name()` owns selector identity, separately from `runtime_parameter_name`. The only production `CellProfilerArtifactBindingSummary` constructor projects that owner; its selector field is now required. No selector store, guessed names, raw-row decoder, or attribute-name probe exists in the change. The catalog regression derives every registered binding and exercises new derived-name input and explicit-name output declarations without editing the projection. |
| IDEN-7, IMPL-10 | An initial placement incorrectly rejected heterogeneous CellProfiler records. Validation now runs after invocation-contract finalization, where the existing `runtime_adapter.manages_artifact_outputs` capability names the output owner. Native table-wide subject invariants apply only to native returned payloads, not adapter-recorded tables. Real primary/secondary compilation and execution plus native missing/corrected tests exercise both owners. |
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
  under the serialized validation lock when Euler releases it. Zeno is now the
  active runtime-fix owner under the explicit scope extension. The focused fix is
  present and store regressions pass, but complete paired execution remains
  unverified. No `core/source_bindings.py`, `core/source_binding_workspace.py`,
  source preparation, ROI, viewer, or #211 authorization method/test was modified.
- Scheduling: the parent owns the first released validation slot for real MCP
  #151/#212 and its useful merge/installation checkpoint. Zeno will run the full
  six-case headless journey only after the explicit next-slot handoff. No race for
  fresh environments, GUI, JVM, or installed-baseline changes is authorized.
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
- `openhcs/core/component_group_scope.py`
- `openhcs/core/runtime_stores.py`
- `openhcs/core/steps/function_runtime.py`
- `openhcs/interop/cellprofiler/runtime/adapter.py`
- `openhcs/interop/cellprofiler/runtime/artifact_binding.py`
- `tests/unit/agent/test_mcp_cellprofiler_function_contract_friction.py`
- `tests/unit/test_function_artifact_outputs.py`
- `tests/unit/test_runtime_value_store.py`
- `tests/integration/test_measurement_declaration_journey.py`
- `docs/plans/issue133_204_measurement_contract_checkpoint_20260929.md`
- `docs/plans/issue204_catalog_diagnosis_20260929.md`

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
