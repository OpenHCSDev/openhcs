# Measurement declaration checkpoint (#133, #204)

Implementation owner: Zeno. Integration owner: OpenHCS issue-batch coordinator.
Worktree: `/home/ts/wt/openhcs-exact-label-selection-20260929`.
Base: `openhcsdev/main` at `98d9b9d23`, fetched and merged normally on 2026-09-29.
Fetched again before publishing the regression checkpoint; normal merge reported
already up to date. No parent/integration edits, rebases, resets, or gitlink changes.

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
  It remains an unweakened failing regression, deselected explicitly above;
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

## Essential anti-pattern audit: actual ownership evidence

This is a focused source/caller and AST audit against the current archived
refactor-audit pattern catalog, **not a complete NRA semantic/proof scan**. All
seven changed production files were parsed against the merged base: zero added
`match`, `isinstance`, `getattr`/`hasattr`, or 6+-term boolean-chain AST nodes.
That guard detects listed shapes, not every possible semantic ownership defect.

| Pattern IDs | Owner, projection, and new-case evidence |
| --- | --- |
| IMPL-1/2/3/4, MEMB-1/2 | The finalized compiler calls `ArtifactPlanKeySelector.validate_artifact_output_declarations`; each spec delegates to `spec.artifact_type.validate_output_declaration`. Only `MeasurementsArtifactType` owns the subject requirement. No kind/name roster or external type switch was added. A future output kind supplies its rule on its declaration; compile/runtime consumers need no new branch. |
| IMPL-5/12/13, TIME-1/3 | `ArtifactSpecRelation.measurement_subject_for_output` resolves original relation-owned subjects once. The output-plan accessor, kind requirement, and native runtime all delegate; the former output-plan extraction body and runtime missing-subject body were deleted in place. The output-plan method remains a domain accessor, not an old reader or compatibility alias. |
| IDEN-1/2/5, BOUND-2/7, MEMB-3/4 | `SettingToKeywordBinding.require_parameter_name()` owns selector identity, separately from `runtime_parameter_name`. The only production `CellProfilerArtifactBindingSummary` constructor projects that owner; its selector field is now required. No selector store, guessed names, raw-row decoder, or attribute-name probe exists in the change. The catalog regression derives every registered binding and exercises new derived-name input and explicit-name output declarations without editing the projection. |
| IDEN-7, IMPL-10 | An initial placement incorrectly rejected heterogeneous CellProfiler records. Validation now runs after invocation-contract finalization, where the existing `runtime_adapter.manages_artifact_outputs` capability names the output owner. Native table-wide subject invariants apply only to native returned payloads, not adapter-recorded tables. Real primary/secondary compilation and execution plus native missing/corrected tests exercise both owners. |
| AGENT-2/3/6/7, TIME-5/9 | No second mechanism, format converter, test-only production switch, or dormant feature was added. One pre-existing cardinality fixture received a valid artifact-level subject so its original missing-return assertion remains meaningful. The paired-channel failure is retained, not hidden by weaker expectations; publication proceeds with that exact acceptance gap stated. |

Caller review covered the default invocation declaration provider (returns the
finalized `CallableContract`), every call to the new output-validation hook and
shared subject resolver, all production measurement-subject accessors, and the
catalog DTO constructor/consumers. Structural `extract_artifact_declarations`
still checks relation references without prematurely applying native runtime
requirements to partially reconstructed CellProfiler contracts. Real compile
inspection reaches the finalized validation boundary and fails before execution.

New-case edit count: one owner declaration for a new setting binding, zero new
catalog/compiler branches; the registered/new-binding regression exercises this.
A new subject relation exposes its existing `measurement_subject()` capability;
both compile and runtime use it unchanged. A new output kind supplies its own
validation hook, with zero edits to the generic compiler consumer. The
duplicate-resolution removal is factoring; no pure file move is claimed.

## Remaining acceptance

- The original paired-channel journey fails **before measurement**, while
  secondary consumes `Nuclei`: the exact record has fixed channel 1 scope,
  but `RuntimeArtifactInput._matches_execution_scope` compares it with the
  secondary source's channel 2 scope and rejects it. Address, axis, and producer
  identity match. Reproduce with `pytest -q
  tests/integration/test_measurement_declaration_journey.py -k paired --tb=short`
  under the serialized validation lock when Euler releases it. Zeno preserves
  the reproducer; integration coordinator must assign/coordinate the runtime/input
  fix before edits outside this worker's measurement scope. No runtime/input,
  source preparation, ROI, or viewer implementation was modified.
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
- `openhcs/core/steps/function_runtime.py`
- `tests/unit/agent/test_mcp_cellprofiler_function_contract_friction.py`
- `tests/unit/test_function_artifact_outputs.py`
- `tests/integration/test_measurement_declaration_journey.py`
- `docs/plans/issue133_204_measurement_contract_checkpoint_20260929.md`
- `docs/plans/issue204_catalog_diagnosis_20260929.md`

Owned disposable test output: `/home/ts/.cache/agent-scratch/openhcs-issue-measurement-20260929`,
owner Zeno, purpose tiny synthetic plate and bounded pytest temporary outputs.
Clean after preserving test evidence; no source or saved sessions are stored there.
No owned large scratch artifacts have been created. Viewer-bind and ROI
materialization implementation surfaces remain with their assigned owners.
