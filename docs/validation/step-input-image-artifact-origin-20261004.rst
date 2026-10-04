STEP_INPUT named-image artifact origin after ordinary preprocessing
==================================================================

Investigation checkpoint, not a repaired or live-verified implementation.
Reviewed main e1400cb9f278149fea7056b8fc8319d1ebd6ca69 and the retained
installed source0b3ead24459954829986e2e0763a886bb4d0fef6 exhibit the same
source-artifact resolution route. Frozen analysis and all originals remain
unchanged; no reference, scientific correction or parameter advice is supplied.

Observed public workflow
-------------------------

A source-bound image enters two ordinary registered NumPy processing steps.
The following CellProfiler primary-object step declares PREVIOUS_STEP and an
image alias with origin STEP_INPUT. With a new alias the invocation raises
``Source-bound artifact ... resolved no workspace members``. With the original
raw alias the invocation completes, but its threshold support is inconsistent
with the separately measured processed image. That second pixel-origin inference
is not a demonstrated full-array equality. Zero surviving objects does not
prove absence of biological objects or identify the underlying gate by itself.

The complete frozen source uses normal PipelineDocument/FunctionStep/source
binding declarations. The original raw and measured processed arrays are uint8;
the manual threshold is expressed in the existing CellProfiler normalized
domain. No independent normalization defect has been established.

Determining owners and consumers
--------------------------------

* ``SourceAssignmentBase.origin`` in core/source_bindings.py explicitly defines
  selection from prior-step input versus pipeline-start sources. The existing
  CompiledSourceUniversePlan also models that distinction; it is not a new flag
  to invent at the adapter.
* PathPlanner's advance_artifact_context_after_compiled_pattern creates an
  implicit unnamed image artifact for ordinary unlabelled NumPy returns.
  The previous source alias is consequently not the current main-flow artifact
  name merely because its spatial provenance remains attached.
* InvocationArtifactInputEdgePlan.source_projection in function_patterns.py
  assigns a main-flow projection only when the exact artifact ref is in BOTH
  current main-flow artifacts and the invocation's group-scope sources.
* PathPlanner.compile_invocation_input_edges compiles unstored named source
  edges from those declarations. Its separate process_artifact_inputs omits
  storage plans for exact declared source bindings.
* CP RuntimeInputBindingRequest.artifact_value (artifact_binding.py300--365)
  sends a source-only edge to RuntimeAdapterRequest.source_artifact_payload.
* RuntimeAdapterRequest.source_artifact_payload (runtime_adapters.py251--366)
  unconditionally resolves members through VirtualWorkspaceSourceProjection
  and loads Backend.VIRTUAL_WORKSPACE. It does not consult binding.origin.
  A new alias cannot match the original workspace source; an existing alias
  can load its original pixels despite declaring STEP_INPUT.
* FunctionCoreExecutor.declared_source_payload is the other direct consumer of
  that same resolver. A CP-only special case would leave the authority split.

Existing refactor-audit Package AST parsing covered200 current-main modules in
core and CP runtime with zero parse omissions. The resolver has exactly two
direct call sites in that scope: FunctionCoreExecutor and CP artifact binding.
This is targeted source evidence, not an NRA semantic proof or a complete
dependency/selector migration census. The initial file-root Package invocation
parsed zero modules; it was corrected to actual directory roots, not reported
as coverage.

The applicable ownership failure is IDEN-5 (declared source origin versus a
different pixel authority at consumption), with IMPL-13 as the repair risk if
another adapter-specific origin mechanism is added. The correct change must
extend the existing origin/source projection owner and migrate both consumers,
not add aliases, a second workspace, a reader fallback or a string dispatch.

Ownership and acceptance
-------------------------

Popper owns the binding investigation. Singer's626 change owns automatic/named
publication metadata only and is semantically separate. PR630 crosses execution,
runtime and output identity; coordinate its integration owner before changing
those files. This checkpoint deliberately contains no competing runtime hunk.

Use a modest synthetic scalar image and the existing registered processing/CP
pipeline entrypoint, not the frozen retinal field. Retain an original raw alias,
apply an ordinary operation that produces distinguishable pixels, then select
an explicit STEP_INPUT alias at primary objects and measure the original alias
with PIPELINE_START in a separate downstream step. Acceptance must demonstrate:

* new and reused STEP_INPUT aliases select the actual processed pixels;
* PIPELINE_START retains raw pixels and source identity;
* exact component/plane selectors work for a multi-channel or multi-plane
  processed carrier, including a supported companion source-artifact input;
* a genuinely absent/ambiguous selection still fails through its original owner;
* current main-flow/named artifact producers and both resolver consumers use
  one consistent authority, with replaced decisions removed;
* the existing installed public MCP compile/execute/measurement path confirms
  the result after the coherent implementation, not only mocked adapter tests.

No synthetic execution, native launch, source installation or acceptance result
is claimed by this initial checkpoint. The frozen foreground observation does
not by itself prove the precise consumed array; source/runtime reproduction is
the next engineering step, kept separate from assisted science development.
