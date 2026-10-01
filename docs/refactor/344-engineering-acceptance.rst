PR344 engineering document and acceptance disposition
====================================================

Runtime source checkpoint: a14d471e3f2a92148f88a60b6c972e1a49f67db0.
Parent integrated current main and owns installed/native acceptance. Later
child checkpoints change only authoring examples, diagnostic checks and receipts.
H003g remains permanently FAILED and untouched. This is engineering, not biology.

Corrected complete source
-------------------------

examples/344-aligned-rescale-engineering.py is one complete PipelineDocument
with pipeline_config and one ordinary registered RescaleIntensity FunctionStep.
Its imports and declaration-derived input/output keyword names are explicit.
It contains no custom callable, executor wrapper, arrays or pixel-file operations.

The current recipe adopts the parent's successfully admitted private engineering
document's acquisition declarations, with only this example's output root/header
different. Submit the entire source via normal MCP authoring/compile/run.
Never strip its pipeline source bindings or substitute another config argument.

Separate fixture: the parent's cp-stack-installed-20261001/fixture contains
eight 2-D TIFFs, sites 1/2, channels 1/2, Z 1/2, timepoint 1. Representative
physical spelling::

    TimePoint_1/ZStep_1/A01_s001_w1_z001_t001.tif
    TimePoint_1/ZStep_2/A01_s001_w2_z002_t001.tif

Required existing declarations:

* source_filters EXTENSION / IS_TIF excludes HTD and other sidecars.
* FILE_NAME MetadataExtractionRule extracts well/site/channel/z_index/timepoint
  from the actual verified filename grammar. Zero padding is excluded from the
  numeric capture, so s001 resolves site "1", not a new site "001".
* METADATA SourceBindingMatchPlan explicitly pairs both aliases by
  well/site/z_index/timepoint. Channel distinguishes aliases, not the pair key.
* Both typed selectors restrict SITE "1" and their respective CHANNEL.
* Each NamedSourceBinding.component_identity explicitly declares CHANNEL "1"
  or "2", selecting the documented semantic coordinate projection.
* Calibration is (4.0, 0.5, 0.5) micrometers Z/Y/X. There are no embedded stack
  axes in a 2-D file, so source_stack_components remains empty. The step declares
  variable Z_INDEX, GroupBy.NONE and enabled inherited source bindings.

Source diagnosis and ownership
-------------------------------

Inspected source: public 327cec9f6 and parent candidate c7ed2acc4. Their
source_binding_workspace.py is byte-identical. SourceBindingWorkspaceProjector
source_candidates (line 886) builds file candidates from declared extraction
rules, not an injected native filename parser. _component_is_compatible permits
absent coordinates (line 997); _candidate_with_binding_components then assigns
selector coordinates. Without acquisition metadata, both aliases therefore
select the same physical universe; the ORDER ambiguity guard correctly rejects it.

ImageXpress inherits MicroscopeHandler.projects_declared_source_bindings False.
The current create_microscope_handler factory selects SourceBindingsHandler for
nonempty bindings when the requested owner does not project them. Raw inspection
without bindings can retain ImageXpress and parse its native coordinates. Thus
IMAGEXPRESS in pipeline source alone does not certify the resolved ingestion owner.
The child construction-only test verifies the factory route, not the parent's
live handler class; preserve actual handler identity in the parent receipt.

For store-emitted candidates, _source_set_projections (line 1157) retains
declared_address unless component_identity is explicitly declared. Metadata
extraction alone does not override a store's singleton address. NamedSourceBinding
documents component_identity as authoritative over inferred store coordinates
(source_bindings.py line 867). Explicit channel identity invokes the existing
coordinate projection; matched metadata supplies well/site/Z/time.

Disposition: the minimal public recipe omitted required acquisition declarations.
It was not a compiled valid native-alias recipe. Its inference of native alias
projection was wrong. The existing native handler does not promise that capability;
automatic propagation is a product/ingestion limitation, not a proven regression
of a promised alias-projection contract. No production intake, selector, guard,
dispatcher or executor changes are made. NRA BOUND-2 guidance keeps identity with
the existing metadata/binding/coordinate owners rather than adding a second parser.

Predecessors are not relabelled as passes. Parent reports four original admission
attempts retained, including same-ref ORDER rejection, duplicate projection address,
and HTD lacking well identity. Public predecessor source survives at 327cec9f6
and inside the original a14 supplemental archive. The promoted example now carries
the complete admitted acquisition declarations rather than the invalid minimal form.

Plans, occurrence evidence and output scope
-------------------------------------------

Expected projected source inventory: A01/site1/time1, four virtual files
CH1/2 x Z1/2, with exact physical refs and calibration. Both RescaleIntensity
declaration inputs are primary ImageArtifactType occurrences with no runtime
parameter injection. Callable mode is FULL_STACK, contract PURE_2D.

The public artifact-plan artifact_inputs list is not the complete input-occurrence
surface: _bounded_step_summaries renders step_plan.artifact_inputs storage plans.
PathPlanner skips a storage input plan when an exact source binding satisfies it
(path_planner.py line 1817). Exact invocation occurrences instead live in
CompiledFunctionInvocation.artifact_input_edges and contract.artifact_inputs.
RuntimeInputBindingRequest selects those declarations through RuntimeAdapterRequest,
then resolves a source-satisfied edge via source_binding_plan/source_artifact_payload.

For direct carrier proof, inspect those exact selected occurrences, their two
source bindings, runtime source payload axes and composed primary value before
the FULL_STACK projection. An empty storage-plan list does not prove missing
bindings, and a successful multi-plane output does not prove the carrier's type.
The actual MCP surface did not expose carrier or validity-mask inspection.

EngineeringRescaled declares SourceStackLineageSourceRelation to EngineeringCH1.
Output source identity must follow that first-source lineage, not a fabricated
four-source output contract. Output plate root for this published example::

    /home/ts/wt/openhcs-344-engineering-20261001/output/fixture_openhcs

For plate name fixture, well A01, step0, no grouping key, the canonical runtime
artifact-store address is::

    results/A01_EngineeringRescaled_step0.pkl

This is not a promised durable pickle. Compile/materialization plans own actual
TIFF destinations; retain the descriptors rather than guessing filenames.
The earlier EngineeringPlate example root changes if that is the input basename.

Bounded source checks and parent acceptance
-------------------------------------------

Child source-only checks parse the complete document and verify registered owner/
canonical raw callable identity. Pure synthetic path/declaration checks reproduce
the ambiguity and singleton-address failures, then prove four unique coordinates
with the same physical SourcePixelRefs. No TIFF pixels are loaded, no workspace is
initialized, and no pipeline is compiled/executed by this child. A first conflict
test used the wrong exception class; its 3-pass/1-fail receipt is retained, and the
corrected assertion preserves the actual existing RuntimeError contract.

Parent's reported installed/native gate (2026-10-01): same owned native5993,
ordinary MCP compile job1 COMPLETE in 1.823s; execution job2 COMPLETE in 0.745s.
Main-flow and EngineeringRescaled each yielded two Z TIFFs, each (2,32,32) float32.
MCP samples were compared against all four raw planes with global stretch
min90/max8405: 8192 pixel comparisons across both destinations, maximum error
1.23e-7 and zero errors over 1e-6. Parent reports exact declared calibration and
first-source CH1/Z scope, and retains the actual native observation export.
These are parent observations, not independently rerun child measurements.

This clears the reported installed dense ABI continuity gate, not direct carrier/
mask inspection or biology. Raw TIFF validity masks are None; source MaskedImagePayload
and capability-MRO controls are separate evidence. Child source117+45 and parent's
revised installed21 cases remain distinct from this continuous MCP/native gate.
R1 remains unqualified. Parent alone closes/verifies owned processes, archives live
receipts and integrates the public PR. No frozen H003g retry or held-out access occurs.
