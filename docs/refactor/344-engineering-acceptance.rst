PR344 engineering document handoff
=================================

Runtime source checkpoint: a14d471e3f2a92148f88a60b6c972e1a49f67db0.
Parent owns installed integration with main 05c3cf288 and the sole native
5993 slot. This child has not loaded fixture pixels, compiled the document,
started MCP/native/viewer, or executed a pipeline. This is not H003g, a
scientific retry, biological validation, or an installed acceptance receipt.

Complete source
---------------

``examples/344-aligned-rescale-engineering.py`` is one complete public Python
PipelineDocument: pipeline_config plus one ordered FunctionStep. Submit the
entire file through the ordinary MCP document authoring/validation/compile
route. Do not call a custom function, construct runtime arrays or invoke the
contract executor as a substitute for that route. Imports are explicit in
the source; input/output keyword keys come from
RescaleIntensityModule.declared_artifact_bindings().require_parameter_name().

Fixture request for the parent
-----------------------------

Use the existing synthetic ImageXpress fixture infrastructure, not any frozen
H003g input or artifact. Proposed separate root::

    /home/ts/wt/openhcs-344-engineering-20261001/raw/EngineeringPlate/
      TimePoint_1/ZStep_1/plate_A01_s1_w1.tif
      TimePoint_1/ZStep_1/plate_A01_s1_w2.tif
      TimePoint_1/ZStep_2/plate_A01_s1_w1.tif
      TimePoint_1/ZStep_2/plate_A01_s1_w2.tif

Each file: one 32x32 uint16 plane, one site, one timepoint; distinct channels
and Z planes. One deterministic nonconstant engineering pattern is
``1000*(channel-1) + 100*(z-1) + 32*y + x`` with channel/z in {1,2} and
x/y in [0,31]. Record actual fixture creation, input hashes and inventory in
the parent's receipt; no fixture files were created by this child.

Two typed aliases explicitly select channel 1 and channel 2. Step variable
components select Z_INDEX, group_by is NONE, and both aliases are enabled.
There are no embedded stack axes in a 2-D file: source_stack_components
deliberately remains empty. The existing source-bound artifact resolver loads
each alias's members and calls stack_image_payloads in RUNTIME_SLICE mode
(core/runtime_adapters.py). Two declared primary image inputs then pass
through CellProfilerModuleExecutor._image_request and
compose_aligned_image_payload: an AlignedImageStack with a two-channel bundle
per Z slice. The callable's FULL_STACK mode overrides slice execution.
This is the original primary carrier failure path, not an auxiliary kwarg
or the ordinary single dense two-channel input path.

Compile identity gates, before execution
---------------------------------------

Require the actual inventory to contain A01/site 1/timepoint 1, channel 1/2,
Z 1/2. Main 05c3cf288 includes the parent's raw ImageXpress ZStep fix.
Reject a flattened singleton-Z inventory rather than accepting a different
test. Require the registered declaration owner RescaleIntensityModule,
function_name rescale_intensity, ProcessingContract.PURE_2D and
ImagePayloadExecutionMode.FULL_STACK. The public document authority
canonicalizes decorator callables through RegistryService: callable object
identity before/after normalization is NOT the identity gate. Its canonical
raw callable and module declaration owner are the gates.

Require exactly two ImageArtifactType input occurrences, in declared order:
EngineeringCH1 and EngineeringCH2. Both declaration bindings have
runtime_parameter_name None; compiled artifact input parameter_name is None.
No auxiliary runtime keyword image is injected. Each alias's source payload
must retain two exact Z members in RUNTIME_SLICE order. The composed primary
must be aligned before the full-stack contract materializes it, and its dense
callable input should be (2 Z, 2 bindings, 32 Y, 32 X). These are acceptance
requirements inferred from inspected production authorities, NOT a claimed
compile or native observation. Preserve the observed typed plan and logs;
if the entrypoint does not expose carrier evidence, do not invent it from a
successful run or from file/channel count alone.

Require one output ImageArtifactType named EngineeringRescaled. Its declared
SourceStackLineageSourceRelation is anchored to EngineeringCH1 by
RescaleIntensityModule.artifact_output_relations. Output contextualization
and materialization remain owned by the existing output policies. This
declaration does not promise a new four-source output identity contract.

Addresses, pixels and metadata gates
-----------------------------------

Configured output plate root::

    /home/ts/wt/openhcs-344-engineering-20261001/output/EngineeringPlate_openhcs

For axis A01, step 0 and no grouping key, PathPlannerPaths.artifact_path
derives this canonical runtime artifact address::

    results/A01_EngineeringRescaled_step0.pkl

This is an artifact-store address, NOT a claim that a durable pickle exists.
ImageArtifactType projects disk exports under ``images/EngineeringRescaled``
when its writer uses plane projection, or uses its declared source-identity
filename policy for scalar exports. Retain exact compiled output/materialization
plans and returned artifact descriptors before asserting TIFF suffixes or
export filenames; this child has not compiled or observed those paths.

For the proposed integer pattern, the dense default stretch expectation is
``(input - 0) / 2123`` across both Z planes and both source bindings. Confirm
the actual callable normalization/dtype policy and compare every output
plane against the recorded fixture, not just extrema or a run-success flag.
The original failing full-stack path would raise float(AlignedImageStack)
before emitting the image. Preserve a real original failure if available;
do not reinstall/replay an old candidate merely to manufacture that receipt.

Configuration declares synthetic physical calibration (4.0, 0.5, 0.5)
micrometers in Z/Y/X order, and both source aliases retain their exact source
paths, channel/Z coordinates and native 32x32 spatial domain. Inspect typed
metadata at input composition and output contextualization separately.
The input composition must retain all four source contributors and both
aliases; output source scope follows the actual first-source lineage relation.
Do not silently equate a virtual workspace path with its physical raw path:
resolve provenance through the recorded source projection before comparing.
Calibration metadata preservation is not a physical measurement validation.

Ordinary raw TIFFs carry no validity mask: require mask None to remain None.
``load_as_mask`` converts pixel values to booleans; it does NOT manufacture
a validity mask. Nontrivial MaskedImagePayload preservation and independent
mask capability MRO cases are covered by the source family controls. A live
nontrivial-mask claim would require a separate parent-approved typed masked
fixture/path; this minimal document does not claim that coverage.

Source-only checks
------------------

diagnostics/test_344_engineering_document.py executes only the Python
configuration document through PipelineDocumentAuthority.from_source and
checks declared source selectors, calibrated config, step axis and canonical
registered identity. It does not load data, compile or execute a pipeline.
The initial object-identity assertion failed because canonical normalization
replaces the decorator wrapper; that receipt is retained. The corrected test
uses the owning module and canonical raw callable identity instead.

No biological guide/validated assay recipe was retrieved or claimed. The
use-openhcs skill's complete-document rule applies, but the parent's explicit
source-only/no-MCP instruction defers its live catalog/schema/compile gates
to the installed acceptance owner. Do not label this source check MCP validated.
