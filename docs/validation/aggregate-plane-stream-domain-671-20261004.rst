Retained aggregate plane domain:671
==================================

Original BBBC007_FRESH651_88 failed executiond31a43b4-dae8-43cb-801c-e617c6c6d1f3
and viewer6021 log remain unchanged. The native guard correctly refuses a
payload-local site axis absent from the declared STACK layout. Default site
display is STACK, not LAYER; this is not an author instruction to change it.

Determining producer path: RuntimeArtifactMaterialization.stream_source_metadata_items
uses emitted scalar identities; StreamSourceComponentMetadataItems.complete_component_order
then removes a component absent from every scalar address. An aggregate image's
retained site planes are nevertheless emitted by StreamImagePayloadMetadataProjector.
Thus the scalar-only projection loses the display axis while the item still
declares its exact plane domain. The native strict guard is unchanged.

One owner projection
--------------------

StreamSourceComponentMetadataItems.from_image_metadata consumes the original
ImagePayloadMetadata retained plane declaration and SourceImageProvenance plane
identities. It derives domain observations without creating an axis store or
rewriting provenance. RuntimeArtifactMaterialization and StreamOutputBatch use
it; persisted image reopen uses the same projection instead of its separate
per-plane extraction. Collapsed contributor provenance cannot recreate axes.

Domain observation count is not streamed item count: image route addresses stay
one per image through the original StreamViewerComponentMetadataProjector,
excluding payload-local components. Artifact materialization already writes its
exact per-output scalar addresses through ViewerStreamBackendCallKwargs.
No compiler, generic stack, protocol, dependency package or native guard changes.

Source evidence
---------------

Existing refactor-audit AST overlay parsed runtime and core/steps families at
main2960a6abba15414119d0c69221ce68a81654d650. Before files retained outside source
as671-runtime-ast-before.json and671-producer-ast-before.json. Relevant semantic
consumers read: function_outputs.StreamOutputBatch/stream finalizer,
function_artifact_materialization.RuntimeArtifactMaterialization,
viewer_streaming_service.ViewerStreamingSource,
processing.materialization.ViewerStreamBackendCallKwargs (unchanged),
viewer_component_system domain/layout, Napari stream intake/pending-update/
aggregate binding/peer reconciliation/feature readout, and the installed
PolyStore viewer transport and Napari batch processor. Native receiver retains
unknown domain, incompatible mode, cardinality, duplicate-axis and mixed-domain
rejections. AST is source evidence, not public settlement acceptance.

Validation status
-----------------

Focused source controls and actual installed native settlement are not yet
claimed. #669 receiving06 publication is separately pinnedcf10bb; this source
change is NOT overlaid on that immutable target or a scientist. P001's adjacent
timeout later recovered; it is not proven this defect or a persistent deadviewer.
