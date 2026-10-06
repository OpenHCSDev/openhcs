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

Focused source controls:44 passed in671-source-controls04.log; its one remaining
setup error was the omitted original viewer_ack_return_route fixture. A distinct
bounded follow-up loaded the ORIGINAL tests/conftest.py using the installed
dependency bootstrap before selecting these source modules: the remaining
selected-plane persistence/QA-stream test passed, terminal0, in
671-source-controls05.log. Thus all45 selected controls pass across the two
original receipts, not a fabricated single all-pass run. Peak456088/461632KiB;
no invented memory/swap ceiling. Earlier bootstrap/pytest configuration
negatives01..03 and fixture omission04 are preserved, not product failures.

Actual installed native aggregate settlement remains unverified. #669 receiving06
publication is separately pinnedcf10bb; this source change is NOT overlaid on
that immutable target or a scientist. Its installed two-well publication now
passes, with exact typed native closure, independently of676. Singer explicitly
confirmed the shared function_outputs.py changes are disjoint:669 owns the
OpenHCSMetadataTarget publication hunk;676 owns StreamOutputBatch domain/route
projection. Normal current-main integration after669 merge plus installed
aggregate-plane acceptance are required before676 merge. P001's adjacent
timeout later recovered; it is not proven this defect or a persistent deadviewer.

Current-main integration
------------------------

669 merged1aba11c9db6598d42cbb9acbf53f29ee08b0280d. Normal merge16f57253b
preserves its OpenHCSMetadataTarget step-update/final-reconciliation distinction
without reapplying its hunk. StreamOutputBatch's retained-plane observations and
one-per-image route addresses remain disjoint; no domain or index store added.
Current main's compilation/materialization changes are also retained normally.
The integrated four-file focused suite, including the complete function_outputs
consumer controls, passes119 tests, terminal0:671-integrated-controls06.log,
467632KiB peak, 12.45s wall. Installed native aggregate acceptance remains open.
Foreign eight gitlinks and ten untracked historical runtime groups are untouched.
