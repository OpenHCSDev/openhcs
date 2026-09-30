Same-source raw/result viewer QA follow-up
=========================================

Active integration/fix owner: parent OpenHCS agent. No existing open issue/PR
was found for this exact two-stage witness (the existing retained-viewer schema
issue280 is a different contract). This is not attributed to the ACK patch:
the existing clear_accumulated_stream_state resets all component groups while
leaving mounted native layers. No scientific trial has been accepted.

Reproducer uses the real current candidate OpenHCS sourcec299c6e98, native ACK
9e11f6f, PolyStoredc34173, metaclass448cdf07, existing Python3.12 environment,
MCP3889216, exact native3890586 and managed Napari3897920 on display91.
All artifacts live in the persistent batch's ack-runtime-parent-20260930/.

1. Through MCP generate one ImageXpress well A01, one channel/Z/time/site,
   96x96, four synthetic blobs, seed42. No assay or held-out data.
2. Through stream_plate_files_to_viewer open the single source on TCP5592.
   The manual route has item_count1 and native Y/X scale0.65/0.65.
3. Inspect and compile the retained lazy PipelineDocument pipeline.py.
   One ordinary registered gaussian_blur(sigma1), one worker/thread, disk
   checkpoint and final image, Napari output to that same owned TCP5592.
4. Execute once: native ee69d54e-9d28-49da-a227-5db0efecd65d completes in0.908s.
   Raw MCP producer ACK46881 and native producer ACK36219 coexist. Native
   logs report All1 images processed; both durable TIFFs inventory/read back.
5. Read viewer state and capture again. Both native layers remain mounted,
   but manual route item_count/component_value_count becomes0 and its typed
   producer/payload inventory vanishes. Pipeline route still has item_count1.
   Pipeline Y/X scale is1/1 instead of the same-source raw0.65/0.65.
   The opened post-execution bitmap visibly superimposes displaced/sized-differently
   raw/blurred blobs. No caller resampling or spatial transformation is declared.

Witnesses (both bitmaps opened by parent, not accepted as matching QA):
raw-capture/20260930T200752669566Z_napari_5592_OpenHCS_Napari_Visualization.png;
post-execution-capture/20260930T201135297437Z_napari_5592_OpenHCS_Napari_Visualization.png;
mcp-paired-session.log (raw state, plan, compile/job status, post state, readback);
pipeline.py and original source/output TIFFs.

Source lead, not a complete causal proof: NapariViewerServer.
clear_accumulated_stream_state clears component_groups/component_values/name
metadata wholesale, despite mounted manual layers. Source spatial provenance
must be followed separately through manual and native pipeline producers.

Acceptance for the follow-up: reuse the original typed route/producer/source
owners; reset only the execution-owned state, preserving usable raw inventories;
derive both native transforms from original physical source geometry. Add a
provider-free ownership regression plus repeat this actual MCP compile/run/viewer
journey at the same coordinates, asserting raw/result inventories and transforms
and opening matched raw-only/result-only/combined captures. No string-origin
switch, second registry, viewer-only scale patch, legacy format alias or biological
acceptance from counts. Parent will use a separate persistent worktree/PR after
shipping the independently verified ACK/startup checkpoint.
