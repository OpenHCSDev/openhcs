Neurite admission evidence: receiving owner
=========================================

Singer owns issue890 implementation after lesson889. Current open PRs checked:
654/404/160 do not claim this analysis module. Fresh main has no additional
change to neurite_outgrowth.py/count_cells_simple.py relative to the inspected
lesson branch. Foreign dependency gitlinks and retained validation paths remain
untouched. No scientific author was contacted or given trial information.

Determining source relationship
------------------------------

CellProfilerNeuriteEngineProfile.analyze owns the shared physical/pixel recipe.
PixelCellProfilerNeuriteEngineProfile composes PixelMetricCoordinates through
C3 MRO; this stays the unit/export policy, not a separate detection algorithm.
The sole production caller of _identify_neurites_cellprofiler is this shared
analyze method. The helper computes enhanced response once, adaptive candidate
support, optional seeded-component retention and raw-unit local response, then
intersects candidate support with the local-response gate before skeletonizing.
It currently returns only combined mask, skeleton and response. Original enhanced
and independent support values disappear at that return boundary.

Existing _neurite_qa_checkpoint_output declares source-identifiable on-demand
MainFlowPlaneProjectionOutputSpec images. Both callable declarations derive
their artifacts through the shared profile; SelectedPlaneImageOutput binds
checkpoint values to the actual neurite channel. These are the publication
owners to extend, not the viewer or a second threshold implementation.

The registered inspect_metaxpress_round_objects is not sufficient: it calls
round_object_segmentation_stages for a nuclear/body channel and returns round
object masks and width rows, not the consumed neurite tubeness/admission evidence.
Earlier custom diagnostic experiments recomputed stages; they are not an existing
registered observation of this original invocation. No algorithm defect is
inferred solely from absent final support.

Implementation closure
----------------------

Replace the helper's positional result with one owned stage result retaining
its computed values. Publish original enhanced response, candidate support
before/after optional retention and local response/gate through the existing
checkpoint/artifact family. Keep final mask, skeleton, labels, rows and rooted
graph numerically unchanged. Complete physical/pixel declaration annotations,
return assembly and related test/example consumers in one batch; no compatibility
tuple adapter. New diagnostic members require only their declaration/value hook,
not generic materializer/MCP/viewer edits.

Applicable patterns: IMPL-12 prohibits copied enhancement/threshold recipes;
BOUND-2 requires consumers to use the owned stage result rather than rediscover
its fields or recalculate evidence. AST census uses existing refactor-audit
overlay; declaration/call/import consumer searches are retained locally before
editing. Global NRA/dependency closure is not yet claimed at this checkpoint.

Acceptance remains source numerical invariance and ordinary installed native MCP
float checkpoint persistence/reopen, exact source/channel/axis identity and
matched raw/response/admitted views. Installed receiving needs the existing
whole-candidate builder/lane handoff, not a frozen scientific bundle hotpatch.
