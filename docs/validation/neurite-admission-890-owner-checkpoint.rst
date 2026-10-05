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
Before this change it returned only combined mask, skeleton and response. Original enhanced
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

Implementation checkpoint a3775984e
----------------------------------

NeuriteAdmissionResult replaces the positional detection return. Its response
property reads NeuriteAdmissionPlanes.local_response; it is not another stored
response. Enhanced response and independent threshold/retained/local gates
come from the same execution. The optional retention-disabled case keeps the
original same support object; it does not claim a seed gate executed.

NeuriteAdmissionPlanes field declarations derive checkpoint names/order and
callable ABI slots. Both physical/pixel functions use NeuriteOutgrowthRuntimeTuple,
removing duplicated return annotations. The shared profile adds the declared
planes to its original return/artifact family. Existing detector arithmetic,
settings/defaults, labels, summary rows and graph construction are unchanged.

SelectedDiagnosticPlaneImageOutput cooperatively uses the original selected-plane
ancestor for exact source/axis admission, then DiagnosticPlaneSource for response
intensity semantics. Its full-raster shape guard retains original spatial domain;
it cannot claim cropped data as unchanged geometry. Float responses are not
reinterpreted with an acquisition uint16 scale. No generic viewer, materializer,
MCP consumer or dispatch roster changed. Existing demo/integration/publication
fixtures now consume the extended declaration family rather than truncated slots.

Qualification
-------------

Existing refactor-audit Package/Overlay parsed all702 OpenHCS production modules
at the before/after revisions, zero parse omissions. Semantic reads cover profile
declarations/MRO, the sole helper call, artifact return assembly, SelectedPlane
source contextualization, DiagnosticPlaneSource intensity semantics, original
image metadata/spatial owner and persistence/stream consumers. Companion tests,
preset and integration uses were searched and migrated. This is production AST
coverage and owner/consumer evidence, not a complete global NRA/dependency R1
certificate. Borrowed receiving18 dependency origins are explicit in controls;
foreign dependency gitlinks are preserved, not silently qualified as current.

Original pinned R0 over both changed production files: all dispatch/raw-key/
validation/probing measures delta0; three new owner/result/leaf classes, net52
code lines. Original raw output is retained, not a copied detector.

Source01:104 PASS/1 FAIL/3 deselected,33.25s/660552KiB/swaps0. The sole failure is
demo-contributor results outside the strict output plate root. Exact pre-change
recipe and original test reproduce that same path rejection in baseline03;
the guard remains strict and the failure is preserved. No unrelated path fix
is included. This is not a whole-source-suite pass.

Pinned pre-change recipe comparison:4 cases PASS (unbranched/branched, seed
retention disabled/enabled),8.76s/447556KiB/swaps0. Raw input, both measurement
row sets, all existing labels/checkpoints and complete rooted graph match
exactly. Five observation planes are added; no scientific output is replaced.

Publication02:13 PASS/1 explicit fixture deselection,13.36s/479760KiB/swaps0.
Includes ordinary float TIFF persistence and typed stream construction across
both declared runtime-axis members, source channel2/path/XY spacing and pixels.
Full publication test needing the original global ACK fixture is deferred to
normal installed fixture loading, not supplied a copied ACK implementation.
Newcase04:1 PASS/14 deselected; an independently declared diagnostic leaf with
an observed-projection capability exercises cooperative super() hooks through
the original ImageArtifactType consumer and preserves selected identity/float
units. No consumer edits admit that new case.

Complete stdout/stderr, original source/test snapshots, AST/consumer evidence
and original R0 are archived byte-exact alongside this receipt. They are source
checks, not actual installed native acceptance. No scientific author was given
these controls or updated instructions. The new receiving packet reuses the
existing public541 acquisition generator and normal launch/lifecycle owners.

Ordinary installed native acceptance completed on receiving20. See
neurite-admission890/LIVE-ACCEPTANCE01.rst and the byte-exact public archive.
Source and native scope are now qualified; this is engineering observability,
not biological tracing completeness or an active scientific bundle update.
