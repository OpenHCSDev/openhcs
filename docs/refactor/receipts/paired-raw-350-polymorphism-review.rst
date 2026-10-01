Issue350 declaration-owner review
=================================

Integration owner: Schrodinger. Review starts at88e9c34ab766475edbadb147ed00576d9eac430b,
against frozen main094425c8c81324da7a3878379074e1bd8234ff52. Current NRA and
refactor-audit skills/catalogue and00-RULES.md govern this review. This is a
source-authored ownership repair, not a completed NRA global/native proof.

Deletion and correction
-----------------------

IMPL-12/TIME-3: remove the complete20-line NapariAxisPresentation projection
method from main, including the forwarding-only leaf residue left by017642ff0.
ViewerComponentAxisSemantics now owns axis_projection_semantics and
for_display_layout; PendingLayerUpdate, AxisPresentation and the MI batch
context all inherit the same implementation. No compatibility alias remains
on a leaf and the two production consumers are unchanged by this promotion.

IMPL-12: the initial candidate projection separately built exact-source lookup
beside virtual_paths_for_source. Consolidate the original lookup in
SourcePatternResolutionContext.virtual_paths_for_sources: one declaration pass
serves single-address lookup and candidate-position projection. It derives a
temporary exact-address index from the original manifest, not another stored
identity registry. SourceIdentityResolutionContext and SourceBindingMatchedImageSet
inherit it; the exact one-position admission proof remains unchanged.

Owning declarations and independent capabilities
------------------------------------------------

ViewerComponentLayout owns shared STACK-slot reconciliation; configured modes
continue to own route grouping. NapariDimensionLayerState owns its genuinely
optional mounted presentation and exposes participation, not a second store.
No new isinstance/type/name switch appears in either changed consumer.

MEMB-1/MEMB-2/MEMB-5: reuse real production MI:
ViewerDisplayBatchContext(ViewerComponentAxisSemantics, ViewerComponentNameMetadata,
Generic). The first branch owns entries/layout, inherited domain/projection
algorithms; the second owns the original name store and inherits label algorithms
from ComponentMetadataPresentationABC. These are distinct coordinate membership
and friendly-name capabilities, not copied records. The executable test exercises
both on one batch and checks entries/store object sharing. No new mixin, flattened
record, optional-capability flag or MRO priority table is introduced.

The synthetic new config leaf extends the existing genuine-MI NapariDisplayConfig
(ViewerDisplayConfigABC plus AnnotatedDataclassValidationMixin). Its small
component_modes hook calls super().component_modes() and adds its own region mode;
it does not copy the five inherited mode assignments. Dataclass validation stays
with the existing capability. Domain/name operations have separate contracts, so
there is no invented shared initialization chain or noop super facade.

New-case experiments: declaration only
--------------------------------------

1. Declare _RegionDisplayConfig in the existing test module: one owned region
   field/order extension and one cooperative hook. Add its row to the existing
   family-level review fixture. Both manual STACK and pipeline LAYER routes use
   the unchanged NapariLayerDisplayPipeline; native ViewerModel coordinates,
   translated positions and retained pixel values match for region1 and region2.
   Production consumer/algorithm edits for this new case: zero. This proves the
   typed display contract only; the fixture is not a new persisted config schema,
   registered public function or installed MCP/wire extension.
2. Add TRITC/channel3 to the source-binding fixture's declaration tuple. Existing
   ORDER membership resolves FITC and TRITC from exact DAPI anchor provenance
   with no alias-specific branch or consumer edit. A shared store's different
   planes remain distinct; a relative basename alone does not identify either
   /a/raw.tif or /b/raw.tif. The original ambiguous-position rejection is retained.
3. Use the existing MI batch context for region coordinates plus West/East names.
   Both inherited capabilities work together without editing their consumers,
   duplicating their fields or adding a new capability roster.

Mechanical guards and exclusions
--------------------------------

The source-context and projection surface guards assert that the leaf methods
resolve to the original ancestor's callable, not copied methods or forwarding
facades. These are targeted ownership-policy checks, not replacement R0/R1
detectors or golden snapshots of internal record shapes. Behavioral tests retain
all exact-coordinate, pixel-retention and ambiguous-source assertions.

BOUND-2/TIME-9: no external decoder, persisted store, numerical processing,
CellProfiler interop, package installation or backend dependency is changed.
No copied registry, codec subclass, fallback reader or parallel facade is added.
The frozen scientific trial and parent-owned PR349 files remain untouched.
No validation.lock, native/MCP/UI launch or live-slot acquisition occurs.

Proof limits
-------------

Original R0 bootstrap and R1 dependency-context failures remain preserved and
unqualified. The earlier global audit and overlay did not complete; this manual
diff review and its source tests do not supply global semantic proof. The initial
MI fixture expected the wrong label capitalization; its complete failure receipt
is retained, with exact expectations corrected to the existing title-case format.
Installed paired composition and bitmap QA still require parent's post349 slot.

Accepted source shards:53 source-binding tests,52 selected viewer/navigation
tests,15 selected pipeline source-projection tests;120 pass including the two
scoped ownership-policy guards. All use the exact frozen installed interpreter,
oneCPU/thread pools1, kernel512MiB/no swap and outer60s. Current complete command
and resource footers are retained in owner-review-source/viewer/projection.txt.
Ruff E9/F63/F7/F82 and git diff --check pass. No global/R0/R1/live pass is inferred.
