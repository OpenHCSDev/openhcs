Persisted point receiver: main-only source split
===============================================

Base and custody
----------------

Pinned remote main f7de9efad393bce83a3756a271f0cd4383783ea9, fetched on
2026-10-03. Local main2bc579ca9 is older and is not this base. The existing
checkout is reused only after no active source builder/runtime borrower was
found; seven foreign dirty gitlinks remain unchanged and excluded from commits.

This change has five production files, NOT PR494's 157-file Root-dependent
stack. PR494 head e6c0bf77f and all its original failed/public receipts remain
published. No producer, materialization, source provenance identity, graph,
compiler, registry or dependency declaration from Root394 is imported here.
The current main source_component_metadata_items and SourceVoxelSpacing owners
already implement the required coordinate/calibration projections.

One fact, one receiver owner
---------------------------

ROIFractionalZ guards the represented plane domain using existing nominal
component projections instead of comparing ancillary original-path records as
physical non-Z components. It retains every original record and rejects true
coordinate/calibration differences, duplicate/unordered Z and invalid fractional
coordinates. Source metadata construction/identity stays unchanged.

ROIArchiveSourceMetadata owns feature-only exclusion. StreamingService sends
the original source-bearing archive values. Both native Points and Shapes
derive feature columns through that original owner, without removing source
metadata from the transport payload.

NapariPointsLayerDisplayHandler retains the represented source span from its
validated anchor instead of truncating it at the largest occupied point.
NapariAxisPresentation derives scale, units and scaled world translation
together. Image, Shapes, Points and shared-axis reprojection consume it; their
separate unscaled translate calculations are deleted. Only explicit ZYX source
spacing calibrates projected Z, and selectors/bands remain dimensionless.

Applicable catalog leads: BOUND-2 (use existing source declaration), IDEN-1
(source span is not occupied extent), IMPL-12 (delete repeated translation).
The before census covers704 production and95 actual PolyStore/ZMQ dependency
modules, zero parse omissions. This named AST census is not a full NRA semantic
proof. Native retirement methods are disjoint from Singer522's selected6c49
source, as acknowledged by both owners.

Qualification boundary
----------------------

Main-only source d7dee6f9ebf20967b50b9d4c58e323933433d607 passed39 controls in
5.20s under512MiB/noSwap/CPU1, peak332959744B andOOM0. The original retained
public source records/domain/anchor are admitted unchanged. Receiver controls
cover singleton/full/nonzero-origin domains,16 real coordinate/calibration
rejections, fractional bounds, original ROI/source disk roundtrip, reopening,
native Image/Points transform and semantic navigation without a Qt application,
and Shapes feature separation. Root-only producer/graph/nestedidentity controls
are not imported or claimed. Existing fractional-axis/anchor guards remain.
Final consumer sweep also migrates the three original presentation tests and
the shared-axis navigation family to the mandatory owner-derived scale. The
separate ViewerLayerAxisProjection.translate contract is unchanged. These are
test consumers, not a new production repair or dependency/guard relaxation.
Ordinary combined wheel/target qualification is next. Prior59PASS on the full
Root-dependent source is NOT reported as main-only acceptance. No native or
viewer is launched. The public receiving plan is a NEW standalone reopen of the
unchanged989B archive SHA256
fd0a372f3100c73da9533b308d44c2f85fa7a86b733e2608ae986135cb4e401a,
then same-coordinate raw/points/combined XY/XZ/YZ with exact source metadata,
four-plane domain and ZYX2/.65/.65 calibration readback. Parent owns runtime
admission. The original failed producer9292bfb8 is not replayed; Root435's
persisted image metadata publication remains a separate unresolved producer
boundary. No science/biological acceptance or full orthogonal issue closure.
