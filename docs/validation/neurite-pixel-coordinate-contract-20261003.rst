Integrated rooted neurite analysis: missing pixel-unit contract
=============================================================

Status and ownership
--------------------

Singer owns the analysis declaration/unit boundary implementation. The original
Root394 exclusive claim below is historical:394 is merged and no current unit
owner overlap was found. Singer now owns the narrow spacing/graph/export seam.
Parent owns future installed/public acceptance. No scientific author contact.
Existing isolated checkout reused, mainf910830954646b4c38c6ff46ec0a2f78b1d3addb;
522 and539 published branches/evidence are retained without further mutation.
Foreign gitlinks/untracked validation work remain unchanged.

Open issue/PR claims were checked:424 owns the existing soma pixel-size gate,
390/391 help projection is merged, and435/394 owns publication. None supplies
an integrated pixel-unit rooted neurite declaration. The compact analysis blob
45f7f22401b93f1c433f7b5f9639fef17b0d157d is identical on current main,522,
main306512de and Root394f12250993d91dfa38d5de548fed0fabbaa107e61.

Determining contract
--------------------

neurite_outgrowth_metaxpress declares artifact_inputs("pixel_size"). Its
MetaXpressCellBodySettings/OutgrowthSettings and inherited nuclear widths are
physical controls. PixelSizeMetadataArtifactProvider, microscope_interfaces.py
238..253, explicitly resolves micrometers per pixel. PathPlannerMetadataArtifactInjection
576..604 resolves that provider before invocation. OpenHCSMetadataHandler.get_pixel_size
312..322 delegates declared source spacing to SourceVoxelSpacing's physical
projection. RELATIVE is dimensionless and correctly cannot provide it.

SourceVoxelSpacing.require_physical_pixel_size404..416 rejects missing absolute
calibration, anisotropicXY and mixed/conflicting sources. Root's corresponding
903..914 implementation retains the same strict contract. This guard is correct.
No supplied1.0, changed source units, copied callback or caller bypass is a fix.

The registered compact callable has no pixel-coordinate unit selector or pixel
settings/results declaration. Its direct default HiddenPixelSize(1.0) is not a
supported compiled pixel route. NeuriteOutgrowthCellResult400..408 mentions pixels
under legacy _um headings, contradicting the actual required physical artifact.
Those headings are not proof of micrometer calibration and must not be dropped
or silently repurposed to make an uncalibrated run appear valid.

The shared computation is already present: segmentation, soma-rooted path
partition, per-cell rows, labels, diagnostics and _build_neurite_morphology_graph.
Lengths use skan spacing; areas use spacing squared. Graph coordinates remain
source-pixel indices, coordinate_spacing carries conversion and node radii/edge
features currently claim physical units. SpatialGraph carries source provenance
but no explicit analysis-unit field. The SWC writer's _swc_xyz applies that
spacing and describes physical coordinates. Therefore a pixel route needs an
end-to-end typed unit contract, not merely successful numerical invocation.

Existing alternatives do not establish equivalent capability. The CP
measure_object_skeleton family has seed-relative pixel measurements but not the
compact unified-neuron/rooted-forest contract. skan_axon_skeletonize_and_analyze
has physical voxel_spacing and network/branch outputs, not that soma ownership.
HMM tracing has its own seeds/graph dictionary contract. No alternative is
claimed absent or scientifically invalid; none is the missing integrated route.

Retained reproducer and limits
-----------------------------

Coordinator-only original evidence under the public94 author output:
REPORT.md, final/pipeline.py and evidence/098-openhcs_get_execution_status.json.
The original compile job reports the physical scalar calibration exception;
the saved status traceback is explicitly truncated5855characters. The fallback
does not execute the compact rooted analysis. No raw image, held-out answer,
reference annotation or measurement CSV was opened for this investigation.
Original rejected/frozen outcomes are unchanged. Rejection of a particular
ownership-dependent metric does not imply every algorithm-defined estimate is
useless; graded quality policy is separate539, not a calibration workaround.

Source evidence
---------------

Latest NRA skill and authoritative refactor-audit ZIP plus identity,
implementation and boundary catalogs were read. Relevant patterns:IDEN-1/2
(numeric scale versus unit identity),BOUND-2 (use the existing source frame),
BOUND-8 (do not flatten units to a scalar),IMPL-12 (do not copy the topology).

Original full-package overlay01 hit enforced512MiB OOM,Swap0; retained, no cap
increase or clean-scan claim. Original debt_census02 subsequently parsed the
whole704-module production package with zero parse omissions,16.98s/maxRSS45836KiB,
oneCPU512MiB/Swap0. This is structural source coverage, not full NRA R1,
dependency-family closure or behavioural proof. family-consumers03.txt records
the related declaration/consumer source search; it is not AST resolution.
Complete related dependency/consumer facts remain necessary before structural
implementation. No tests, builds, installations or native launches occurred.

Byte-exact source evidence is neurite-pixel-coordinate-contract-20261003.tar.gz;
original logs remain in the issue-batch engineering-neurite-units-20261003 root.

Receiving design and acceptance
-------------------------------

Keep the physical calibration guard and physical result schema. Extend the
original source-frame/unit and analysis owners with a genuine pixel-coordinate
declaration, explicit pixel controls and unit-correct row/graph projections.
The existing integrated algorithm remains one implementation. Shared mechanisms
belong on their behaviour-owning ancestor; unit declarations supply small
conversion/projection hooks. Independent source provenance and unit capabilities
compose through their existing cooperative inheritance, not a consumer mode
switch, mirrored unit table, cloned callable or wrapper invoking1.0.

A synthetic known soma/branched path must compile and execute through the
registered pixel-unit contract without physical calibration; measurements and
graph/archive readback must explicitly retainpx/px2/source coordinates.
The same known geometry with genuine calibration must preserve the physical
contract and correct scaling, while relative/conflicting/anisotropic sources
still fail physical scalar admission. Adding another declared unit/frame case
must require its own hook/declaration, not generic consumer edits. Real source
controls precede separate ordinary installed/public acceptance. No biological
accuracy, rooted ownership or merged/installed readiness is claimed here.

Exact shared dependency: Root's release/integration of any source_metadata.py,
runtime_spatial_graph.py and materialization/core.py unit-frame/projection hunk.
This checkpoint requests that boundary, not permission to alter their checkout
or merge whole394. Independent analysis declaration work can proceed after the
complete owner pass; original failed inputs and sourceguard remain protected.

Current independent continuation
--------------------------------

Dewey verified the complete immutable567 source archive8513 before releasing
this existing checkout: engineering567/build-input01/source8513.tar SHA256
02fe1abad6a2c1a74a9f0b6f9d54b289b9fc78b8214c9d4f38a9e5ca2e3c01a9,
original Git archive commit8513a7d2483ea09a2ec6b9e9f0193a5a16a56902.
No corrected567 wheel/native acceptance is inferred from that source archive.
The finished checkout switched back to this original541 branch, then normally
merged mainf2066ded at f542d411f39da7a477675bce3b3078518a40cf25. No conflicts,
foreign gitlink reset, scientific package or borrowed source change occurred.

Original Package parser source-family04 completes the relevant source evidence
at8513:704 OpenHCS +12 python-introspect +6 metaclass-registry +17 arraybridge
modules, zero parse omissions,11.187s/235.3MiB/Swap0/terminal0 under original
common CPU1/512MiB/60s limits. Complete selected ASTs include declarations,
inheritance, imports, constructors and reads/writes/consumer bodies; not just
the earlier textual source search. Evidence stays under the existing
engineering-neurite-units-20261003 root. JSONL SHA256
55eb03064f95b86b301c7ed46b82703340cd63bdb42f7239507cf041fc9b3ece.
These are preserved dependency source revisions, not installed-runtime proof.
This pass is prior8513 source evidence, not an assertion that every later main
or Root module is unchanged. No repeated global R1/OOM/test batch was run.

Determining current consumer contract: FieldSpec.from_dataclass_type derives
columns from original nominal fields; DataclassMeasurementColumnarRows does
not provide a unit-key renaming API. The shared numerical statistics and
topology therefore need physical/pixel declaration-owned row hooks, not raw
column replacement. Existing NeuriteOutgrowthCellResult falsely described
uncalibrated pixels under its _um fields. That source docstring is corrected
to the actual compiled physical contract; signatures, fields, numerics and
guard are unchanged. This is a source clarification, NOT the pixel feature.

Actual Root3940bca source contents were inspected: spacing unit remains only
MICROMETERS/RELATIVE; SpatialGraph carries coordinate_spacing and physical
radius but no explicit analysis/export unit. Its source_metadata/graph blobs
are d13f23bb/db26f654, different from8513, so no old-hunk reapplication is
claimed. Latest Root headf3c66cd7 remains separately owned. The narrow request
is public at394 comment5975214247; receiving status at541 comment5975217712.

Requested original-owner seam: explicit PIXELS member on SourceVoxelSpacingUnit
with no physical scalar projection; reused typed analysis spacing/frame distinct
from acquisition provenance; explicit graph analysis/export unit alongside its
existing scale/radius; original graph/ROI publication carries that declaration.
Original SWC admission retains the physical format contract. A pixel declaration
can select supported graph/ROI formats without inventing physical SWC units.
No source calibration relabel, copied units roster or generic consumer switch.

Singer's settings/measurement/topology continuation remains independently owned;
Root release/integration of that exact shared seam is needed for an end-to-end
pixel graph. No unused parallel analysis implementation or unsupported wrapper
has been added while this dependency is unresolved. Existing physical guard is
preserved;541 pixel route is still unimplemented and not installed-qualified.

Independent detector projection checkpoint
------------------------------------------

Current394f3c66cd7 file claims and all open PR titles/heads were rechecked.
No active analysis settings owner overlaps this hunk; Root's source metadata,
graph and materialization files remain untouched. Dewey builds567 from its
immutable8513 archive, not this reused checkout. #131's new uncertain revision
is preserved and is not a registration receiving input or replay authorization.

The existing settings now own their dimensional projections. Body maximum
width/minimum area live on MetaXpressCellBodySettings, outgrowth width on
MetaXpressOutgrowthSettings, and nuclear wavelength bounds on the existing
MetaXpressWavelengthSettings ancestor. Primary detection, nuclear propagation,
signal-body filling, neurite detection and the compact registered physical
recipe consume those hooks. Five dimensional expressions remain solely at
their five declaration hooks; the competing consumer expressions are deleted.
No settings mirror, units roster, decoder or second detection algorithm exists.

This is the working physical detector seam needed by the pixel continuation,
not a new registered pixel callable. Physical artifact admission, settings
fields/defaults, result headings, topology spacing and graph/export semantics
are unchanged. Root's analysis/export unit integration is still needed before
the pixel route can be enabled honestly. Analysis and export unit identity are
not inferred from numeric one or acquisition-relative calibration.

New-case source controls use declaration-only projection hooks through the
original body detectors and wavelength ancestor. Independent audit and width/
area capabilities compose with cooperative super and declared C3 MRO. The
compact physical callable must produce identical labels, physical rows and
graph for equivalent projected controls; no generic consumer edit is needed
for these new declarations. These controls have been authored after the
coherent owner change; qualification is pending at this source checkpoint.

Original complete8513 AST/dependency evidence remains applicable to the
unchanged underlying family; the determining two analysis modules differ from
8513 only by the prior physical-schema doc clarification before this hunk.
Changed-module AST and original pinned R0 will qualify this actual delta,
followed by a bounded focused source batch. No global R1, installed/public
pixel acceptance or autonomous scientific improvement is claimed.

Projection qualification at5dad36f88
-----------------------------------

Source19 controls PASS, terminal0,24.658s/364.2MiB/Swap0/OOM0, under the
unchanged common slice with CPU1/512MiB/60s. This includes the existing body
gate family, all three new primary/nuclear-seeded/signal-body declaration cases,
the shared wavelength detector's cooperative hooks, unchanged public signatures
and the original compact physical callable. Equivalent declared projections
produce identical body/outgrowth/nucleus masks, image/cell physical rows and
the complete spatial graph. The raw input is unchanged. New declaration/audit
capabilities compose through actual super calls; these are behavioral controls,
not merely inheritance assertions or word matching. No new registry or generic
consumer switch was required. The source bootstrap is the original runner from
the immutable567 archive, with the reused541 checkout explicitly selected.
This is source-runtime qualification, not installed-wheel/public pixel proof.

Before controls, the original Package parser parsed the current23-module
analysis family with zero omissions and retained complete changed-module ASTs.
Its installed tool source SHA03167cc1 is preserved; it is not the authoritative
ZIP's later parser blobdfdddeb7. Original debt_census.py SHA
fbe4651372d4d79963075d7fb6ba6dedf90d5e88e14eee07f845c5d836974e35
does match the authoritative ZIP. Its exact two-file R0 versus21e1ca313 has
ALL measured counts zero, code lines+16;0.682s/20.2MiB/Swap0/terminal0.
Prior full8513 consumer/dependency evidence remains separately retained.
No global R1 or unchanged Root dependency claim is made.

Original R0 invocation05 stopped before measurement because --json lacked its
required output path. Original controls05 stopped before collection because
the transient service lacked WorkingDirectory. Both terminal errors/raw logs
are retained unchanged. Corrected distinct R0 invocation06 and controls06
used the original tools/bounds; no assertion, test input or resource cap was
weakened. No fixture runtime was UNKNOWN and no native operation was submitted.
Two existing pytest config warnings remain in the complete original output.

Byte-exact changed source/tests, original parser caller/AST, both known harness
failures and final R0/control outputs are archived in
neurite-detector-projections-20261003.tar.gz,222071bytes,SHA256
ab3811ce8cfa42e672aa7fb6972f42182323a60dc89f9f99fd5718c9b817fd96.
Loose originals remain under engineering-neurite-units-20261003. The owned
terminal Numba fixture cache is2.1MiB there; no source, foreign ledger or prior
scientific evidence was cleaned or rewritten.

Remaining dependency is precise: Root394's analysis-unit-bearing graph/export
contract before a pixel registered route can publish unit-correct rows/graphs.
This independent settings checkpoint is working; it neither claims that shared
integration exists nor changes physical calibration admission. #567 still uses
Dewey's separate archived8513 candidate. Its public observation case awaits
whole-package qualification and positively observed original131 client/native
closure on6012; the newly retained uncertain revision is never replayed.

Current-main receiving checkpoint, 2026-10-04
-------------------------------------------

Normal merge7916ddad2c270c40177d3def81d62009cbb67464 integrates main7fb3c09b,
including accepted594 declaration descriptions, without changing the five
owned detector projections. Planck released the finished source checkout:
ordinary594 package/receiving uses its immutable private target and a different
source checkout. All six dirty foreign gitlinks, seventh gitlink absence and
untracked historical evidence are preserved. No new worktree, environment,
installation, native process, scientific input or author contact.

Latest NRA/refactor-audit skills and authoritative archive patterns were read.
Required relation remains distinct acquisition calibration versus declared
analysis/export units (IDEN-1/2), original typed spacing/graph/materialization
owners rather than mirrored units or raw field renaming (BOUND-2/8), and one
shared detection/topology recipe with declaration hooks rather than copied
procedures (IMPL-12). The working independent hooks remain on the existing
body/outgrowth settings and wavelength ancestor, not a new forwarding facade.

The original source-family04.py caller was reused unchanged against merged7916:
704 OpenHCS,12 python-introspect,6 metaclass-registry,17 arraybridge modules;
zero parse omissions, retained complete related ASTs and dependency identities.
Terminal0,12.46s,213532KiB maximum RSS, process swaps0. These are source
declaration/write/read/import/MRO facts, not global R1 or runtime acceptance.

Current18 focused source controls PASS, terminal0,11.53s,438776KiB maximum RSS,
process swaps0. Whole body-gate family, primary/nuclear-seeded/signal growth,
inherited wavelength cooperative hooks, original compact physical callable and
both public signatures are exercised. The unchanged source input, masks,
physical rows and graph equality controls remain intact; new declaration-only
capabilities execute their cooperative hooks without generic consumer edits.
This independently qualifies current-main integration, not a pixel route.
Original historical19-control receipt remains unchanged. Two existing pytest
configuration warnings are retained. Shared historical cgroup peaks are not
attributed to this test. No invented memory/swap cap was restored.

Exact current two-production-file R0 against main7fb3: every measured count
delta0, code lines+17. Original old-base code+16 receipt remains historical;
neither result is a global audit or a waived positive switch delta.

Determining shared dependency, not historical status
--------------------------------------------------

Actual Root394 head a0bb0f4089a85475e112cea32d60132c1cd94752 was fetched and read.
SourceVoxelSpacingUnit at source_metadata.py764 declares MICROMETERS/RELATIVE
only. SpatialGraph at runtime_spatial_graph.py190 still carries bare
coordinate_spacing and physical radii, with no explicit analysis/export unit.
The original ROI writer at processing/materialization/core.py3411 constructs
SourceVoxelSpacing(graph.coordinate_spacing), selecting its physical default.
The original SWC writer scales coordinates using the bare graph spacing.
Complete ASTs for these three actual shared modules are retained separately;
three parsed,zero omissions. This corrects the obsolete core/materialization
path in earlier receiving prose; its original record is preserved above.

Root remains the exclusive shared-file owner. The current narrow release or
integration request is394 comment5978234373, following5975214247; no release
or existing explicit pixel analysis frame was found in the inspected current
claims/source. The required hunk is original spacing-unit/graph/export behavior:
explicit pixel analysis unit without physical scalar calibration, typed analysis
spacing carried by graph/export independently of acquisition provenance, and
original physical SWC admission retained. Unit/format policy belongs on those
owners. No generic switch, alternate exporter, calibration1.0 bypass or unused
parallel measurement implementation is added while this seam is unavailable.

The registered pixel row/graph route remains unimplemented. This is the precise
Root dependency, not a hosted-CI, acknowledgement, test or package hold. After
the shared contract is integrated/released, Singer owns the single measurement
construction/topology consumer migration and source qualification; ordinary
installed/public pixel receiving then requires a released engineering lane.

Separate new source-projection witness
-------------------------------------

Read-only original BBBC007 log950..1166 in
next-bbbc00796-ownp00188-after593-20261004/BBBC007_PUBLIC593_96/author-workspace/
output/runtime/scratch/data/openhcs/logs/
openhcs_zmq_server_port_6016_1791102257189925629.log records first
PersistNuclei01 conversion failure before the writer. A01 has runtime_slice
size8 versus returned(4,450,450); A02 has RUNTIME_SLICE versus SOURCE_BINDING.
Original attempts/candidate01_first.py and failed job remain untouched.
ImageOutputRecorder.record reaches contextualize/output_owns_source_context,
then ImagePayloadMetadata.has_complete_source_identity and plane validation.
This identifies the determining boundary, not the earlier wrong producer.
No guard is weakened and no original request is replayed.

Those five related Root production modules materially differ from installed
main7fb3. Current Root reproduction/fix is NOT claimed. Dewey combined this
witness with the existing P001 source-assembly observation in the SAME
Root394 comment5978205597; there is no duplicate issue/patch or scientist
feedback. It is distinct from541's unit-bearing graph dependency.

Current raw controls/source evidence is archived separately in
neurite-current-owner-controls-20261004.tar.gz,4910507bytes,SHA256
a03ddd1f91be288d3d0cb7604df8aedaeb7d094415d8b925d4e6f37728885b49;
the original earlier archives,
failures and loose originals remain intact under engineering-neurite-units-
20261003. The current source checkpoint changes no shared Root implementation.

Current unit-owner continuation after522 source repair
-----------------------------------------------------

522's coherent repair is published atd4ff1cbbf; Planck explicitly uses its exact
Git export and holds no mutable source checkout borrower. Singer reuses this
same checkout for541, normally integrating mainb461 at221357aca without conflict.
Eight foreign gitlink worktrees and all untracked evidence remain unchanged.
Active727's declared files do not overlap this unit/graph/materialization family;
closed394 is not a continuing exclusive claim.

Original Package caller source-family04 was reused, not copied into a new
scanner. Current source-family08.jsonl parses702 production/12python-introspect/
6metaclass-registry/17arraybridge modules with zero parse omissions; terminal0,
9.59s/208644KiB maxRSS/process swaps0. Full related ASTs and exact dependency
Git identities are retained under engineering-neurite-units-20261003; SHA256
72fbefe68c7ae93c99ed435bba870bf38d1d03fc8ba3a11dcdd953d0c87d8038.
This is source evidence, not current installed dependency or global R1 proof.

The registered pixel-rooted route remains unimplemented. The next owner batch
must distinguish analysis metric units from acquisition/native calibration:
SourceVoxelSpacing owns declared units; SpatialGraph still carries a bare
coordinate_spacing tuple and physical radius convention. The ROI writer builds
SourceVoxelSpacing(graph.coordinate_spacing), implicitly asserting micrometers;
SWC also exports scaled coordinates/radii without unit admission. A pixel
analysis must not relabel an acquisition's spacing, assert1um, or silently emit
physical SWC. Settings, hidden input/provider, measurement rows, graph and both
export consumers must use the same declared coordinate contract and shared
analysis implementation. The original physical negative remains required.
No541 production edit, test, package/runtime action or scientific feedback is
claimed by this continuation checkpoint; semantic consumer review is active.

Working typed graph/export checkpoint, 2026-10-05
------------------------------------------------

This is an implemented source checkpoint, NOT a freeze-ready registered pixel
analysis route. The production delta adds PIXELS to the original
SourceVoxelSpacingUnit declaration. Its member-owned physical projections return
no calibration; SourceVoxelSpacing.require_physical_coordinates rejects pixel
and relative SWC exports. Physical anisotropic coordinate export remains valid;
the existing physical scalar calibration guard remains unchanged.

SpatialGraph now composes SourceImageProvenanceFields and SourceVoxelSpacingFields
with NamedArtifactPayload. Its required coordinate_spacing is the original
SourceVoxelSpacing value, expressing the analysis metric. Inherited acquisition
spacing remains a distinct fact. Graph contextualized_source_metadata owns the
one source-plane/provenance/calibration binding recipe; the artifact consumer's
copied projection/replacement is deleted. All current production and test graph
constructors use the nominal spacing. The old provenance-only hook is deleted;
no tuple compatibility reader, unit mirror or alternate graph writer exists.
Historical frozen receiving drivers remain unchanged, not current consumers.

The existing graph ROI writer uses inherited acquisition calibration rather than
reinterpreting analysis spacing as micrometers. SWC uses the analysis owner's
physical admission. The physical neurite producer explicitly declares its actual
micrometer metric. Source coordinates, graph node/edge identity and geometry are
unchanged. Independent ProjectionAudit capability executes the cooperative graph
hook through super; no generic artifact/writer edit is needed for that case.

Original graph-unit-controls09 ended before collection, terminal2: the borrowed
foreign PolyStore checkout lacks TiffPhotometric. The unchanged original runner
then used the qualified receiving16 read-only PolyStore backing and startup API,
without any install or foreign source edit. Distinct graph-unit-controls10 passed
27 controls, terminal0,3.83s/250072KiB maxRSS/process swaps0. These exercise original
graph/SWC/ROI behavior, both nonphysical export negatives, pixel analysis with
physical acquisition calibration preserved in the real ROI archive, source
projection and the independent cooperative hook. Two existing pytest config
warnings remain. Original failure and complete output are preserved.

Source evidence preceding this owner batch is complete source-family08 above,
not global NRA/R1. After-source family and five-path original R0 are the next
source qualification; no inherited512MiB cap has been imposed. Applicable current
catalog patterns are IDEN-1 (two distinct metrics), BOUND-2 (existing spacing and
metadata owner), IMPL-2 (unit member behavior) and IMPL-12 (deleted projection
recipe). The historical archive's BOUND-8 references are not current catalogue IDs.

Exact controls/logs live under the existing engineering-neurite-units-20261003
receipt root: graph-unit-controls09.stdout/stderr and
graph-unit-controls10.stdout/stderr. No original negative was overwritten or
replayed. No wheel, installed pipeline, native/viewer or biological claim.

Remaining implementation is explicit: registered neurite analysis still requests
the physical pixel_size artifact and emits physical-only row/edge headings. Its
default materialization includes physical SWC. These input/provider, row schema,
metric computation and export declarations must be closed together before an
uncalibrated compiled pixel route is supported. This checkpoint does not bypass
that guard with1.0 or claim a pixel route through direct function invocation.

Independent522 source-owner rendering disposition
------------------------------------------------

Read exact OWNER-PUBLIC-ACCEPTANCE16.rst and original Napari Shapes code at the
existing paired dependency root. Shapes._outline_shapes constructs a separate
selection outline from edge centers plus normalized_scale_factor times highlight
width times edge offsets. VispyShapesLayer._on_highlight_change renders those
triangles into shape_highlights, separately from shape_faces. Selected geometry
therefore has a presentation overlay that disappears when deselected.

The retained three native PNGs and ordinary presentation-only deselection show
that separation: the compact polygon remains aligned while the yellow highlight
disappears, without source-row reselection or retirement replay. A concrete data
geometry/remount regression is not demonstrated. The expected selected-overlay
explanation is source-backed; the exact star silhouette is not an assertion of
unchanged native vertex arrays, which the public contract does not expose.

Accept the installed-live contract demonstrated by receiving16: extent3->2,
A03 ordinal2->1, Points selected_data[1] and Shapes[3] retained, source/frame and
immediate pre/post camera retained. Canvas428->426 pixels and the occluded before
outline preclude a fixed-canvas/pixel-identical renderer comparison. These limits
do not block the working retirement workflow or justify another source patch.
All originals are closed and sealed; no new client or uncertain operation replay.
