Integrated rooted neurite analysis: missing pixel-unit contract
=============================================================

Status and ownership
--------------------

Singer owns the analysis declaration/unit boundary investigation and fix.
Root394 retains shared source metadata, runtime graph and materialization files;
no shared production hunk has been released for this task. Parent owns future
installed/public acceptance. No scientific author contact or live operation.
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
