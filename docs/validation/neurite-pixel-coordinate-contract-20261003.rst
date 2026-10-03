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
