Selected-plane streaming/materialization -- Lorentz -- issue395
==============================================================

Base source91dc52d4040890e1b88494acba7368196f6cd1e8; ordinary new branch
fix/selected-plane-stream-materialization-20261001 in existing persistent WT.
Original storage_cleanup_20261001 receipts are preserved/untracked. No reset,
newWT/environment/install/download/native/science/provider operation.
Read nra-refactoring SKILL.md and authoritative refactor-audit.skill archive
entry, patterns README, implementation/identity/boundaries and surface receipt
in full. Exact-patch semantic implementation, not a claimed native DSL proof.

Boundary and ownership decision
-------------------------------

Original selected-plane declaration retained a leading singleton SOURCE_BINDING
axis after selecting one input plane. StreamImagePayloadMetadataProjector correctly
requires an exact component for any payload-local pixel axis; the empty artifact
storage axis tuple cannot supply one. Source provenance of a singleton cannot
prove which fixed coordinate formerly varied. Inferring CHANNEL/default identity
or suppressing the projection check would violate that contract.

SourceProjectedImageOutput now owns inherited selection validation and source
context transformation. SelectedPlaneImageOutput supplies only its exact ordered
index hook and with_data reconstruction. One selected plane consumes its leading
axis through the existing ImagePayloadMetadata.for_leading_source_plane owner and
returns actual2Dpixels. Multiple selected planes retain their ordered axis and
provenance. No separate selection metadata, registry, compatibility path or viewer
case switch. The former leaf implementations are deleted, not copied alongside.
IMPL-4/IMPL-12 shared procedures belong to ancestor; IDEN-1 pixel vs storage axes
remain distinct; BOUND-2 existing metadata projection is used, not reconstructed.
The scientific callable's raw selected outputs and pixels are unchanged.

Crossing: PR394 owns materialization/core.py, runtime_image_values, projection,
function_artifact_materialization and adjacent tests. No edits on those paths.
Production change is only openhcs/core/projected_image_output.py; strict stream
projector unchanged. Parent coordination was explicit in the working commentary.

Original red and first green
----------------------------

Original installed execute71243f96-be49-4fb5-b3b2-65507d868498 failed19:02:57UTC;
parent ASSISTED-2-MATERIALIZATION-DEFECT.rst remains authority, science rejected
independently. New synthetic uses actual public neurite checkpoint declaration,
FunctionOutputContextStrategy, real TIFF disk saving and actual viewer backend
kwarg/materialization path; intercept ONLY transport batch sending(no server).
red.xml/log:1failed SOURCE_BINDING with exact original singleton error,1passed
RUNTIME_SLICE control. green-initial.xml/log:39passed including original strict
singleton missing/ambiguous and multi-varying component rejection tests.

Bounds: existing private parent interpreter and readonly ABI extensions; source
imports asserted in original source_shard.py. Serial oneCPU512MiB60s cgroup
source shards, owned persistent basetemp/cache roots. Headroom16.9GiBRAM;
disk warning preserved, not a reason to add environments/heavy workers.

In progress / not yet accepted
------------------------------

Independent leaf/cooperative MI behavioral proof; all12declared-output persistence
and selected-plane QA stream identity/calibration; complete related source controls;
original packaged R0 and scoped R1 evidence. Draft checkpoint is not an installed,
native/viewer/biological acceptance. Parent owns installed acceptance when Dalton
releases canonical5993/5992; live391/383 and frozen trials remain unchanged.
