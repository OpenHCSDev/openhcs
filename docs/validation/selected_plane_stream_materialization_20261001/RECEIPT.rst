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

Source qualification -- completed; installed acceptance pending
---------------------------------------------------------------

Issue https://github.com/OpenHCSDev/openhcs/issues/395; draft PR397
https://github.com/OpenHCSDev/openhcs/pull/397. Named source owner Lorentz;
integration/installed acceptance owner parent. Reviewed production35d730c1743ea51ba40951e04fda31625f828429
is byte-identical after ordinary main49a95d8fb3da8ecb3dc4c1323332bd48b345f42e
merge bdd3c2d6a95b5c571cd2df5da204d877cfdfaf99. This receipt's containing Git
commit identifies the final evidence publication; no self-referential head hash.
Production SHA256 ae17fab8b22e216c23a3d3b55bcba5d7a8fdbc504a4435c82b0ba8d9380e9c3f.
Only production path is projected_image_output.py; new regression tests and
reproducibility evidence are the other changes. No PR394-owned paths changed.

Original red, public-path persistence and real SHM proof
------------------------------------------------------

Original installed execute71243f96-be49-4fb5-b3b2-65507d868498 failed19:02:57UTC;
parent ASSISTED-2-MATERIALIZATION-DEFECT.rst remains authority, science rejected
independently. New synthetic uses actual public neurite checkpoint declaration,
FunctionOutputContextStrategy, real TIFF disk saving and actual viewer backend
kwarg/materialization path; intercept ONLY transport batch sending(no server).
red.xml/log:1failed SOURCE_BINDING with exact original singleton error,1passed
RUNTIME_SLICE control. green-initial.xml/log:39passed. expanded-third.xml/log:
49passed including original projected-image and strict singleton missing/ambiguous
and multi-varying component rejection controls. Two failed fixture iterations are
retained: expanded-first passed48/failed1 (measurement rows lacked original
FunctionOutputContextStrategy conversion); expanded-second passed48/failed1
(fixture omitted MemoryStorageBackend). Both repaired in test construction only.

The new public declaration regression derives all12 ArtifactOutputPlans from
CallableContract.from_callable(neurite_outgrowth_metaxpress).artifact_outputs.
Original FunctionOutputContextStrategy, RuntimeValueStore, FileManager and
materialize_artifact_outputs persist all12 actual files (measurement/labels/QA/
graph), with no mocked materialization or disk storage. Five selected-plane QA
streams retain channel2, source name FITC, calibration1.3556 and actual2Dpixels.
Original StreamingBatchMessageBuilder allocates real SHM; each transmitted array
is read through its exact SHM handle and equals the persisted TIFF. Exact SHM
allocations are closed/unlinked through the existing backend cleanup. Only the
final viewer transport batch send is intercepted: this is NOT native/live-viewer
acceptance and no scientific callable or biological sample is executed here.

Eight generic cases exercise channel/site/z_index/timepoint declarations with
singleton and reordered two-plane selection. Independent DeclaredCrop leaf
composes ObservedSelection and ReversedSelection capabilities with the owning
PlaneDeclaration/SourceProjectedImageOutput ancestors. Actual shared consumer
behavior calls cooperative super hooks in observe/reverse/declaration order,
retains reversed source names/components, and leaves pixels unchanged. No edits
to generic consumers are needed to add this declaration/capability composition.

Complete scoped controls and preserved baseline failures
--------------------------------------------------------

current-main-controls.xml/log:350passed after main merge, comprising:

* focused selected/projected/strict-stream controls:49;
* materialization_core, function_artifact_materialization,
  cellprofiler_full_stack_materialization:143;
* runtime_slice_projection, image_plane_contracts, function_artifact_outputs,
  source_image_provenance, multi_template_matching:156;
* exact existing napari declared-component and mixed-aggregate rejection nodes:2.

Final bounded serial qualification reruns the identical350 test identities with
unrelated installed pytest plugin autoload disabled (no assertions/fixtures/
production dependencies removed). Explicit repository conftest and actual ABI/
materialization/storage/SHM owners remain in use. Each following shard exited0
with monitor reason=None; XML identity union equals current-main-controls exactly
and has no failures/errors/skips:

=============================  =======  =======================  ==========
Receipt stem                   Passed  Peak aggregate RSS KiB   Elapsed s
=============================  =======  =======================  ==========
bounded-no-autoload             49       440236                   8.440
bounded-materialization-core    57       516556                   10.996
bounded-function-artifacts      65       309184                   7.697
bounded-cellprofiler-stack      21       319944                   5.331
bounded-image-contracts         156      270836                   6.956
bounded-viewer-controls         2        467524                   9.551
=============================  =======  =======================  ==========

Peak observed total includes exact child process group and monitor; maximum
516556KiB is below512MiB (524288KiB). CPUQuota100% and outer60s guard remain.
No asynchronous cases occur in this enumerated scope; unknown asyncio config
warnings from disabling unrelated plugins are retained, not suppressed.

These are the complete enumerated adjacent scopes, not a whole-repository suite.
The earlier individual shards/logs are retained, not counted again as unique tests.
neurite-output-controls.xml/log (neurite_outgrowth + function_outputs):125passed,
21failed. run_original_projection.py loads only the original base91dc52 projected
module in memory before running the identical source shard. neurite-output-base
reproduces all21 same test identities/messages, with125passed and zero candidate-
only failures. Failures are unchanged numerical/CellProfiler-adapter unpacking
errors ('too many values to unpack (expected 3)'), not fixed or hidden here.
Unique observed scoped outcome:475passes/21same-base failures. No assertions in
existing tests were weakened, and no scientific implementation was modified.

Original R0 and precise R1 coverage limits
-----------------------------------------

Unmodified CI-pinned agent-comms3b03785f45df2ef5dc62ba6aed99294192ecbb01
packaged debt_ratchet.py SHA256
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562
was verified against its retained Git object. r0.json compares initial base91dc52
to35d730c. r0-current-main.json compares current main49a95 to merged bdd3c2d6a:
exit0,5163metrics, no increases, exact sole changed production path. This is the
original packaged R0 over the changed openhcs production surface, not a global
refactoring audit of unrelated roots/tests/evidence.

R1 is BLOCKED, not passed/waived. Current NRA9c4546964e899d06c74c896143b083f6b343da24
does not export RedundantTypeCheckDetector required by original policy.
r1-original.stderr.txt preserves the first original-policy invocation selected by
the initialized artifact315 cwd (older policy hash33d2; NOT worker-exact).
r1-exact-policy.stderr.txt preserves corrected absolute current worker policy
scripts/check_refactor_r1.py SHA256
4c6282f52e7c188068dd9d63399f5522a7cb1d222504d0c0b809be10303884ca.
Both fail at import before scanning/staging any surface. Empty stdout JSON files
are failure receipts, not zero findings. CI-pinned NRA0844525ecaba is unavailable
in the local cached Git objects; no install/download/fetch of dependencies was
performed. The separate current NRA CLI request targets only the changed production
file with tracked openhcs context (702 Python files), one parse/analysis worker,
raw full JSON. nra-current-full.json reports complete:false, deadline_exceeded:true,
stage contextual_global_prepare:closed_parameter_conveyor, internal20s deadline,
finding_count:null, deadline_incomplete. Outer60s guard was not the deadline hit.
There is NO completed scan/findings inventory or whole-dependency audit claim.
Preserve existing issue357/policy integration boundary; this receipt grants no waiver.

Execution/resource boundary and retained ownership
-------------------------------------------------

All tests use the existing private parent interpreter and readonly installed
extension ABI files, with source imports asserted by original source_shard.py.
Source PYTHONPATH is this worker root, not installed production. Serial CPUQuota
100%, MemoryMax512M, outer60s scopes; owned basetemp/cache remain beneath the
preserved storage_cleanup_20261001 with selected-plane prefixes. No process/native
slot, installation, environment, submodule or frozen science mutation.

IMPORTANT: cgroup charging did NOT prove the requested actual512MiB RSS limit.
Original time receipts explicitly show materialization143 peak534796KiB,
current-main350 peak590324KiB, candidate neurite711152KiB, original neurite634496KiB,
and incomplete NRA533512KiB. Those over-bound observations are retained and are
NOT resource-qualified, despite passing test assertions where applicable. Initial
focused49 peak496008KiB, image156 peak480948KiB, viewer2 peak482512KiB;
original R0 current-main peak88284KiB. No run exceeded60s elapsed.
run_bounded_source.py adds aggregate exact child-process-group + monitor RSS
observation (512MiB) and58s execution/2s shutdown allowance. The first combined
focused current-main retry was terminated at aggregate533348KiB; its original
log/resources remain. bounded-public-path.xml has12passing assertions but its
process was terminated during cleanup at528328KiB; it is NOT a bounded success.
bounded-current-main-controls records an invocation error (wrong viewer test-file
path, exit4, no tests), retained rather than overwritten. Corrected combined
bounded-main-qualified was terminated at534340KiB; combined bounded-materialization
at524708KiB. These are resource failures, not scientific/test passes. Splitting
by actual existing test-module owners and disabling unrelated plugin autoload
produced the final bounded350 controls above; no limit was raised or assertion
weakened. Earlier over-bound baseline/NRA observations remain outside resource
qualification, not hidden by the successful final source shards.

Parent owns installed serialized acceptance when the canonical native/viewer slot
is released. This source handoff establishes synthetic persistence/SHM behavior,
not an installed/live claim or biological acceptance. Assisted candidate rejection
and all frozen biological dispositions remain terminal/unmodified. Protected
storage cleanup evidence, source refs, prior PR378 evidence and parent environment
remain intact. No redundant source/evidence archives were created.
