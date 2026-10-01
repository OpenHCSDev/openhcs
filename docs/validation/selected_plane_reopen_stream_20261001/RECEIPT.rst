Persisted selected-plane display projection: PR397 paired with PR399
==================================================================

Lorentz owns image-stream request declaration behavior; Singer owns PR399 metadata
inventory/reopening. Parent owns integration/live acceptance. Original ad6baa4ef
receipt and protected storage_cleanup_20261001 evidence remain unchanged.
Ordinary merge of3997b38bb013 is dependency integration, not a competing patch.

Witness: installed8d0480ef stream007 terminally failed at strict
NapariAggregateAxisBindingAuthority.bindings, absent plane_component_values.
Original checkpoint has explicit SOURCE_BINDING metadata with exactly one runtime
provenance plane. Manual source image loading preserves it, but forwarded pixel
shape(1,H,W) still exposes a payload-local axis without a varying component domain.
Fixed channel2/FITC is source identity, not proof of a varying pixel component axis.
Original parent request/response/log and exact viewer incarnation remain unchanged;
parent already closed the exact failed viewer. No native/science replay.

Target: original ImageStreamingRequest owns display projection after its original
window admission. Exact persisted plane_axis plus runtime provenance count1 is
the proof; original RuntimeSliceProjection validates shape and projects scalar
pixels/metadata/masks. Its FullWindowImageStreamingRequest leaf retains cooperative
full native-window validation before display projection. Multi-plane/undeclared
axes are not inferred from ndarray rank, filenames or fixed channel identity.
Generic StreamingService calls the request owner; strict viewer/stream guards,
PR394 projection owners and Singer metadata handler remain unchanged.
Patterns: IMPL-4 shared ancestor/minimal hooks; BOUND-2 original projection owner;
IDEN-1 source identity vs payload axes; no TIME-1 historical reader or rewrite.

Working source checkpoint. New real-disk -> public inventory/service ->
real-SHM builder -> original packet decoder -> exact strict receiver binding
regressions cover explicit singleton axes and independent plain persisted TIFFs.
Only lifecycle and final transport endpoints are replaced, never pixel loading,
metadata declarations, message construction/decoding or receiver axis validation.
Source tests run serial1CPU/512MiB/60s with the existing readonly interpreter and
ABI. No install, provider, environment, shared production or scientific edits.

Working implementation and behavioral evidence
----------------------------------------------

Original ImageStreamingRequest now owns image_plane_projection (the minimal
declaration hook) and inherited project_image (one shared dispatch to the original
RuntimeSliceProjection family). StreamingService replaces its existing append
with request.project_image after original require_image_window; no case switches
or new consumer fallback. FullWindowImageStreamingRequest keeps its existing
super call and exact native-window check before display selection. No code was
added to SourceProjectedImageOutput, runtime projection owners, stream projector,
receiver guard or microscope399 owner. Scalar provenance/channel/calibration,
mask/color semantics and exact source spatial domain survive the original slice
projection; saved TIFF and metadata SHA256 remain unchanged during reopening.

red-source-binding.xml/log reproduces the exact original strict receiver error
through real SHM and original packet decoding:1failed, peak522264KiB/10.488s.
green-native-final:3passed for both declared plane-axis members and scalar2D
native output; peak521788KiB/9.589s. green-plain-tiff-final:1passed, peak521412KiB/
9.318s, independently reads ordinary TIFF through native ImageXpress HTD/folder
declarations, without any saved image_metadata/OpenHCS workspace document.
It retains actual calibration0.5 and nondefault Z5/timepoint3; no default identity.
Exact newly allocated SHM names are closed and absent after backend cleanup.

request-controls-final:15passed, peak189256KiB/3.182s: singleton masks and RGB;
multi-plane preservation; undeclared arrays not inferred; absent runtime-plane
provenance not fabricated; conflicting native shape rejected by original axis
proof; independent PhysicalCalibration and ObservedProjection capabilities on
new CalibratedFullWindow leaf exercise cooperative super/MRO with the original
native-window ancestor and shared display projection. Wrong full-window origin
remains rejected before capability/projection side effects.
original-core-streaming:39passed, peak496916KiB/9.434s;
original-reopen-inventory:8passed, peak262864KiB/5.842s;
strict-plane-guards:37passed, peak242392KiB/4.882s.
This checkpoint has103completed passing controls, not a whole-repository claim.

Rejected source/fixture attempts retained
-----------------------------------------

red.log first combined attempt exceeded aggregate527308KiB before XML completion.
fixture-diagnostic has1new-fixture failure: expected physical rather than original
inventory-owned virtual stream path. The expectation was corrected to the exact
SourcePixelRef backend address. green-native had3new-fixture failures: the viewer
codec intentionally excludes hidden full provenance, so FITC is now asserted on
the original projected source metadata before that codec, not invented on wire.
request-controls had13passes/2new-fixture failures (canonical component domains
are strings, not the fixture's integer expectation); exact string values are
now checked. No existing production assertion was weakened.
green-plain-tiff passed its assertion but exceeded528748KiB during cleanup; that
run is not resource-qualified. Removing an unrelated imported broad test fixture
and retaining a direct native plain-TIFF fixture produced the final bounded pass.
original-streaming-controls combined shard exceeded526992KiB; no pass count is
claimed. original-agent-streaming exceeded527900KiB after6 test progress markers
when entering existing Java-backed BioFormats auto-detection/plane controls.
That native-backed test path was entered, not completed; this receipt does not
claim those tests passed or that their native initialization was absent. No
application native worker/viewer or scientific job was launched; the bounded
source process group exited, with no surviving owned test/Java process observed.
Final agent-service qualification separates that path from the CPU-only source
scope instead of raising the bound or modifying its assertions.

Original changed-path qualification and owner correction
--------------------------------------------------------

Ordinary current-main merges6e8bbc28 and32d7a6ec are retained. Final source revision
32d7a6ec49e4a7b995586f9d464353ddb2e00d60 includes main
e3765e3534b009f09413c7c5bfc35d072030a704 (merged399). Original pinned R0
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562
first FAILED against c4be/6e8: the only positive among5177 comparisons was
ForeignAbsenceProbe +1 at the new request's metadata.plane_axis absence check.
r0-current.json/stderr/resources preserve that original failure, not a waiver.

Parent-directed, PR394-coordinated original-owner correction moves the exact
singleton declaration/provenance proof construction onto ImagePayloadMetadata.
ImageStreamingRequest.image_plane_projection delegates to its rich nominal
singleton_plane_projection hook. Its inherited project_image algorithm and
original RuntimeSliceProjection remain unchanged. No absence check is renamed,
aliased, hidden in a local, or replaced with ndarray inference. Two identical,
overwritten definitions of from_mapping and retained_plane_component_values are
reduced to one unchanged implementation each on their original metadata owner.
That removes duplicate authority without a new metadata carrier or facade.

r0-owner-final PASS: all THREE current-main production paths (projected_image_output,
runtime_image_values, viewer_streaming_service),5177 comparisons, zero positive
deltas. ImagePayloadMetadata GodClassExcess decreases14; StringSubscript decreases2.
Original GodClass scope also inventories unchanged production declarations, as
the unmodified packaged ratchet requires; this is a structural guard, not a
formal semantic equivalence proof. Original policy and measurement authority
were not patched. CPU100%,512MiB cgroup,60s outer bound; elapsed15.07s.

New owner-hook-controls:104passes/307184KiB aggregate RSS/8.359s, comprising the
complete request, persisted-metadata, image-plane and runtime-slice modules.
Independent CalibratedMetadata leaf composes ObservedProof and PhysicalProof
with ImagePayloadMetadata; actual cooperative super hooks execute in order
through the unchanged shared request, preserving exact pixels/masks/FITC/1.3556.
The earlier independent request-capability/full-native-window control remains.
Original remaining agent-service CPU-only scope:14pass/2deselected,262256KiB/5.450s.
The exact exclusions are test_inventory_source_projection_loads_exact_ome_stack_planes
and test_inventory_source_projection_loads_exact_ordinary_tiff, which enter existing
Java-backed autodetection; they are not reported as qualified or weakened.
Original whole12-output/real-SHM module:12pass/445912KiB/7.983s on current-main6e8.
Completed unique controls now218, with overlaps counted only once. Final production
32d7 source confirmation: owner-public-native3pass/521860KiB/9.514s;
owner-plain-tiff1pass/521164KiB/10.346s; owner-all12 module12pass/446120KiB/8.960s.
These confirmations do not add duplicate identities to the218-control total.
The original public disk/SHM/packet/strict-receiver path, independent native TIFF
declaration and all12 public artifact outputs/five exact QA streams remain working
after metadata-owner promotion. No further source controls or native run are needed
for this finite checkpoint.

Fresh canonical NRA83b05d1f exact policy still failed before analysis at its missing
RedundantTypeCheckDetector export. No detector/policy stub or compatibility import
was introduced. Its separate three-path CLI attempt with full OpenHCS context
hit the strict512MiB aggregate RSS bound at525588KiB/19.108s, before a completed
JSON report. Those are retained failure receipts, not zero findings or full R1.
Parent identified existing original-API baseline NRA673c062fc656e9c74f1eddcab30f036c9befbc1f;
read-only imports of both original detector declarations succeed with the existing
interpreter. Unmodified exact policy then reaches its original source-owner
validation and refuses this worker's uninitialized external/ObjectState; that
separate failure is retained (211200KiB/3.549s), with no initialization or install.
The complete-context policy run uses existing read-only initialized Git source
owner /home/ts/wt/openhcs-input-parent-integration-20261001, with the same Git common
directory and exact same committed base/head, writing only this worker's declared
scratch. All eight exact head gitlink commits are present in their original
child repositories; no source/environment/package metadata was changed there.
Original policy roots are openhcs/scripts/benchmark plus recursive recorded Git
dependencies, and report selection is exactly the three changed production paths.
The strict source-group watchdog ended that unmodified policy at its58s execution
allowance (2s reserved for shutdown):212036KiB aggregate RSS, process group exited.
No before/after NRA count, detector finding report or completed descent certificate
was emitted. There was no phase-completion marker; this receipt does not infer
whether staging/preparation or analysis held the process at shutdown. R1 remains
BLOCKED at the bounded complete-context attempt, not a pass, waiver, API workaround
or complete scoped audit. The earlier canonical API failure is independently
distinguished from this API-correct source run. Parent retains the broader bounded
R1 preparation/tooling follow-up; issue395's finite materialization/display defect
does not turn into a global NRA qualification or a biological acceptance claim.

Final artifacts and reproducibility
----------------------------------

Production is frozen at32d7a6ec49e4a7b995586f9d464353ddb2e00d60; subsequent commits
contain evidence/documentation only. Actual SHA256 values:

* projected_image_output.py: ae17fab8b22e216c23a3d3b55bcba5d7a8fdbc504a4435c82b0ba8d9380e9c3f
* runtime_image_values.py: 356f4ffa469383fa0989a4da4f59c9c1ea07591ad9d4c7e8dac8efca691e5665
* viewer_streaming_service.py: 6bec8b5cb7052d118d7d44fd308721bc055dd48c998565728bf09ad0c1fb556a

All72 raw logs/XML/JSON/resource receipts, including every rejected fixture/resource
attempt and both original failed/final passing R0 runs, are byte-exact members of
raw-evidence.tar.gz. Archive SHA256:
e9a10347805e3e334c0783b742136328430389ff2abd9932ace08779bbfe28b8.
RAW_EVIDENCE_SHA256.txt indexes each member's original complete worker-relative path
and SHA256. ARCHIVE_COMPARE.txt records successful native tar byte comparison,
exit0. ARCHIVE_SHA256.txt authenticates the archive. Versioned raw duplicates were
removed only after comparison; originals remain on this worker's disk and in prior
Git commits. No raw evidence whitespace or assertion was edited. Extract the archive
into a separate persistent review directory; member names are workspace-relative.
Original selected_plane_stream_materialization_20261001 evidence, biological freeze,
storage_cleanup_20261001 receipts and parent/Singer sources remain protected.
MANIFEST.json records exact source/tool authorities and finite acceptance boundaries.

Installed boundary
------------------

Parent reports fresh installed229 transport and bitmap acceptance with original
channel2/FITC/1.3556, uint8[1024,1024], then an explicit binary0..1 display window.
Parent evidence: PR397 issuecomment5941295091 and retained
paired397-388-installed-20261001/reopen399-projected-binary-review/REVIEW.json.
That installed acceptance belongs to exact229 bytes, not the later source-only
metadata-owner correction. Final9a3/32d owner promotion installed byte/live acceptance
is explicitly PENDING the next parent-owned safe milestone. Parent's handed-off
viewer2339091/create1790890853.17
and subsequent assisted science remain parent/Dalton-owned. No private install,
native/viewer launch, scientific callable change or biological replay by Lorentz.
Original007 failure and frozen/rejected biological records remain unchanged;
this source receipt establishes no biological acceptance or autonomous success.
