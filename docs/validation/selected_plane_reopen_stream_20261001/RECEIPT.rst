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

Qualification still to publish with this checkpoint
---------------------------------------------------

Fresh whole-changed-production-path original R0, precise scoped R1 disposition,
current-main merge and remaining bounded adjacent source controls. Installed
source8d0480ef failure is NOT replayed or accepted by this source checkpoint.
Parent owns serialized installed acceptance; biological records stay frozen.
