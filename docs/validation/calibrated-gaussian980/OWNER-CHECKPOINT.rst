Calibrated Gaussian source-axis owner checkpoint
==============================================

Issue980 preserves the original receiving25 failure and author source. No
original execution is replayed or scientist prefix changed. This branch starts
from actual merged main c882d5edc67bffe7ec7f2eb3a2eeb7fe64e9415a in the reused
finished context-bounding checkout; foreign gitlinks and keepers are preserved.
Current normal-main integration and capability ownership supersede that initial
base as recorded in the final section below.

Determining cause
-----------------

GaussianFilterModule declares FLEXIBLE/FULL_STACK. Its raw implementation
passed total pixel rank to SourceVoxelSpacing.spacing_for_ndim. The supplied
SITE/Y/X cohort therefore requested three physical spacing values for a
calibrated two-dimensional source. This also let uncalibrated multi-site
arrays blur between sites instead of representing independent images.

SourceSpatialDomain.spatial_rank already owns intrinsic Y/X versus Z/Y/X.
VolumeSourceSpatialDomain.admit_source_cohort promotes explicitly declared
volume cohorts through the existing source-binding and main-flow loaders.
ImagePayloadMetadata already owns channel-axis normalization and spatial Y/X
placement. Its new spatial_axes projection consumes these same declarations;
Gaussian derives its sigma vector from that projection with zero smoothing
on nonspatial axes. No new stored axis/domain facts, execution mode, codec,
spacing fallback or reader relaxation is introduced.

Owner and consumers
-------------------

The pre-edit refactor-audit measure_source/AST pass parsed twelve relevant
production modules without omissions: runtime_image_values, source_spatial_domain,
source_metadata, runtime_plane_projection, aligned_image_payload, source_bindings,
source_binding_selection, steps/function_runtime, callable_contract,
interop/cellprofiler/runtime/function_contract_execution, Gaussian and shape.
Dynamic contract selection was read semantically; AST is not a runtime proof.

Both source-binding load and main-flow load admit the original cohort domain.
Full-stack projection retains that metadata. SourceVoxelSpacing continues to
reject physical rank greater than its declared calibration. Viewer coordinate
scales and object feature spacing are separate existing consumers, unchanged.
Shape feature spacing applies to its physical label-image geometry, not this
Gaussian full-stack source-cohort dispatch. Gaussian's competing total-rank
decision is deleted. No active #973/#977 file overlaps these two source methods.

Acceptance boundary
-------------------

Source qualification is complete at the published checkpoint below. Installed
public compile/execute qualification remains pending; the draft is not claimed
merge-ready.
Required controls: calibrated singleton SITE/Y/X; multiple independent sites
with no cross-site smoothing; anisotropic declared intrinsic Z/Y/X parity;
SITE/Z/Y/X and declared channels; original metadata/provenance and mask
preservation; strict missing physical-Z spacing and invalid channel/rank
rejection. The ordinary installed public MCP compile/execute and persisted
result check use a separately recorded synthetic engineering destination,
not the original scientist or receiving25. No merge readiness is claimed yet.

Qualified source checkpoint
---------------------------

At the initial qualified checkpoint, production bytes were unchanged since
c0d67deff and its final fixture head was 775163f06. Original source checks used
the paired Python3.12 interpreter and
the five receiving25 qualified dependencies, without modifying their prefix.
The isolated Git source archive has no foreign external checkouts. Its original
unchanged _tabular_native.abi3.so was reused from receiving25; both copies have
SHA256 eb91e62b2f2bac4b86c06d602fc1905fd52d9191ecc8356fc738a55c5f3cc7e3.

Original receipts are retained under
/home/ts/wt/openhcs-issue-batch-20260929/engineering-gaussian980:

* controls02.log/time: original session89273, terminal0, 50 passed in20.82s;
  full process peak532804KiB, zero swaps. Covers Gaussian controls, prepared
  geometry ABI, and original saved label-plane/calibration family.
* controls05.log/time: original session37603, terminal0, two added composed
  provenance controls passed in2.76s; process peak373936KiB, zero swaps.
  Original source-plane count is preserved for independent SITE and explicitly
  admitted physical Z cohorts, using the existing provenance count property.

Original negatives remain intact: controls01 lacked the Git archive's native
extension during import; controls03 was incorrectly launched from the source
checkout and selected its foreign old ZMQ dependency before collection;
controls04 numerical/provenance equality assertions passed but the added count
assertion used a nonexistent .planes property. It was corrected to the original
SourceImageProvenance.source_plane_count, with no production change or weakened
assertion. None was a scientist execution or an UNKNOWN replay.

Initial qualified production byte pins (superseded below for metadata only):

* runtime_image_values.py:
  118750a9171d45114a9be18c5bb0bd8df29eee3718a04c5a085a7217f7778c33
* gaussian_filter.py:
  df06de7964caf889ff6f5539da93ff7656864b9ebaeceba4654250e9d6301b35

Additional semantic closure confirms the original CellProfiler infrastructure
``Process as 3D?`` declaration selects VolumeSourceSpatialDomain and Z stack
components. RuntimeSliceProjection composes declared aligned stacks without
discarding the metadata. The installed skimage Gaussian delegates the full
sigma vector to scipy.ndimage; zeros exclude nonspatial axes without changing
the filter implementation, border mode or intensity conversion.

Next installed acceptance uses the ordinary whole-candidate builder once for
this source and the next natural guide bundle, with a synthetic engineering
destination and an exact lane handoff from Dewey. Required public evidence is
registered Gaussian compile/execute COMPLETE, exact persisted pixels against
independent-site and anisotropic-volume expectations, and unchanged source
provenance/calibration. No viewer or biological rerun is necessary. Receiving25
and all blind-author packages remain immutable.

Parent IMPL-12 cleanup before candidate build
-------------------------------------------

Source head 5991cabc9 deletes the duplicated pixel-rank/channel-normalization/
axis enumeration from spatial_axes and spatial_axes_yx. The existing metadata
owner now provides non_channel_axes once. Optional Y/X projection still returns
None for fewer than two non-channel axes, including a channel-bearing rank2
payload with only one non-channel axis. Strict intrinsic projection still
rejects insufficient declared Y/X or Z/Y/X dimensions. A volume declaration
does not make optional Y/X placement reject a rank2 image. Both paths continue
to reject an invalid declared channel index through the original normalizer.

Relevant post-edit AST closure parsed seven metadata/placement/consumer modules
with zero omissions. Existing Y/X callers in aligned payloads, streaming-axis
binding, viewer sampling and viewer source-domain materialization retain the
optional contract and their own established None handling. Gaussian alone
consumes the strict intrinsic projection; its implementation is unchanged.
This is a focused owner-family audit, not a global R1 or native runtime proof.

Original controls06 session89764 is terminal0: all59 Gaussian, optional/strict
projection, prepared geometry and saved-label domain controls passed in3.56s.
Full process elapsed8.75s, peak426164KiB, zero swaps. Original log/time remain at
/home/ts/wt/openhcs-issue-batch-20260929/engineering-gaussian980/controls06.log
and controls06.time. No whole-candidate build was started before this cleanup.

Current metadata SHA256:
33810f045251604c1404fe91f98da7048ae9b9481a77a41fe61fd04e73dff1bb.
Gaussian SHA256 remains
df06de7964caf889ff6f5539da93ff7656864b9ebaeceba4654250e9d6301b35.
Installed registered MCP pixels/provenance acceptance remains required and
unclaimed. No current scientist, target or shared dependency was changed.

Current-main capability integration
-----------------------------------

Normal merge 0d3bc97ca has parents79491d543 and current merged main
c13028ecf46bbe68249e19939aa05a709eee0e0c. Merged990 already moved the channel
normalizer and optional Y/X projection onto ImagePayloadAxisFields. The real
runtime_image_values.py conflict was resolved in that existing capability:
non_channel_axes lives there and spatial_axes_yx consumes it. The metadata
copies of non_channel_axes, spatial_axes_yx and is_declared_source_channel_plane
were deleted; the normalizer and plane/stack predicates are inherited without
forwarding methods. This closes the IMPL-12 lead without copying the new base.

Strict spatial_axes remains on ImagePayloadMetadata, composing the inherited
non-channel projection with the existing SourceSpatialDomain.spatial_rank.
No abstract source-domain property/default, new carrier or stored field was
added to ImagePayloadAxisFields. This capability keeps its original abstract
channel/plane declarations; metadata keeps its concrete dataclass defaults.
The instantiated MRO control verifies inherited method identity and default
source_channel_axis=None/plane_axis=None, not just successful AST parsing.

Original controls07 session31394 is terminal0:149 passed in22.08s on the
integrated source. Full process elapsed27.80s, peak549612KiB, zero swaps.
The same Gaussian/geometry/saved-domain controls now include original metadata
projection algebra and mixed-carrier intensity-domain/MRO controls. Receipts:
/home/ts/wt/openhcs-issue-batch-20260929/engineering-gaussian980/controls07.log
and controls07.time. Source was materialized at source-controls02 from the
merge commit, using the unchanged receiving26 qualified dependency artifacts
and native table extension; no prefix or scientist was modified.

The determining diff against c13028ecf contains only this receipt, metadata's
shared projection, Gaussian, and its focused controls. Current metadata SHA256:
468abdc4c5d890ce1a9fb271bae0116620244d869396e6684ee7647d8d5d78b5.
Gaussian SHA256 remains
df06de7964caf889ff6f5539da93ff7656864b9ebaeceba4654250e9d6301b35.

Receiving26 is frozen at its original77c3a34f candidate containing79491d543.
Its qualification and acceptance remain evidence for that earlier combination,
not installed proof of this main990 composition. Dewey is notified of the exact
resolved head before merge/final package selection; integrated installed
registered-MCP compiled pixels/provenance acceptance remains separately named
and required. No original client is replayed and no receiving26 bytes relabelled.
