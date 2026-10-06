Calibrated Gaussian source-axis owner checkpoint
==============================================

Issue980 preserves the original receiving25 failure and author source. No
original execution is replayed or scientist prefix changed. This branch starts
from actual merged main c882d5edc67bffe7ec7f2eb3a2eeb7fe64e9415a in the reused
finished context-bounding checkout; foreign gitlinks and keepers are preserved.

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

Production bytes are unchanged since c0d67deff; the final fixture head is
775163f06. Original source checks used the paired Python3.12 interpreter and
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

Production byte pins:

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
