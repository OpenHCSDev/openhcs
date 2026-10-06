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

Source and installed qualification are pending at this initial checkpoint.
Required controls: calibrated singleton SITE/Y/X; multiple independent sites
with no cross-site smoothing; anisotropic declared intrinsic Z/Y/X parity;
SITE/Z/Y/X and declared channels; original metadata/provenance and mask
preservation; strict missing physical-Z spacing and invalid channel/rank
rejection. The ordinary installed public MCP compile/execute and persisted
result check use a separately recorded synthetic engineering destination,
not the original scientist or receiving25. No merge readiness is claimed yet.
