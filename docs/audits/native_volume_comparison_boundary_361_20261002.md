# Native volume comparison boundary (#361)

The matched batch previously compared two native volumetric SaveImages TIFFs
with 120 OpenHCS plane TIFFs by physical image count. Those exports represent
the same two logical images. The comparison now consumes the existing typed
workspace projection and the execution's declared image-set axis policy.
Native execution, output generation, and scientific processing are unchanged.

`SourceProjectionSet.image_plane_groups` owns ordering and cohort separation.
Only an explicitly declared Z member axis permits composition; producer alias,
artifact kind, execution scope, well, site, channel, and time remain separate.
Z coordinates must be unique and contiguous. Their origin comes from the
actual source addresses: `SourcePlaneIndexedMetadata.z_index_for_plane`
preserves explicit scalar origins, so comparison cannot universally assume Z=1.

`RuntimeImageSnapshot.from_source_planes` owns decoding and pixel composition.
It validates scalar image axes, declared dtype, spatial placement, matching
non-provenance metadata, and exact plane shape/dtype. Existing
`SourcePlaneIndexedMetadata.from_metadata` validates the full declared plane
count and zero-based order when the source provides those fields. The snapshot
owns all constituent physical paths; its existing `path` view derives the first
constituent. No independently synchronized path or image roster is introduced.

`RuntimeOutputSnapshot` selects only actual exported image files through
`VirtualWorkspaceSourceProjection` and rejects missing or multiply owned
physical coverage. `RuntimeExportObservation` continues to own the physical
inventory. Matched batch accounting replaces physical image counts with logical
image counts while preserving all-file, table, schema, and output-format checks.
The existing image comparator still rejects logical cardinality and pixel
mismatches. The regular OpenHCS adapter derives its axis policy from the actual
`RuntimeArtifactExecutionObservation`; the matched OUTCOMES route derives it
from its resolved pipeline configuration. A 2D policy retains singleton images.

Cross-tool matching retains the existing decoded-pixel multiset contract.
OpenHCS producer identities constrain its own grouping; this change does not
claim a new correspondence between native and OpenHCS producer names. CSV
measurement/schema comparison remains a separate gate. Without declared
indexed-plane metadata, physical coverage cannot infer an absent boundary plane;
the native logical shape/content comparison detects that mismatch.

Saved actual official 3D exports were replayed through the production snapshot,
matched inventory, and strict CellProfiler measurement comparison: native two
uint16 volumes and OpenHCS 120 plane TIFFs yield two [60,256,256] images with exact
pixels, complete physical coverage, and zero measurement differences across six
participating CSV tables. This replay runs no scientific pipeline, preparation,
or native execution and makes no speedup claim.

Validation: 77 focused tests and 245 existing equivalence/adapter/export tests
pass. Controls include arbitrary Z origin, missing internal/tail planes,
declared plane cardinality, mixed source/producer/execution cohorts, duplicate
physical ownership, wrong axes, dtype/mask/geometry conflicts, changed pixels,
and existing 2D behavior. Source ownership and replay receipts are retained in
the benchmark-runs workspace for review.

Timing remains separately reported: warmed native invocation includes its
prepare/group/module/output/post-run work; OpenHCS server-job includes submitted
pipeline coordination/execution/export and excludes endpoint startup. Native
JVM/pipeline loading and OpenHCS startup prewarming are distinct preparation
boundaries. This comparison repair does not declare those clocks identical or
promote a performance ratio.
