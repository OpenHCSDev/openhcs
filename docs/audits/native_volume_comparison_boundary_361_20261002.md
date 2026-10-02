# Native volume comparison boundary (#361)

The matched batch previously compared two native volumetric SaveImages TIFFs
with 120 OpenHCS plane TIFFs by physical image count. Those exports represent
the same two logical images. The comparison now consumes the existing typed
workspace projection and the execution's declared image-set axis policy.
Native execution, output generation, and scientific processing are unchanged.

`SourceArtifactProjection.image_plane_cohort_key` owns whole-image versus scalar
cohort derivation. `SourceProjectionSet.image_export_groups` owns ordered
cohort partitioning, which the comparison consumes without reinterpreting the
projection address.
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

Initial validation: 77 focused tests and 245 existing equivalence/adapter/export tests
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

The original architecture gate identified foreign metadata/address checks. The
repair gives scalar axis and declared pixel validation to `ImagePayloadMetadata`,
while removing its complete channel slicing and mask projection algorithms.
`ImageMaskDomain` now owns those algorithms alongside accepted mask geometry and
broadcasting. Existing call order, modulo requested axes, supplied-channel-data
behavior, shared masks and pixel/mask views remain intact. No core source owner
imports the equivalence layer and no new nominal class is introduced.

Fresh execution and current-main qualification
---------------------------------------------

The original matched native 3D command completed warmup and two measured
repetitions at `1cfec7e4ba9626e05fb282db3c762ff21a57b109`, with ArrayBridge
0.3.6, openhcs-basicpy 1.3.1 and JAX/jaxlib 0.9.2. Native CP/core remains
4.2.8.1 in Python 3.9.25 with NumPy 1.24.4 and SciPy 1.9.0. The launcher
explicitly selects the existing pinned Temurin JDK 11; the earlier missing-Java
import failure remains retained under the existing bootstrap issue #138.

Both measured repeats independently pass complete physical inventory and exact
logical-image comparison: two uint16 `[60,256,256]` native images against all
120 OpenHCS planes, in two 60-plane cohorts. Six nonempty scientific CSV tables
contribute 150 feature keys and 2,825 measurement facts per tool per repeat,
with no scientific differences. Within-tool repeated pixels and scientific
measurements also agree; native elapsed-time cells and its experiment timestamp
are separately identified. Native input hashes and all observed output hashes
are retained and checked. Unsaved intermediates are outside this validation.

| Measured repetition | Native invocation (s) | OpenHCS server compilation (s) | OpenHCS execution job (s) | OpenHCS compilation + execution job (s) |
| --- | ---: | ---: | ---: | ---: |
| 0 | 14.354725 | 1.103083 | 9.713339 | 10.816422 |
| 1 | 14.724486 | 1.105663 | 9.623588 | 10.729251 |

Server startup, registry/kernel prewarming and native JVM/pipeline loading are
excluded. OpenHCS execution-job time does not include compilation; the final
column explicitly adds the two server jobs. Native invocation includes its
prepare/group/module/export/post-run work. OpenHCS uses one inline worker in the
endpoint PID; the configured `fork` setting does not imply a child was forked.
Native TIFF compression is Adobe DEFLATE (tag 8), while OpenHCS plane files are
uncompressed (tag 1). Those actual packaging and preparation differences remain
disclosed, and the original report's `timing_claim` is unchanged. This is a
comparison-correctness qualification, not a universal scaling claim.

After that frozen execution completed, main `6ed8b87f7` was normally merged at
`f6bd14f8e0060dc261fe52be8a8204b210b987fa`. All 550 relevant tests pass, including
the new source-label plane-domain controls from main. All original R0 roots and
R1 pass against that main with unchanged tools and the 160-second R1 budget.
Earlier failures remain retained. This documentation addition changes no
production source; broader 30-case native parity remains a separate gate.

The benchmark-runs workspace retains the execution directory
`native-volume-361-current-matched-3d-v3-20261002`, its source-freeze receipt,
`native361-fresh-current-3d-timing-science-independent-audit-20261002.json`, and
`native361-f6bd-latest6ed8-qualification-summary-20261002.json`.
