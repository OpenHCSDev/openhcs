Fixes #395. Source owner: Lorentz. Integration, merge and installed acceptance: parent.

The original `SourceProjectedImageOutput` consumes proven selected singleton
outputs during materialization. The ordinary saved-image stream now queries
`ImagePayloadMetadata.singleton_plane_projection` through the inherited
`ImageStreamingRequest` hook, after original native-window admission; existing
`RuntimeSliceProjection` owns pixels, masks and source context. Strict projector
and receiver guards are unchanged. Duplicate overwritten metadata methods are
deleted, retaining one original implementation each. No ndarray/channel guesses,
historical metadata rewrites, mirrored stores or compatibility readers.

Independent request and metadata capability mixins exercise actual cooperative
`super()`/MRO behavior through unchanged consumers.

Current main `e3765e3` is normally merged. Production freeze `32d7a6ec`:

- Original packaged R0: **PASS**, all three changed production paths,
  5,177 comparisons, zero positive deltas. Original failed R0 is preserved.
- 218 unique bounded passing source controls across named scopes. Final public
  saved-image branches: 3 passes via real disk/SHM/original decoder/strict receiver;
  independent plain persisted TIFF: 1 pass with native calibration/Z/T declarations;
  original complete 12-output/five-QA real-SHM module: 12 passes.
- Complete owner-contract shard: 104 passes, including new metadata cooperative
  hooks, masks/color, undeclared/missing/non-singleton controls and existing
  persisted metadata/image-plane/runtime-slice contracts.
- Two original Java-backed autodetection cases remain explicitly outside CPU-only
  service qualification; rejected fixture/resource attempts are retained.
- R1 **BLOCKED, not waived**: original-capable read-only NRA673c062 verified;
  unchanged exact policy with complete recorded Git context reaches the fixed
  58s execution allowance without a completed before/after report. No detector,
  API or policy shim. Broader bounded tooling/preparation remains a separate
  parent-owned follow-up, not a hold or scope expansion for finite issue395.

[Final receipt](docs/validation/selected_plane_reopen_stream_20261001/RECEIPT.rst)
and manifest include source hashes and all failures. The 72 raw evidence members
are preserved unchanged in a byte-compared archive with individual SHA256 index.
Original materialization evidence and baseline numerical failures remain intact.

Parent's installed229 ordinary saved-image/native bitmap acceptance passed,
including source channel2 and physical1.3556. **The later metadata-owner promotion
has not yet been installed/live-verified**; parent owns its next safe milestone.
No installation/native/scientific execution or live environment mutation by this
source author. Biological rejection/freeze and assisted-versus-autonomous boundary
remain unchanged; this PR establishes transport/materialization, not biology.
