# Parent PR309 grid warning: separate layout publication boundary

Read-only witness: parent attempt02 `receipt-044.json`, result
`openhcs_inspect_plate_path`: four saved paths and pixel size0.65; partial warning
`plate_grid_dimensions_unavailable`. Parent synthetic input declares `[1,1]`;
both produced `images` and `checkpoints` declare `[]`. No parent tree/runtime
or synthetic artifacts were modified.

The richer existing owner is `SourceTileLayout` in
`core/source_tile_geometry.py`, not the scalar grid field or well count.
`AtomicMetadataWriter._update_projection_geometry` (virtual_workspace_metadata.py
266) rebuilds layout from retained typed projections on each publication and final
reconciliation. Those projections contain no per-source `SourceTileGeometry`;
`SourceTileLayout.metadata_grid_dimensions` deliberately returns unknown `[]`.
The input's legacy rectangular-grid declaration does not accompany the produced
source-domain facts. This differs from issue315's inherited object producer kind.

`MetadataHandler.get_metadata_grid_dimensions` is already the serialization
view that preserves unknown layout; strict `get_grid_dimensions` is required by
actual stitching consumers. `PlateInspectionService` currently calls the strict
getter (plate_inspection_service.py1908), hence the warning. Merely changing that
call would suppress the symptom without retaining the known acquisition fact.

Named follow-up: **parent integration / PR206 acquisition-layout publication**.
Reproducer: source `[1,1]`, per-well site1 Gaussian output, two wells, automatic
main and explicit checkpoint targets. Preserve the original receipt. Acceptance:
the existing acquisition/projection owner publishes a valid layout proof when
the output retains it; layout-changing or genuinely undeclared source geometry
stays unknown, and strict stitching still rejects it. Source tests must cover
ordinary identity-preserving processing and collapsed/transformed tile domains.
Do not infer coordinates from generated names, well count or array shape, copy
an input grid blindly, or add a parallel layout store. This crosses PR206's
source workspace/preparation authority and is not included in PR316 without
that owner's direct coordination. Parent owns installed/MCP confirmation.
