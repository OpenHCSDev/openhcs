# Typed 3-D point result: implementation boundary

Status: measurement payload retention implemented in this draft. The point
writer, native 3-D projection, installed entrypoint, and biological result are
not yet implemented or claimed.

Base: OpenHCSDev/openhcs `9644febe2785aace85bbc8bd1d2ce062525c56d2`.
Issue: OpenHCSDev/openhcs#134. Integration owner: blind-analysis coordinator.
Coordinate the worker/export crossing with open PR #157; do not edit its
`function_artifact_materialization.py` or worker/export paths competitively.

## Current contract and failure

- `MeasurementTable` owns schema-bearing rows, an object subject and optional
  measurement-feature owner, plus source provenance
  (`openhcs/core/runtime_measurements.py:41`). The subject's declared ID field
  is supplied by `ObjectMeasurementSubjectRelation`
  (`openhcs/core/artifacts.py:1344`).
- Before this draft, `MeasurementsArtifactType.materialization_payload` handed
  only `table.rows` to every writer (`openhcs/core/artifacts.py:704`). This
  draft retains the complete table through the existing `ColumnarRows`
  contract, while CSV and JSON still serialize only rows. Its provenance,
  subject and feature owner are now available to a measurement writer.
  `MaterializationSpec` already admits multiple writer options for the same
  artifact; a separate hand-built file bundle is not required.
- The existing ROI writer extracts image-label contours, not measurement
  coordinates. `ROIArchiveSourceMetadata` stores an existing
  `ImagePayloadMetadata` declaration in the native archive sidecar; it is not
  a second source schema (`openhcs/core/roi_source_metadata.py:15`).
- OpenHCS pins PolyStore `e430c331ad931edc92dfe9d4fcd0d837a3cfeea8`.
  Its native `PointShape(y, x)` codec preserves fractional XY, but has no Z
  member. Standard ImageJ native Z is a discrete plane. OpenHCS's Napari
  `_build_nd_points` prepends route component indices to 2-D coordinates
  (`openhcs/runtime/napari_viewer_server.py:1089`); this cannot represent
  fractional centre Z by itself.
- Frozen H002 hand-wrote an ImageJ POINT ZIP with rounded Z and no source
  sidecar. It remains AMBIGUOUS and must not be rewritten or rerun as a repair.

## Required closure

1. Keep coordinate roles and object ID on typed declarations: a producer must
   declare which measurement features mean Z, Y, X and which subject owns the
   object ID. Do not infer them from column spellings or filenames. Retain the
   complete `MeasurementTable` through writer dispatch, adapting existing CSV
   and JSON writers coherently rather than adding a side channel.
2. Persist exact fractional ZYX, stable object ID and canonical source binding
   in one inspectable typed point result. If the ImageJ ROI ZIP is retained as
   the external format, its metadata sidecar must carry information the native
   format cannot express, under an owning typed contract. No rounded-Z-only
   fallback or legacy reader for the frozen malformed archive.
3. Reopen the persisted result through the installed public MCP
   `result_directory` route with the declared raw source, not a guessed plate
   path. The managed viewer must show the exact fractional 3-D point location,
   feature-row/object identity and orthogonal views. Preserve path policy and
   reject foreign source identities and escaping paths.
4. Verify one continuous synthetic compile/run/materialize/inspect/reopen
   journey, then a new bounded context-isolated blind trial with raw-only,
   result-only and combined captures at spatially distributed matched native
   coordinates. Keep held-out answers sealed until pipeline freeze. A focused
   source test or synthetic viewer does not establish biological acceptance.

## Current stop conditions

Do not claim a complete ownership proof from a partial scan or duplicate
PR #157's worker/export owner. The resource guard currently warns on swap;
do not start parallel agents, a large scan/test, or a new blind image load
until headroom is restored. Source inspection and small isolated edits may
continue, but a coherent change still needs complete ownership and native
behavior evidence before merge.
