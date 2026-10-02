S1 typed viewer-result presentation: receiving surface
=====================================================

Source owner Lorentz; integration/live owner parent. Base e66500e7ae3804abca1396681c50e1cef5e9a11e.
Original dispatch S1-VIEWER-DISPATCH-20261001.rst read completely. Main's
McpDevTypedOutputRenderer and McpDevToolBatchResponse own framing, contract
descent, diagnostic errors and renderer MRO lookup. Viewer leaves own only
presentation of declared DTO facts. BOUND-1/2/8, MEMB-1/2/5, IMPL-4/12/13 apply.

Known DTO bypasses: viewer.py validation44, state148, payload297, navigation802,
runtime-debug1053 and snapshots1367. Parent's eight-module census (zero unparsed)
is syntax screening, not a global ownership proof. Serial checks are bounded to
one CPU/512MiB aggregate RSS/60s with MemorySwapMax0. No dependency install,
native/viewer launch, scientific execution, private environment mutation or397
artifact changes. Disk check warns7.7GiB; no new environment or heavy parallelism.
Owned disposable source-test/analysis scratch: scratch/s1_* beneath this checkout.

Producer seams needing explicit coordination
-------------------------------------------

Not external extension metadata:

* ViewerWindowLayerState.payload_summaries and ViewerWindowPayloadRecord.summary/
  array_value_summary hold internally produced native summary records. Existing
  consumers include ViewerWindowStateResult.image_payload_binding_for and
  ViewerWindowService validation, native-window decoding and sampling.
* ViewerWindowImageSampleResult.records is assembled in ViewerWindowService.sample_image
  at1907 from existing payloads plus layer identity, then raw-read again for route,
  axis and bounded sample semantics. ROI payloads at2081 likewise have known schema.
* RuntimeExecutionStatus.response is produced by the owned runtime protocol,
  but renderer reconstructs counts from raw executions/running/queued/uptime keys.

Proposal: extend the original declaration owners with their native summary/array
sampling and per-layer sample/ROI record types, then change the producing service
to carry these original typed records end-to-end. Where original native protocol
already has the schema, reuse it rather than create a viewer DTO facade. Preserve
exact public JSON and original raw response receipts; unknown genuine component
maps remain open. Move sample/ROI behavioral decisions to original record owners,
not a new consumer type/string switch or shape registry. Coordinate shared
agent/dto/viewer.py, agent/services/viewer_window_service.py and execution.py seams
with parent before modifying them; runtime materialization/source394 remains out.

First coherent checkpoint migrates existing rich declarations and their shared
framing, removes corresponding raw reader algorithms, proves actual CLI rendering
and independent declaration/cooperative-MRO behavior. Full closure remains open
until every remaining state/payload/sample/ROI/runtime member is on that route;
partial migration is not S1 completion. Publish working draft promptly. Parent
owns subsequent installed/local-live acceptance; hosted CI waiting is overridden.

Working checkpoint
------------------

Issue407 owns this finite surface. Validation and probe now inherit original
typed framing and decode each producer DTO once. Validation layer/counter fields
descend through their original multiple-inheritance declarations; shared viewer
warnings and optional descriptor presentation live on one viewer presentation
ancestor, with original diagnostics, options and renderer registry retained.
The replaced validation/probe raw readers are deleted in place (70 lines deleted,
66 added at this checkpoint before the source guard). Seven bounded behavior
controls pass,273044KiB aggregate RSS/7.969s/MemorySwapMax0. They exercise actual
command/parser rendering, false/zero/empty facts, strict bool rejection, preserved
malformed receipts, missing/error separation, new DTO/capability inherited binding
and a new renderer combining independent cooperative super hooks. An initial
new fixture omitted the required server framing and had7 failures; that receipt
is retained. Fixture construction now uses the original batch/server/tool owners,
not a permissive source decoder or compatibility fallback.

The admitted guard derives typed viewer members from the original declaration
hierarchy and prevents literal-key raw get readers there. It does not exempt any
typed production member or ban genuine dynamic component mappings. State, payload,
image/ROI records, navigation, snapshots, runtime status/debug remain open at this
first checkpoint. The working PR stays visible while those members are migrated;
neither this partial source pass nor the source guard establishes installed S1
acceptance or a complete global NRA audit.
