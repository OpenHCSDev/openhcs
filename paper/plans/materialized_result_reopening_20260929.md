# Native materialized-result reopening

Owner: OpenHCS blind-analysis integration coordinator. Issue #134.
Base: 9a6db7bab414740f91d953367ab64f0cc6106026, merged inspection PR #173.
Branch: fix/mcp-materialized-result-reopening-20260929.
Worktree: /home/ts/wt/openhcs-materialized-result-route-20260929.

Required workflow remains the full workflow in materialized_result_followup_20260929.md.
This continuation must not narrow it to file inspection or a synthetic count.

## Ownership decision

Task authority: reopen exact retained materialized files without a scientific
rerun, relocation, filename-derived source identity or coordinate/calibration loss.
The initial NRA class-first corpus covers the plate DTO, inspection service,
streaming service and core viewer streaming service: 75 original ClassDefs,
75 unique canonical class-family joins, no omitted syntax rows. Global R1/MRO
and native equivalence remain OPEN. Feature extensions are intentional authored
changes, not a proved-equivalent NRA transaction.

Determining owners and required consumers:

- AgentPathPolicy -> the one admitted explicit-directory inventory used by both
  query and streaming. Do not duplicate the reader/record-building algorithm.
- PlateFileStreamRequest -> automatically generated MCP selection fields.
- Original PlateInspectionContext -> StreamingService source calibration. The
  independent result-directory selection must not replace this source context.
- ImagePayloadMetadata -> native ROI source/plane/domain/spacing projection.
  Its existing codec determines meanings; a new archive codec may encode/decode
  this owner, but may not recreate its schema, registry or field roster.
- Existing PolyStore ROI codec -> geometry and object identities. No fallback
  conversion of malformed archives and no invented detections.

IDEN-1: plate/source context and persisted output location are different facts.
BOUND-2: source metadata must descend to ImagePayloadMetadata, not raw consumers.
Counterevidence: ROI geometry is preserved by the native archive, but current
Output.metadata does not enter the per-ROI disk sidecar. A reader cannot recover
discarded plane/source identity by making plausible filename guesses.

Historical external ROI files can lack OpenHCS source metadata. That is a genuine
optional external contract, not a compatibility reader. Exact arbitrary-directory
reopening must reject missing required source/plane evidence rather than claim it.
H002's historical malformed centre archive remains unchanged and unaccepted.

## Acceptance and crossing

Run focused source/native disk round-trip checks, then the installed public MCP
journey on bounded native producer outputs: explicit directory, original source,
exact labels/coordinates, plane identities, transforms, and personally opened
raw/result/combined captures under two windows. Check frozen science digests.
Use isolated :90/unused port, not the active H002 port 5690 or desktop :0.
Keep the held-out and private-reference boundaries intact.

PR #157 still owns worker_execution, runtime_exports and
function_artifact_materialization. Do not compete there. This branch owns the
independent shared directory consumer and native source-metadata persistence
boundary. Full writer-success observation remains coordinated with #157.

## Implemented native reopening checkpoint

Production commit: 9f37cb66d. The source contract is intentionally extended;
this is not a proved-equivalent NRA migration. Expanded native class census:
162 original ClassDefs, 162 unique canonical joins, zero unprojected rows across
the original four modules plus ROI metadata, runtime metadata and materialization.
No global full-package/R1/native-MRO proof is claimed.

- Query and streaming now use one path-policy-admitted explicit-directory inventory.
  PlateFileStreamRequest owns result_directory; MCP derives its exposed parameter.
- Original plate context supplies ROI acquisition calibration, independently of
  where outputs were saved. Explicit image-result reopening requires a verified
  source receipt rather than manufacturing identity from a filename.
- Existing ImagePayloadMetadata is projected into the native ROI sidecar, and
  decoded through its canonical codec on reopening. Source schema/fields and
  geometry remain owned by their existing types; no extra format registry exists.
  Missing or conflicting source declarations fail the explicit native route.
- Native per-archive metadata drives components, retained plane projection,
  domain and spacing. Existing partition_indices groups wire-compatible batches;
  existing producer.for_indices preserves identity after empty-archive omissions.
  One source-owned calibrated_metadata method fills absent spacing for images
  and ROIs without replacing explicit native spacing.
- The stream capability now truthfully declares viewer launch/update side effects.

Focused source checks passed 156; installed checks passed 157, including the added
retained-plane native round trip. Application module paths were verified inside
the owned installed venv, with source used only for test fixtures. A first new
plane test mistakenly expected integer display-coordinate values; source tracing
confirmed the existing projection deliberately returns canonical strings. The
test now checks that original declaration's exact output and round-trip equality;
no production codec or assertion was relaxed to hide a serialization change.
Two pytest configuration warnings are due to deliberately disabled async plugins.

Installed public MCP on isolated :90/5691 reopened both a fractional POINT archive
and a real native-materializer polygon archive from retained_native_20260929.
Despite B99/w7 artifact names, A01/channel 1 source identity, shape 128x128,
XY scale 0.65, zero translation and exact native labels/coordinates were retained.
All six same-coordinate raw/result/combined captures under [444,26058] and
[1500,9000], gamma 1, were personally opened. Canvas 1440x950, camera center
(0,41.275,41.275), zoom 5.366586538461538 and axes stayed fixed. Exact raw 4x4
values were also read via MCP. These are manual synthetic transport fixtures,
NOT detections: accept transport, reject any biological accuracy claim.

Complete native envelopes, requests and disposition are retained under
/home/ts/wt/openhcs-live-point-evidence-20260929/native-reopening-20260929.
MCP closed the extra viewer and a listener check confirmed port 5691 absent.
Current H002 processes stayed alive; SCIENCE_SHA256SUMS passed unchanged.
No frozen rerun, tuning, artifact rewrite or new reference/held-out access occurred.

Still OPEN: source-bearing runtime writer-success admission with #157; the real
compile/run-to-reopen journey; truthful reopening of historical H002 files whose
source header was never persisted; full 3D/orthogonal installed viewer proof;
fresh context-isolated blind QA and scientific acceptance. Keep issue #134 and
the full goal active. Do not substitute this synthetic checkpoint for them.
Resource headroom remains warning, so no extra agent fleet was started.
