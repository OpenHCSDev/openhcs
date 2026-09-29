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
