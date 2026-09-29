# H002 attempt4 query preparation: timing correction and bounded diagnosis

Owner: Lovelace, original206/PolyStore16 source continuation only.
No edits to installed imagej-cache-progress source, H002 driver/receipts,
scientific pipeline or data. No repeated query, raw pixels/notebooks/biological
outputs, new JVM/runtime/download, install, profiling attach or process restart.

## Evidence and exact timing meaning

Named receipt:
`/home/ts/wt/openhcs-h002-uncoached-20260929/output/runtime/h002-live-attempt4/receipts/013-openhcs_query_plate_files.json`.
It records query with limit1, include_previews=false, terminal success.
No inspection of the underlying container was performed by this worker.

Actual driver source `output/mcp_session_attempt4.py:94` sets
`started = time.monotonic()` once before stdio-client/session initialization.
Lines113-115 calculate `elapsed_seconds = time.monotonic() - started` BEFORE
awaiting session.call_tool. Therefore90.16998135202448 is session age at request
admission, NOT query duration. Original90s claim is withdrawn; no new90s query
regression established and no fix justified by that number.

Receipt admission at1790718869.0149193, UTC2026-09-29T21:54:29.014919.
Result-bearing receipt mtime1790718875.589610, UTC21:54:35.589610.
Difference **6.574690818786621s**: admission-to-terminal-receipt-write interval,
including dispatch/serialization/receipt IO; not an exact native stage timer.
The driver rewrites the same receipt after the successful await. The parent's
next-receipt96.745 estimate is a separate upper bound including author time.
The previous cache acceptance explicitly measured0.211s differently; neither
figure proves identical fixture/warm/cold cost or a general latency reduction.

Both driver1614516 and MCP1614529 were alive when checked, started17:52:57/58
local time. The MCP stderr fd points at this attempt's mcp-stderr.log.
Read-only whitelist of actual MCP environ confirms:
`POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej` and
`POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false`.
No credentials/unrelated environment values printed or retained.

Startup stderr reports BigStitcher override from the existing digest-addressed
shared Fiji jars, then OMETiffReader initialization. These lines contain **no
timestamps**. Several reader-open lines accumulated across this continuing
session; they cannot be attributed/count-budgeted to query013 alone. File mtime
is the most recent write, not each line's event time. Do not assign a precise
JVM/decoder split from their order or repeated filenames.

## Source-owned preparation boundary

QueryPlateFilesCapability -> PlateInspectionService.query_files/_query_files
(:997/:1114) -> _create_handler(:1869) -> existing registered detection/handler
owners -> BioFormatsMetadataHandler.source_dataset(:64) -> registered
SourcePlaneStoreAdapter -> BioFormatsJavaAdapter._declares_path and
_discover_container -> BioFormatsJavaContext.ensure_initialized/open_reader
-> FIJI_IMAGEJ_RUNTIME.initialize -> FijiArchiveDistribution.materialize.
Limit1 bounds returned records after inventory preparation, not container/JVM
initialization. include_previews=false prevents requested previews, not metadata
discovery. No biological behavior is assumed.

Existing ImageJRuntimePolicy.initialize separates materialization from Java:
with a fresh JVM it first materializes the canonical bundle, then configures
bundled Java with fetch=never and invokes imagej.init. If Java is already started,
it reuses Java subject to declared Java/gateway compatibility checks.
BioFormatsJavaContext additionally imports reader/metadata/format Java classes;
open_reader builds OME metadata and invokes setId before source-plane projection.
Its process-owned context/lifecycle lock retains initialized gateway state.
No alternate Java helper/cache/decoder has been added.

Installed false policy rejects a missing/invalid bundle before cold filesystem
materialization/network. Actual environment + successful query + stderr pointing
to the shared bundle are consistent with successful warm bundle admission,
followed by cold Java/decoder preparation. They do not time either component.
Bundle provisioning and JVM/decoder preparation are distinct;228 fixed sharing
and inspection responsiveness, not all cold latency.

Query currently does not declare inspection's progress heartbeat/worker offload,
and its description claims no detection although _query_files can create/detect
the handler. This is a source-backed exposure/observability concern, **not a
newly proved90s regression or measured stage bottleneck**. Keep it within the
existing capability/preparation ownership for a separately justified checkpoint;
do not create another progress runner or speculate about bypassing rich metadata.

## Reproduce the diagnosis without calling MCP

Read this single receipt and its actual driver; calculate
`receipt.stat().st_mtime - json.loads(receipt.read_text())["at"]`.
Inspect only the actual stderr fd/log and whitelist cache/download keys from the
existing process. Never replay the request to establish timing. Exact JVM,
reader-open and source-projection costs are **unavailable retrospectively**.
Future stage profiling belongs on ImageJRuntimePolicy/BioFormatsJavaContext and
existing preparation owners, using before/after monotonic events on an authorized
small synthetic run after the live science slot; do not attach/restart H002.

## Source integration and checks (not live fixes)

Original parent206 was6bc71ee5c, child16 was9e205fee, remote heads matched.
Normally merged fetched OpenHCS main8b090e and PolyStore main94bf443 into ONLY
their original isolated continuation branches. Merge heads parentb2edc4503,
child50c1e49; conflict resolution retains merged17/228 download-policy and launch
projection changes rather than older cache-only declarations. No rebase/reset/
force-push or installed-tree mutation. Main's recorded c16b8fc gitlink is retained;
the original16 worktree intentionally differs while its broader gates remain.

Six scoped source/test files parsed; both diff checks and Ruff on dependency
distribution/cache tests and parent cold-runtime tests pass. No pytest/runtime
rerun needed to answer this diagnostic and none performed. NRA/refactor-audit
coverage is focused source/consumer trace, not a global scan or native proof.
BOUND-2/6: canonical distribution/runtime/context own config/lifetime; do not
read/replace them in callers. IMPL-12/13: keep one materializer and Java lifecycle.
The merge restores current-main behavior, not a performance fix/new owner.

Remaining original206/16 **141 passed/26 failed** and **after-ROI profile not run**
unchanged. Fresh cold stage profile, source preservation controls and broader
Java/CZI fidelity remain pending. No performance/preservation/live claim from
syntax checks or this receipt. Parent's installed228 acceptance remains separate.
