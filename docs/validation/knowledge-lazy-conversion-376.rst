Selected knowledge conversion deadline: issue376
================================================

Status: source diagnosis in progress; no installed acceptance or repair claim.
Owner: managed-viewer sidecar, now distinct knowledge lazy-conversion owner.
Base: main6ace57656 in /home/ts/wt/openhcs-knowledge-lazy-conversion-20261001.

Original installed failure
--------------------------

The read-only openhcs_get_knowledge_document request selects document
openhcs_official30_benchmark_recipes, section
cp-tutorial-pixel-based-classification-openhcs-python, max_chars50000.
The original10s transport observation returns mcp_transport_failed/TimeoutError.
Parent reports the same MCP PID1658909 remains healthy. No retry, restart,
larger deadline or changed max_chars is authorized.

Original evidence remains parent-owned in
/home/ts/wt/openhcs-issue-batch-20260929/calibration371-classification372-installed-20261001:
launch.sh, mcp.stdin line20 and mcp.stdout lines1429..1452.
Private wheel SHA95123985 prefix, parentff52f0e includes371/372.
These references identify retained evidence, not a fresh execution.

Required relation and ownership
-------------------------------

Selected source retrieval must use the existing importer and canonical public
PipelineDocument renderer without initiating unrelated catalogue/runtime work.
Trace KnowledgeBaseService._official30_source_section_lines ->
_official30_public_source -> import_cellprofiler_pipeline ->
PipelineDocumentAuthority. Do not replace that mechanism with another converter,
raw cppipe fallback, generated-source cache or larger deadline.

Applicable patterns: IMPL-12/13 (reuse the original translation/serialization
owners), MEMB-1/2 (derive discovery from declarations and the existing registry),
IMPL-3 (no generic consumer concrete-type dispatch). Shared algorithms stay on
their owning ancestor; leaves supply only independent nominal hooks.

Checked all open PR titles and matching knowledge issues. No matching owner
found. Schrodinger PR358 owns cold runtime startup/readiness, not this boundary:
ZMQClientService, ZMQExecutionClient and paired ZMQRuntime are excluded.
If diagnosis reaches that seam, coordinate before edits. Parent371 calibration
and372 classification source and frozen blind/runtime boundaries are excluded.
Snapshot observation/writer and Qt binding hooks remain unchanged.

Validation and disposition
---------------------------

Source-only: one CPU,512MiB combined RSS,60s per shard, no providers/plugins,
native/MCP/UI/Fiji/download/install or heavy lock. Parent occupies the native
slot and owns subsequent original installed10s entrypoint acceptance.
Resource helper reports RAM20.0GiB, home7.6GiB and swap10.7GiB: no parallel fleet
or large tests; only serial bounded source checks and small durable receipts.
No owned scratch created yet. No complete global NRA/R1 claim.

Done when the original selected request has focused behavioral evidence,
an independent declaration/hooks case needs no consumer edits, missing and
unsupported conversion remain typed, original failures are retained, original
pinned R0 covers all changed production files, and parent installed acceptance
has passed. Current checkpoint does not satisfy those conditions.
