Personal neurite mosaic: aggregate publication defect
====================================================

Observed on the original receiving09 installation, not a reconstructed run.
The author continues field analysis; this defect does not invalidate the
numerical computation or establish biological acceptance of its masks.

Original evidence
-----------------

Control root: next-p001-fresh09-89-20261005/P001_FRESH9SITE09_89 under
/home/ts/wt/openhcs-issue-batch-20260929.

The retained candidate01-technical01.py declares field analysis, shared
acquisition positions, raw acquisition mosaic, and mosaic analysis. Physical
inputs are nine sites with w1 DAPI and w2 FITC. Aggregate metadata correctly
retains well, channel, z, time, source alias and voxel calibration without a
single acquired site identity.

Original native log runtime/data/openhcs/logs/
openhcs_zmq_server_port_6022_1791161109181500137.log, lines1072--1103:

  ValueError: Viewer streaming requires complete source component metadata
  for item 0; missing ('site',).

Owner path: finalize_function_step_outputs ->
ArtifactMaterializationTargetPlan.materialize -> ArtifactOutputBatch.save ->
filemanager_batches -> _output_fields -> project_required in
core/steps/stream_component_semantics.py:335.

Disabling automatic streaming alone permits candidate01t02 numerical
completion, but candidate01t02-measured-receipt.json then records
mcp_tool_failed / ToolExecutionError:

  ZMQ runtime execution violated compiled expectations: table output
  A01_z_index-1_timepoint-1_neurite_outgrowth_cells_step3_details.csv
  is missing schema fields ('site', 'source_image_name').

Viewer publication requires a scalar acquired-site projection. The table
refusal is specifically missing schema columns: it does not prove that the
validator demands scalar acquired-site values. Whether declared nullable
columns are missing, or aggregate expectations are wrong, requires source
tracing. A shared earliest incorrect semantic fact is not established here.
The explicit streaming attempt mosaic-stream-receipt01.json is also rejected:
an exact source receipt is required. Filename guessing is not a repair.

Current bounded continuation
----------------------------

The author retains failed predecessors and now runs all nine fields plus raw
assembly without the aggregate measurement step. No site is fabricated, no
schema assertion relaxed, and no scientific output rewritten. Counts and
lengths remain provisional engine outputs, not accepted accuracy evidence.

Repair acceptance
-----------------

Use a tiny synthetic multi-site source through ordinary compilation,
execution, finalization and managed viewer publication. Derive aggregate
identity and expected table fields from existing compiled artifact/source
scope owners. Both automatic publication and receipt-backed reopening must
accept honest aggregate metadata and preserve calibration, pixels and lineage.
Keep scalar-field behavior and genuinely incomplete acquired-source rejection.
Do not add a fake site, parallel metadata store or filename identity heuristic.

Current owner overlap check
---------------------------

Singer checked current owners: this is distinct from620 (its extension-conflict
fix shipped in626),529 (source-binding versus runtime-slice axes), and closed
630 (broader materialization ownership). No active claim covered the exact
refusals. Singer takes this aggregate publication family after the serial94
installed acceptance and will open its issue. Original science runtime remains
untouched. This record claims reproduced failures, not a tested fix.
