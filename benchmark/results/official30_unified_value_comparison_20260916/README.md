# Official30 unified value comparison - 2026-09-16

This directory preserves the compact evidence from one immutable OpenHCS run
over the canonical 30-case CellProfiler manifest. Every candidate workflow was
compiled and executed afresh through an isolated ZMQ execution endpoint, then
compared with its selected native CellProfiler reference artifacts.

## Result

- 30 workflows executed.
- 30 workflows had retained reference values selected by the manifest.
- 30 comparisons were equivalent.
- Zero differences were reported.
- The focused integration test passed in 1364.81 seconds.

The run used the committed native-reference tree and the five declaration-derived
terminal export pipelines under
`benchmark/reference_exports/official30_value_completion_20260914`. Candidate
runtime outputs were discarded after comparison. The retained files here are
the comparison observations, phase timings, summary and a fresh
inventory of the reference profiles.

## Files

- `observations.csv` and `observations.jsonl`: per-workflow comparison evidence
  and provenance.
- `summary.csv`: one summarized row per workflow.
- `phase_timing.csv`: benchmark phase timings.
- `reference_inventory.csv`: selected reference artifacts and enabled value
  comparison routes for all 30 workflows.

The original `suite_metadata.json` and `run_environment.json` are not present in
the retained archive or its available Git history. The observations identify
OpenHCS 0.8.5 and retain executable, endpoint and submitted-pipeline provenance,
but do not establish the exact candidate source commit or dependency versions.
Later runs' environments are not substituted for those missing original records.

## Claim boundary

This run establishes selected reference-value agreement for the settings and
artifacts represented by the 30 retained workflows. It is not a segmentation
accuracy study or a matched CellProfiler/OpenHCS throughput comparison.
