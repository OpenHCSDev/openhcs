# Matched full-cohort worker sweep — issue 1100

Prepared record: `matched_worker_sweep_20261007`, source `67cdcc3dea60c611f3bb964d1b343c931a589e46`.
This is a draft archive plan, not a qualified result. At preparation no mode had a terminal receipt or converter PASS. Append only completed, unchanged-source captures after strict conversion; keep unfinished modes explicitly pending. No numeric speedup claim is supplied here.

| Archive mode | Assignments | OpenHCS workers | Stock CellProfiler processes | Use |
| --- | ---: | ---: | ---: | --- |
| singlewell | 1 | 1 | 1 | May point 1; fresh single-sample cohort |
| 8assignments-2workers | 8 | 2 | 1 | May point 2 |
| 12assignments-3workers | 12 | 3 | 1 | May point 3 |
| 16assignments-4workers | 16 | 4 | 1 | May point 4; shared fixed-workload endpoint |
| 16assignments-1worker | 16 | 1 | 1 | Fixed-workload reference |
| 16assignments-2workers | 16 | 2 | 1 | Fixed-workload scaling |
| 16assignments-3workers | 16 | 3 | 1 | Fixed-workload scaling |

All modes cover the same declared thirty workflows on one production revision, with one warmup and three measured repetitions. Each repeated assignment uses the selected source sample; repeated assignments are not independent biological wells. Primary denominators are actual one-process stock CellProfiler observations covering the identical assignment identities and outputs. No native timing projection or independently parallelized native-process calibration is used.

The May schedule changes workload with worker count: 1/1, 2/8, 3/12 and 4/16 workers/assignments. Its CP-relative ratios reproduce the requested workload schedule, not fixed-workload parallel efficiency. The separate sixteen-assignment comparison uses OpenHCS one-worker execution time divided by its two-, three- or four-worker execution time; efficiency divides that speedup by worker count. Keep these interpretations separate. The four-worker/sixteen-assignment capture is shared rather than recaptured.

Execution covers CellProfiler's pipeline call, including prepare-run, prepare-group, module work and post-run, versus OpenHCS's complete server pipeline job, including saving/publication and plate exports. Total compares native prepared invocation with OpenHCS's disjoint compilation-plus-execution client submission/wait phases. Exclude process/JVM/server startup, function-library readiness, warmup and scientific comparison; never add nested server/worker durations again. Ratios use independent engine medians from three measured repetitions.

RAM is unavailable: the retained matched producer/native report contracts do not collect process-tree peak RSS. Blank memory fields remain blank; May RAM is not substituted. If genuine separately observed memory becomes available, retain its measurement scope and original custody before making a memory plot.

Qualified layout uses existing archive ownership:

- `data/MODE/{execution_summary.csv,total_summary.csv,summary_custody.json}`.
- `protocol/MODE/`: original command, controller, terminal, declared manifest and environment/source seal; common converter and archive owner alongside.
- `reports/MODE/CASE/`: original lightweight native/candidate/provenance reports, progress and warmup/measured phase receipts. Science image/CSV/database payloads stay at their original capture locations rather than being duplicated.

Original custody is preserved byte for byte. Conversion must reject absent terminal, nonzero exit, changed/dirty source, mixed environment, incomplete assignments/repetitions, wrong worker evidence, missing output inventories and any scientific difference. The protocol converter derives serial-native and candidate-worker counts independently from their command/provenance owners; optional external native calibration still requires matching worker counts. No historical converter or frozen record is edited.

## Current delivery status

The `singlewell` mode is complete and qualified: all thirty declared workflows, warmup plus three measured repetitions, and all 120 complete scientific comparisons passed on production source `67cdcc3dea60c611f3bb964d1b343c931a589e46`. Its original summaries and lightweight custody are archived here. The two-worker mode is running; the other five modes are pending. This partial record is not a completed scaling sweep and does not replace the current manuscript record. The protocol manifest records the original preparation state, not current measurement admission; each mode’s `summary_custody.json` and original terminal are the authorities.

## Post-terminal commands

Run from the existing publication worktree after source admission; use its existing environment. Paths below identify existing owners rather than a new pipeline. Execute only modes whose original terminal and qualification gates pass.

```sh
SWEEP=/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1
RECORD=benchmark/results/matched_worker_sweep_20261007
PYTHON=/home/ts/code/projects/openhcs/.venv/bin/python
CONVERTER="$SWEEP/protocol/convert_matched_reports.py"

# Fresh output namespace; rerunning must not overwrite an existing conversion.
"$PYTHON" "$CONVERTER" --suite-dir "$SWEEP/1assignment-1worker/capture" --output-dir "$SWEEP/1assignment-1worker/converted"
for MODE in 8assignments-2workers 12assignments-3workers 16assignments-1worker 16assignments-2workers 16assignments-3workers 16assignments-4workers; do
  "$PYTHON" "$CONVERTER" --scaling --suite-dir "$SWEEP/$MODE/capture" --output-dir "$SWEEP/$MODE/converted"
done
```

After PASS, stage the three converter files unchanged under `RECORD/data/MODE`; map capture `1assignment-1worker` to archive `singlewell`. The existing archive owner accepts any completed subset, so the first thirty-workflow mode can support the draft PR while other captures remain pending. For the complete record its parameters are:

```sh
ARCHIVE_ROOT="$RECORD" "$PYTHON" "$SWEEP/protocol/archive_converted_modes.py" "$RECORD" "$SWEEP/official30-manifest.json" "$CONVERTER" \
  singlewell "$SWEEP/1assignment-1worker/capture" \
  8assignments-2workers "$SWEEP/8assignments-2workers/capture" \
  12assignments-3workers "$SWEEP/12assignments-3workers/capture" \
  16assignments-1worker "$SWEEP/16assignments-1worker/capture" \
  16assignments-2workers "$SWEEP/16assignments-2workers/capture" \
  16assignments-3workers "$SWEEP/16assignments-3workers/capture" \
  16assignments-4workers "$SWEEP/16assignments-4workers/capture"
```

Retain environment seals and root mode audits unchanged alongside this owner's archived evidence. Check all seven modes contain the same thirty declared cases (210 summary rows per clock) and all 840 warmup/measured scientific comparisons. Verify original/archive and generator/output hashes.

The manuscript owner can consume the resulting qualified summary sources directly. Existing `MeasuredBatchSummarySource` owns each actual serial denominator, `build_measured` supplies workflow details/distribution tables, and `FIGURE_STYLE.generate_average_point_figures` supplies arithmetic-mean bars, all thirty workflow dots, median lines, minimum/median/mean/maximum annotations and linear/log PNG/SVG variants. No new painter is required. Do not call the singlewell-only publication entry point and claim it contains the entire sweep. Preserve the current reading copies and prior archives until the paper owner integrates qualified data.

Open one artifact PR with `Fixes #1100`; keep it draft while modes are pending. No separate manuscript PR, fabricated missing rows or mixed historical cohorts.

## Existing-owner render command

Once all seven modes qualify, archive `render_sweep.py` and the prepared protocol manifest under the record's `protocol/` directory, then run:

```sh
"$PYTHON" "$RECORD/protocol/render_sweep.py" --record "$RECORD" --protocol-manifest "$RECORD/protocol/protocol-manifest.json" --output-dir "$RECORD/figures"
```

The script delegates details and distributions to `build_measured` and May bars/points to `FIGURE_STYLE.generate_average_point_figures`. It retains thirty real workflow points per mode, without the artificial Average row. Execution and total each receive separate May-schedule and fixed16 CP-relative plots. Fixed16 also receives OpenHCS-one-worker-relative scaling plots, with efficiency fractions in `derived_workflow_metrics.csv` under the `efficiency` directory (`efficiency_unit_fraction`, 1 = ideal). Efficiency is not drawn with the existing painter's x suffix. Every output retains source/code hash provenance. This script is the reproducible data-artifact consumer; the manuscript owner can integrate these assets without another plotting implementation.

The archive owner is a byte-exact snapshot of the newer existing `/home/ts/.local/state/openhcs-maintenance/20261006/final-measured-figure-preparation-v1/archive_converted_modes.py` (SHA256 `e9f19f615e9e52f55383a963933df7702ee0cfd185186d86945ea08986449522`). It derives native origin from the original `NativeBatchRequest.output_root` authority and retains command-selected case qualification. Fresh and reused native reports use that same existing authority; no archive patch or auxiliary reuse-path dependency is introduced. Historical archive code remains unchanged.
