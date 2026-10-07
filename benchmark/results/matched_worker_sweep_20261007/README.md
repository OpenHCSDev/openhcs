# Matched full-cohort worker sweep — issue 1100

Prepared record: `matched_worker_sweep_20261007`, source `67cdcc3dea60c611f3bb964d1b343c931a589e46`.
The original v1 preparation preceded all mode terminals. The current partial record includes qualified singlewell evidence, while the actual eight-assignment capture and future target modes remain incomplete. Append only completed, unchanged-source captures after strict conversion; keep pending modes explicit. This is not a completed scaling sweep.

| Archive mode | Assignments | OpenHCS workers | CellProfiler baseline | Use |
| --- | ---: | ---: | --- | --- |
| singlewell | 1 | 1 | Measured one-process, 1 assignment | May point 1; fresh single-sample cohort |
| 8assignments-2workers | 8 | 2 | Measured one-process, 8 assignments | May point 2; projection anchor |
| 12assignments-3workers | 12 | 3 | Projected from measured 8-assignment batch | May point 3; shared fixed-workload endpoint |
| 16assignments-4workers | 16 | 4 | Projected from measured 8-assignment batch | May point 4 |
| 12assignments-1worker | 12 | 1 | Projected from measured 8-assignment batch | Fixed-workload reference |
| 12assignments-2workers | 12 | 2 | Projected from measured 8-assignment batch | Fixed-workload scaling |
| 12assignments-4workers | 12 | 4 | Projected from measured 8-assignment batch | Fixed-workload scaling |

All modes cover the same declared thirty workflows on one production revision, with one warmup and three measured repetitions. Each repeated assignment uses the selected source sample; repeated assignments are not independent biological wells. CellProfiler runs in one stock process. Its one- and eight-assignment baselines are measured; the requested twelve- and sixteen-assignment references are explicitly projected from the genuine eight-assignment observations. The user authorized this prospective change to avoid another long serial-native sweep. Every OpenHCS configuration remains measured, including all four fixed-twelve worker counts. No independently parallelized native-process comparison is used.

Projection is a separate derived source view, never fabricated native observations. Original `native_report.json` and its actual eight-assignment requests, outputs and clocks stay unchanged. The derived reference retains the anchor report digest, source/target assignment counts and declared model/inputs. The approved model is `retained-first-batch-plus-warm-assignments-v1`. For target assignment count N, execution is the actual eight-assignment first observation (repetition −1) plus `(N − 8) × median(actual eight-assignment execution repetitions 0–2) / 8`. Prepared invocation adds the actual eight-assignment first observation’s pre-pipeline overhead once. Internal first-use initialization inside execution is included; external process/JVM/server startup remains excluded. There is one native first observation, not three fabricated cold repetitions, and no actual target native observation for projected twelve/sixteen references.

The headline policy for every mode compares first-use-inclusive CP batch execution/prepared invocation with the median of three measured OpenHCS runs. Metadata records native first-observation count 1, OpenHCS observation count 3, and target native observation count 0 for projected references. Genuine native steady repetitions remain retained as calibration/source evidence, not a separate headline. Existing warm-native median summaries remain unchanged; new first-use views are separately qualified.

The cold-first projection has diagnostic validation, not thirty-workflow measured target validation. Retained two-sample calibration across three representative workflows and actual eight/twelve/sixteen diagnostic batches supported the cold-first form within 5.21%; same-campaign eight-anchor target predictions were within 7.06%. Applying an older retained anchor against newly run diagnostics underpredicted by 3–14%. Keep all diagnostic rows and source/campaign identities, disclose these limits, and do not present the projected thirty-workflow cohort as thirty measured native target batches.

The May schedule changes workload with worker count: 1/1, 2/8, 3/12 and 4/16 workers/assignments. Its CP-relative ratios reproduce the requested workload schedule, with projected CP references explicitly marked for twelve/sixteen assignments; they are not fixed-workload parallel efficiency. The separate twelve-assignment comparison uses OpenHCS one-worker execution time divided by its two-, three- or four-worker execution time; efficiency divides that speedup by worker count. Keep these interpretations separate. The three-worker/twelve-assignment capture is shared rather than recaptured. Twelve is derived as the least common multiple of the May worker counts (1, 2, 3 and 4), so each fixed workload partitions evenly; sixteen assignments on three workers would have imposed a 6/5/5-task granularity limit.

Execution covers CellProfiler's pipeline call, including prepare-run, prepare-group, module work and post-run, versus OpenHCS's complete server pipeline job, including saving/publication and plate exports. Total compares native prepared invocation with OpenHCS's disjoint compilation-plus-execution client submission/wait phases. Exclude process/JVM/server startup, function-library readiness, warmup and scientific comparison; never add nested server/worker durations again. Headline anchor comparisons use one genuine first-use native batch observation and the median of three OpenHCS repetitions. Projected comparisons derive a first-use-inclusive native reference through the admitted model and retain its genuine anchor observations; they are not additional measured native runs.

RAM is unavailable: the retained matched producer/native report contracts do not collect process-tree peak RSS. Blank memory fields remain blank; May RAM is not substituted. If genuine separately observed memory becomes available, retain its measurement scope and original custody before making a memory plot.

Qualified layout uses existing archive ownership:

- `data/MODE/{execution_summary.csv,total_summary.csv,summary_custody.json}`: immutable actual-warm anchor summaries.
- `data/first_use/MODE/{first_use_execution_summary.csv,first_use_total_summary.csv,summary_custody.json}`: separately admitted first-use/projected headline views.
- `protocol/MODE/`: original command, controller, terminal, declared manifest and environment/source seal; common converter and archive owner alongside.
- `reports/MODE/CASE/`: original lightweight native/candidate/provenance reports, progress and warmup/measured phase receipts. Science image/CSV/database payloads stay at their original capture locations rather than being duplicated.

Original custody is preserved byte for byte. Conversion must reject absent terminal, nonzero exit, changed/dirty source, mixed environment, incomplete assignments/repetitions, wrong worker evidence, missing output inventories and any scientific difference. The protocol converter derives serial-native and candidate-worker counts independently from their command/provenance owners; optional external native calibration still requires matching worker counts. No historical converter or frozen record is edited.

## Current delivery status

The `singlewell` mode is complete and qualified: all thirty declared workflows, warmup plus three measured repetitions, and all 120 complete scientific comparisons passed on production source `67cdcc3dea60c611f3bb964d1b343c931a589e46`. Its original summaries and lightweight custody are archived here. The actual eight-assignment/two-worker mode is running; the remaining five OpenHCS modes are pending under the prospective projected-reference policy. This partial record is not a completed scaling sweep and does not replace the current manuscript record. The protocol manifest records the original preparation state, not current measurement admission; each mode’s `summary_custody.json` and original terminal are the authorities.

## Post-terminal first-use commands

The v1 measured-warm summaries and converter are immutable. The v2 converter is a new namespace that admits genuine first-use native observations or explicitly derived references, without rewriting original native reports. The archived `protocol/v2/run-revised-sweep.py` is the primary coordinated workflow; it serializes future captures and conversion with the benchmark-only overlay shown below. Do not launch another copy alongside the owned live sweep. The individual post-terminal conversion commands below reproduce its source admission without launching scientific captures.

```sh
SWEEP=/home/ts/.local/state/openhcs-maintenance/20261007/issue1100-matched-sweep-v1
ARTIFACT_ROOT=/home/ts/code/projects/openhcs-cohort-qualification-main429-20261002
RUNTIME_ROOT=/home/ts/.local/state/openhcs-maintenance/20261004/intensity-batch-maxima-source
RECORD="$ARTIFACT_ROOT/benchmark/results/matched_worker_sweep_20261007"
PYTHON=/home/ts/code/projects/openhcs/.venv/bin/python
CONVERTER="$RECORD/protocol/v2/convert_matched_reports.py"

# Overlay only benchmark modules; retain canonical OpenHCS/runtime source.
convert_first_use() {
  taskset -c 0 "$PYTHON" -B -c 'import sys;sys.path.insert(0,sys.argv.pop(1));import benchmark,runpy;benchmark.__path__=[sys.argv.pop(1)];sys.argv=sys.argv[1:];runpy.run_path(sys.argv[0],run_name="__main__")' "$RUNTIME_ROOT" "$ARTIFACT_ROOT/benchmark" "$CONVERTER" "$@"
}

# Invoke only after each original mode reaches terminal0; output must be fresh.
convert_first_use --suite-dir "$SWEEP/1assignment-1worker/capture" --output-dir "$SWEEP/1assignment-1worker/capture/first_use_converted"
for MODE in 8assignments-2workers 12assignments-3workers 12assignments-1worker 12assignments-2workers 12assignments-4workers 16assignments-4workers; do
  convert_first_use --scaling --suite-dir "$SWEEP/$MODE/capture" --output-dir "$SWEEP/$MODE/capture/first_use_converted"
done
```

After PASS, retain `first_use_execution_summary.csv`, `first_use_total_summary.csv` and `summary_custody.json` unchanged under `data/first_use/MODE`; map capture `1assignment-1worker` to archive `singlewell`. Keep the original actual-warm files at `data/MODE` and all genuine native/candidate/science/progress receipts unchanged. The archive owner handles only completed subsets: pending modes cannot be fabricated to make a plotting table rectangular.

The first-use table's legacy `median_native_*` fields contain the explicitly declared native first-use reference, not a median of three native observations. `n` and `equivalent_count` describe three OpenHCS observations; `native_observation_count` is 1 for measured first-batch targets and 0 for projected targets. The one genuine source first observation and three source warm observations remain separate in custody. All seven OpenHCS modes must contain the same thirty workflows and all 840 warmup/measured scientific comparisons; only CP1/CP8 are measured target baselines.

Retain converter/controller/environment/source identities and byte-verifiable original anchors. `protocol/MODE` remains the manifest role for both immutable warm summaries and first-use views. Projection validation diagnostics remain source/campaign-qualified rather than being represented as additional target observations.

The manuscript owner can consume the resulting qualified summary sources directly. Existing `MeasuredBatchSummarySource` owns measured serial anchors; generic `SummarySource` supplies explicitly admitted projected-reference views without pretending they are measured-native custody, `build_measured` supplies workflow details/distribution tables, and `FIGURE_STYLE.generate_average_point_figures` supplies arithmetic-mean bars, all thirty workflow dots, median lines, minimum/median/mean/maximum annotations and linear/log PNG/SVG variants. No new painter is required. Do not call the singlewell-only publication entry point and claim it contains the entire sweep. Preserve the current reading copies and prior archives until the paper owner integrates qualified data.

Open one artifact PR with `Fixes #1100`; keep it draft while modes are pending. No separate manuscript PR, fabricated missing rows/clocks or mixed historical cohorts. Draft PR1101 is the artifact delivery for issue1100.

## Existing-owner render command

Once all seven modes qualify, archive `render_sweep.py` and the prepared protocol manifest under the record's `protocol/` directory, then run:

```sh
"$PYTHON" "$RECORD/protocol/render_sweep.py" --record "$RECORD" --protocol-manifest "$RECORD/protocol/v2/protocol-manifest.json" --output-dir "$RECORD/figures"
```

The renderer delegates labeled first-use detail rows and distributions to the existing report painters, and May bars/points to `FIGURE_STYLE.generate_average_point_figures`. The warm-native-only `build_measured` entry point is not used to falsely admit first-use or projected views. It retains thirty real workflow points per mode, without the artificial Average row. Execution and total each receive separate May-schedule and fixed12 CP-relative plots, labeled measured CP1/CP8 and projected CP12/CP16. Every plot retains a `first_use_policy.json` with that reference-kind and observation-count policy. Fixed12 also receives OpenHCS-one-worker-relative scaling plots, with efficiency fractions in `derived_workflow_metrics.csv` under the `efficiency` directory (`efficiency_unit_fraction`, 1 = ideal). Efficiency is not drawn with the existing painter's x suffix. Every output retains source/code hash provenance. This script is the reproducible data-artifact consumer; the manuscript owner can integrate these assets without another plotting implementation.

The historical v1 archive owner is a byte-exact snapshot of the newer existing `/home/ts/.local/state/openhcs-maintenance/20261006/final-measured-figure-preparation-v1/archive_converted_modes.py` (SHA256 `e9f19f615e9e52f55383a963933df7702ee0cfd185186d86945ea08986449522`). It derives native origin from the original `NativeBatchRequest.output_root` authority and retains command-selected case qualification. That v1 snapshot and its original summaries remain unchanged. The separate `protocol/v2/archive_converted_modes.py` archives the first-use CSV/custody views under `data/first_use/MODE`, retains original raw reports and `protocol/MODE` manifest paths, and verifies byte-identical existing one/eight-assignment originals. Projected references remain derived declarations rather than fabricated native observations.

## Measured one-versus-eight calibration

Retain a thirty-workflow diagnostic table of actual first-batch CP execution and prepared-invocation durations for one and eight assignments, together with `CP8_first / (8 × CP1_first)` and separately retained warm-source medians. The main comparison remains one first-use-inclusive native batch reference, not separate cold/warm headline results. Render calibration ratios with the existing May painter once both genuine cohorts are complete. CP1 uses CPU affinity with one slot, while CP8 uses four slots. Their ratio combines different affinity and batch scope; it cannot establish batching savings alone. The separate [cold-first model validation](calibration/cold_first/cold-first-model-validation.json) compares matching four-slot affinity across three representative workflows and nine target-count cases, within 5.21%, not all thirty workflows. Same-campaign eight-anchor target errors were within 7.06%; older-anchor cross-campaign predictions underpredicted by 3–14%. This diagnostic evidence justifies the declared projection with explicit scope and variation; it does not manufacture measured target native timings. Fixed-twelve OpenHCS speedup and efficiency use only genuine OpenHCS one-/n-worker clocks and remain independent of that projection law.

Use the renderer’s `--calibration-only` option after both actual anchor cohorts qualify to publish the genuine one-versus-eight table and plot without claiming unfinished target modes are ready.
