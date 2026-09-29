# Lazy execution-server function catalog: official30 1w_1t (2026-09-29)

This report accompanies the lazy catalog initialization change for [OpenHCS issue #165](https://github.com/OpenHCSDev/openhcs/issues/165). Both fresh-server runs used the same CPU-only integration checkout and native CP 4.2.8.1 reference. The control CSV is the completed direct-docstring-parser run; the new run changes only execution-server catalog initialization and its import preflight. Each observation owns a fresh ZMQ server, so `total_seconds` includes that server's startup and shutdown. The 1w_1t preset uses one well and one OpenHCS thread.

All 30 cases succeeded on the final code path. Every case had a lower total, with a paired median saving of 1.171 seconds. All 110 files under the produced `results` directories were byte-identical to the control outputs.

| Sum over 30 observations (seconds) | Control fresh | Lazy catalog fresh | Difference |
| --- | ---: | ---: | ---: |
| Server compilation jobs | 58.632 | 83.759 | +25.126 |
| Server execution jobs | 93.115 | 89.219 | -3.896 |
| Other measured time (`total - compile - execute`) | 160.110 | 101.289 | -58.822 |
| Per-observation total | 311.858 | 274.266 | **-37.592** |

The patch moves some registry work into compilation; the execution-job difference is run variation, not a claimed effect of this initialization change. A separately timed full CLI invocation took 296.684 seconds. That wall time includes source preparation outside the per-observation timer and has no matched control wall measurement. The native CP total-phase reference sums to 1,319.357 seconds, making its 5× reference line 263.871 seconds; the new per-observation sum remains 10.395 seconds above that line. The native total-phase and OpenHCS well-throughput timers have different preparation boundaries, so the line is a reference rather than a like-for-like end-to-end ratio.

`fresh_total_breakdown.png` shows the measured time shift and native reference. `lazy_native_execution_speedup.png` and `lazy_native_execution_cdf.png` show execution-only ratios relative to native CP; the patch does not target those ratios. The completed multi-well native-relative scaling figures predate this startup-only change and remain at `/home/ts/code/projects/openhcs-benchmark-runs/official30-four-modes-native-relative-fresh-v2-20260928`.

Validation: 104 focused tests passed after the final import-guard change. A live client connected in 1.795 seconds and fetched the complete 266-function catalog on demand in a further 1.616 seconds. The benchmark's ordinary ZMQ outcome and progress evidence path was used throughout.

Fresh benchmark command:

```bash
OPENHCS_CPU_ONLY=true .venv/bin/python scripts/benchmark_cppipe_well_throughput.py \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /path/to/output \
  --native-summary-csv benchmark/results/perf_lazy_catalog_20260929/native_cp_summary.csv \
  --mode 1w_1t
```
