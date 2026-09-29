# Exact CellProfiler owners and scoped lookups: fresh-server official30 1w_1t (2026-09-29)

This report accompanies [OpenHCS issue #188](https://github.com/OpenHCSDev/openhcs/issues/188) and [draft PR #189](https://github.com/OpenHCSDev/openhcs/pull/189). The control is integration commit `d18dbc877`, including lazy PolyStore NGFF imports at submodule commit `11269ed`. The final candidate adds exact CellProfiler callable lookup, compiler preparation limited to registered preparation families, experiment-measurement dispatch through the owner recorded on each table, and an owner-scoped lookup dialect for `RelateObjects` table queries. Each observation uses one well, one OpenHCS thread, a `fork` worker, and a fresh client-owned ZMQ server.

The control profile attributed **24.87 of 89.31 compilation seconds** to CellProfiler invocation-contract provider calls across 30 cases. The first provider pass accounted for 22.58 seconds. On the three-step CombineObjects case, its first exact contract lookup triggered full lazy discovery of the CellProfiler module catalog and took 1.014 seconds. Resolving the exact callable module avoids discovery there; skipping registries without compiler preparation hooks prevents the same work from moving into callable preparation.

An intermediate exact-lookup-only run improved compilation but moved some catalog discovery into timed execution. Profiling its WoundHealing spreadsheet export traced **0.77 seconds** to `derive_experiment_measurement_tables`: that method searched the full registry to find a class already stored in each `MeasurementTable.measurement_feature_owner`. Dispatching directly through the registered owner lowered the WoundHealing export step **0.555 → 0.004 seconds** and the quality-control database export step **0.872 → 0.066 seconds** in the retained runs. Explicit catalog/discovery APIs still discover the full registry.

The recorded-owner run still triggered full catalog discovery on the first `RelateObjects` child-feature query. A representative `ExampleSpeckles` cProfile attributed **0.969 of 1.048 seconds** in that module call to resolving global measurement category prefixes. The final candidate derives a lookup dialect from the exact owner on each upstream table and falls back to the global dialect when a table has no registered owner. The four affected `RelateObjects` steps together fell by **2.105 seconds** in the full sweep: Speckles **0.766 → 0.038**, UntangleWormsBrightField **0.548 → 0.055**, advanced segmentation **1.472 → 1.077**, and beginner segmentation **1.234 → 0.747**. This is the direct step-level evidence; unrelated step variation affects aggregate execution.

| Sum of 30 fresh-server observations (seconds) | Control | Lookup only | Recorded owner | Scoped lookup | Final minus control |
| --- | ---: | ---: | ---: | ---: | ---: |
| Server compilation jobs | 89.271 | 75.909 | 75.797 | 75.759 | **-13.512** |
| Server execution jobs | 84.018 | 91.049 | 86.747 | 85.067 | +1.049 |
| Other measured time | 67.294 | 68.564 | 65.146 | 64.329 | -2.965 |
| Per-observation total | 240.582 | 235.522 | 227.690 | 225.156 | **-15.426** |

All 30 final cases succeeded. Compilation fell in 28 cases (paired median **-0.556 seconds**) and total time fell in 27 cases (paired median **-0.584 seconds**). Execution fell in 18 cases (paired median **-0.013 seconds**), but its aggregate was 1.049 seconds higher than control, so the suite-level win remains in total time. The 110 result files have identical paths and bytes on control and final candidate. Both intermediate runs also achieved 110/110 byte parity.

A warmed control/candidate/candidate/control comparison on the short CombineObjects case used the exact parent commit in a separate worktree. For the lookup-only candidate, mean compilation changed **2.151 → 1.309 seconds**, execution **0.158 → 0.283 seconds**, and measured total **4.487 → 3.424 seconds**. Those timings establish the short-case gain and the reason for the recorded-owner follow-up. The first colocalization run in a newly created control worktree incurred unrelated cold JIT work and was excluded from the paired claim.

The global measurement dialect still retains its complete catalog semantics for explicit and unowned lookups. The native CP 4.2.8.1 total-phase 5× reference is **263.871 seconds** for these cases. Its timer has a different preparation boundary, so the figure shows it as context rather than a strict end-to-end ratio.

![Fresh-server total-time breakdown and native reference](fresh_server_total_breakdown.png)

![Per-case compilation and execution changes](per_case_phase_deltas.png)

`control.csv`, `lookup_only.csv`, `candidate.csv`, `scoped.csv`, and `abba.csv` retain the measurements; `plot.py` regenerates both figures. Raw full-run trees and receipts are under `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-ome-zarr-full-candidate-20260929`, `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-cp-registry-full-20260929`, `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-cp-owner-full-20260929`, and `/home/ts/code/projects/openhcs-benchmark-runs/perf-relate-owner-full-20260929`. The warmed short-case runs are under `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-cp-registry-abba-3-20260929`.

All 315 directly affected ownership, lookup, relationship, export, and runtime-adapter tests passed after the final change; 831 focused ownership, export, and compilation tests had passed before the scoped-lookup follow-up. Fresh-process regression tests confirm that exact callable ownership, callable preparation, experiment-measurement dispatch, and recorded-owner lookups leave unrelated CellProfiler modules unimported. The full final run used the ordinary ZMQ completion path and achieved 110/110 byte parity. Black, selected Ruff checks, and whitespace checks passed.

Reproduce the full run with:

```bash
OPENHCS_CPU_ONLY=true \
OPENHCS_REFERENCE_EXPORT_PIPELINES_ROOT=/absolute/path/to/benchmark/reference_exports/official30_value_completion_20260914 \
.venv/bin/python scripts/benchmark_cppipe_well_throughput.py \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /path/to/output \
  --native-summary-csv benchmark/results/perf_lazy_catalog_20260929/native_cp_summary.csv \
  --mode 1w_1t
```
