# Exact CellProfiler lookup: fresh-server official30 1w_1t (2026-09-29)

This investigation accompanies [OpenHCS issue #188](https://github.com/OpenHCSDev/openhcs/issues/188). The control is integration commit `d18dbc877`, including the lazy PolyStore NGFF import at submodule commit `11269ed`. The candidate changes only exact CellProfiler declaration lookup and compiler preparation of AutoRegister families. Each official30 observation uses one well, one OpenHCS thread, a `fork` worker, and a fresh client-owned ZMQ server. The earlier native CellProfiler 4.2.8.1 reference uses its own timer boundary.

Profiling the control attributed **24.87 of 89.31 compilation seconds** to CellProfiler invocation-contract provider calls across 30 cases. The first provider pass accounted for 22.58 seconds. On the three-step CombineObjects case, the first exact contract lookup triggered full lazy discovery of the CellProfiler module catalog and took 1.014 seconds. A lookup-only prototype simply moved that cost into callable preparation, so it was rejected. The candidate imports the callable's exact module and searches the registered declarations already loaded; compiler preparation now touches only registries with `CompilerPreparedAutoRegisterFamily` hooks. Explicit catalog and discovery APIs still discover the full registry.

| Sum of 30 fresh-server observations (seconds) | Control | Candidate | Difference |
| --- | ---: | ---: | ---: |
| Server compilation jobs | 89.271 | 75.909 | **-13.362** |
| Server execution jobs | 84.018 | 91.049 | +7.031 |
| Other measured time | 67.294 | 68.564 | +1.270 |
| Per-observation total | 240.582 | 235.522 | -5.060 |

All 30 cases succeeded; compilation fell in every case (paired median **-0.538 seconds**, range -0.807 to -0.006). All 110 result files have identical paths and bytes. Execution rose in 24 cases, so this change is **not** an execution-only improvement. The total sum fell by 5.06 seconds, but only 14 cases were individually faster; suite-wide total gain is modest relative to its run variation. The first-call execution path appears to absorb some work no longer done by broad catalog discovery. This tradeoff needs review before promotion.

A warmed control/candidate/candidate/control comparison on the short CombineObjects case used the exact parent commit in a separate worktree. Mean compilation changed **2.151 → 1.309 seconds**, execution **0.158 → 0.283 seconds**, and measured total **4.487 → 3.424 seconds**. This confirms a useful short-pipeline total gain alongside the execution regression. A newly created control worktree incurred unrelated cold JIT work in its first colocalization run, so that run is excluded from the paired claim.

The native CP total-phase 5× reference is 263.871 seconds for these 30 cases. Both OpenHCS variants remain below it; those native and OpenHCS total timers have different preparation boundaries. The figures show the native reference for context rather than a strict end-to-end speedup claim.

![Fresh-server total-time breakdown and native reference](fresh_server_total_breakdown.png)

![Per-case compilation and execution shifts](per_case_phase_deltas.png)

`control.csv`, `candidate.csv`, and `abba.csv` retain the observations; `plot.py` regenerates both figures. Full raw trees and receipts are under `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-ome-zarr-full-candidate-20260929` and `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-cp-registry-full-20260929`. The warmed short-case raw runs are under `/home/ts/code/projects/openhcs-benchmark-runs/perf-lazy-cp-registry-abba-3-20260929`.

Validation: 787 focused unit and compilation tests passed. A fresh-process regression test confirms that exact ownership lookup and callable preparation leave unrelated CellProfiler backend modules unimported. Black, selected Ruff checks, and whitespace checks passed. The official30 run used the ordinary ZMQ completion path and achieved 110/110 byte parity.

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
