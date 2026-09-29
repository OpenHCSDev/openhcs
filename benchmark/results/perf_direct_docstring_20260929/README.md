# Direct docstring parser: official30 one-well benchmark (2026-09-29)

The changed dependency is python-introspect `5bb79d5` → `4e8f8bd` ([upstream PR #4](https://github.com/OpenHCSDev/python-introspect/pull/4)). The two fresh-server runs used the same OpenHCS integration checkout, containing the separately proposed single-thread performance changes through `38ec4fbc1`; only the python-introspect checkout changed between control and direct-parser runs. The direct-parser checkout was then committed as `8ace32939` for the reused-server run. This report accompanies the isolated submodule bump in [OpenHCS PR #175](https://github.com/OpenHCSDev/openhcs/pull/175).

All 30 official portable cases succeeded in each run. `control_fresh.csv` and `direct_fresh.csv` use a fresh client-owned ZMQ server per observation. `direct_reused.csv` uses one client-owned server across the sweep. `native_cp_summary.csv` is the fresh native CellProfiler 4.2.8.1 baseline used to project native execution time by well count. Each CSV carries `server_lifecycle` where applicable.

| 30-case sum (s) | Control fresh | Direct fresh | Direct reused |
| --- | ---: | ---: | ---: |
| Server compilation jobs | 100.065 | 58.632 | 22.607 |
| Server execution jobs | 103.767 | 93.115 | 93.564 |
| Non-job (`total - compile - execute`) | 171.189 | 160.110 | 25.773 |
| Per-observation `total_seconds` | 375.020 | 311.858 | 141.944 |

All 30 cases compiled faster after the parser change; the median case saved 1.342 s in compilation. The direct-parser patch changes compilation metadata extraction, not runtime execution. The execution and fresh-server non-job differences are observed variation and should not be attributed to the patch. The reused-server total excludes its once-per-sweep startup/shutdown, while the fresh-server total includes startup/shutdown for every observation. Reuse also benefits from warm in-process compilation and cache state, so the 169.914 s fresh-to-reused difference is not a measured whole-sweep wall-time speedup.

A targeted A/B/A check gave ExampleFly compile times 3.989 → 2.260 → 3.976 s and advanced segmentation 6.259 → 3.176 → 6.303 s (old/direct/old). Direct parsing produced identical `DocstringInfo` for 114 real CellProfiler callables. The upstream test suite passed 127 tests.

`direct_fresh_native_relative.png` and `direct_reused_native_relative.png` show **execution** speedup relative to the native CP baseline. They do not depict total time or multiple-well scaling. The completed four-mode native-relative execution sweep predating this compile-only change is stored separately at `official30-four-modes-native-relative-fresh-v2-20260928` in the benchmark run workspace; a new 120-observation sweep was intentionally not used as evidence for this patch because its execution path did not change.

Fresh command (repeat with `--reuse-execution-server` for the reused run):

```bash
OPENHCS_CPU_ONLY=true .venv/bin/python scripts/benchmark_cppipe_well_throughput.py \
  --manifest benchmark/manifests/official30_portable_axis1.json \
  --output-dir /path/to/output \
  --native-summary-csv benchmark/results/perf_direct_docstring_20260929/native_cp_summary.csv \
  --mode 1w_1t --figures
```
