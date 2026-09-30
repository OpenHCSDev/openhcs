# Prepare the execution server before pipeline readiness

Pipeline total excludes ZMQ server startup and shutdown. Both benchmark commands now use a ready retained endpoint by default; `--no-reuse-execution-server` explicitly selects a separate cold-server diagnostic. Distinct lifecycle hashes prevent resuming or plotting mixed timing boundaries. The API's existing explicit lifecycle choices remain available.

Every execution-server start warms the complete unified registry before binding/readiness. Direct starts and the launcher consume the same catalogue future. Existing asynchronous catalogue controls retain that owner. Cache workers remain bounded fork children, persistent kernel caches are shared, and the warmed parent owns its process-local callable readiness. Genuine worker/callable completions reach the startup journal; no inflated inactivity timeout or invented heartbeat.

Source `3d98ad2c31d5f144f76e2e3878adcc69757bd7dc`, normally merged with main `c42d9bf5d`, including its recorded ZMQRuntime `2c68a114` and other seven dependency gitlinks. [Installed provenance](validation/perf-server-startup-installed-provenance-20260930.json) binds the wheel and all six installed source modules. Imports resolve outside the checkout to the installed target. No timed observation overlaps audits, builds, tests, profilers or other benchmarks.

| Installed ordinary 1w_1t pipeline | Compilation | Execution | Pipeline total |
|---|---:|---:|---:|
| ImagingFlow | 1.372s | 13.863s | 15.912s |

Pipeline overhead beyond compilation and execution is 0.676s. Complete export is byte identical to current-main control (SHA256 `517057a4b018195cc4c57e8503be63a378a8306eb2ecc303d4a025b6eab6dd1c`). Native execution ratio 4.443 uses the earlier physical 61.602s CP single-sample observation; native CP was not rerun for this lifecycle patch. These one-well results make no claim about multiwell scaling.

The fresh empty-cache diagnostic also completed with 1.819s compilation after startup preparation. Its 54.897s cold-server total includes startup and shutdown and **is not pipeline time**. Moving preparation before readiness is an intentional lifecycle correction, not evidence that cold boot or mathematical execution became faster. The initial failed diagnostic is retained: without live progress, the existing 15s inactivity deadline expired. Its standalone CLI exit0 did not represent a successful observation; status/error fields are authoritative. The corrected installed canonical CLI exits1 on its recorded 3D failure.

The 3D monolayer refresh failed in SaveImages (`image_to_save` missing). An independent control on unmodified main reproduces the identical defect; [issue #287](https://github.com/OpenHCSDev/openhcs/issues/287) owns its repair. No failed-row zero timing is treated as a performance result. ImagingFlow is the largest absolute execution cost; this 3D case was the weakest native-relative execution ratio in the saved 30-case frontier.

Validation: 987 startup/kernel/processing/numerical consumer checks pass; 85 benchmark command/measurement checks pass. These include live progress while the shared future is pending, main-thread warming before bind, no second warmup, failure/cancellation preventing readiness, exact owned cache-worker reaping under SIGTERM, completion progress after child reaping without parent readiness, default ready-server and explicit diagnostic routing. R0 has zero positive deltas across all seven changed production paths, and R1 has no increases. [Coverage and original artifact hashes](validation/structural_checks.json) retain all original classes and 12 OPEN unprojected rows; source/syntax transactions and scoped ratchets do not constitute global semantic proof. The decision and owner migration are in [architecture.md](architecture.md).

Actual installed acceptance uses `openhcs-benchmark run-well-throughput --manifest .../official30_portable_axis1.json --preset 1w_1t --case ExampleImagingFlowCytometryObjectsInGrid --case cp_tutorial_3d_monolayer --native-summary-csv .../official30-native-complete-fresh-20260928/summary.csv` from `/tmp`, with an initially absent NUMBA_CACHE_DIR and installed-target PYTHONPATH. Exact commands, ordinary rows, scientific receipt and failed controls are under [observations](observations/); [analysis.json](analysis.json) records raw scopes and hashes. Full original outputs/logs are retained under `/home/ts/code/projects/openhcs-benchmark-runs`.

Fixes #286; Refs #162 and #287. Performance work remains active.
