# Warm-batch timing pilot, 2026-09-15

This is infrastructure validation for a future matched benchmark. It is not a
replacement for Supplementary Figure 6 and does not establish a speedup.

## Workload and execution geometry

The pilot imports the pinned CellProfiler tutorial `Translocation_final.cppipe`
through the existing comparison manifest and source-binding workspace. It uses
eight genuine wells, A01, A12, B01, B12, C01, C12, D01 and D12: one site and two
channels in each well, hence eight native image assignments. No images or wells
are synthetically repeated. The pipeline disables Groups and emits SQLite
measurements, CellProfiler Analyst properties and an overlay TIFF per assignment.

Native input selection, imported metadata rewriting and headless export policy
come from `NativeCellProfilerInputDomainStrategy` and
`HeadlessCellProfilerPipelinePolicy`; the driver does not rewrite biological
analysis settings. The native process starts Java and loads the pipeline once,
then executes a complete warm-up batch and three complete observed batches.

OpenHCS uses one isolated production ZMQ execution server and `num_workers=1`.
At this worker count, the production worker-executor owner executes inline in the
server; this is not a pool of external benchmark-only OpenHCS processes. Source
workspace creation and server/catalog startup precede the observations. Each
batch is compiled before its execution timer, then submitted by compile-artifact
ID. Production consumes that artifact, so subsequent batches compile again;
debug replay retention is not enabled for the benchmark. A complete first batch
is planned as warm-up; the following three are planned observations. The live
probe stopped at strict validation of that first batch. Requested exports remain
enabled, and equivalence checks use the actual resulting exports.

The probe also writes an additional terminal `CellAndNucleiOverlay.tif` per well.
Setting `materialize_runtime_artifacts=False` preserves requested exports but did
not suppress these terminal copies in the live probe. Equal requested export
lists are therefore insufficient to prove equal write work. A declared policy
for terminal/main-flow persistence must be resolved before a matched comparison.

Both sides run sequentially, not concurrently with one another, with
OMP, OpenBLAS, MKL, NumExpr and vecLib thread limits set to one. Native and
candidate NumPy CPU-dispatch controls are retained in the run receipt.

## Timing membership

| Interval | Starts | Ends | Interpretation |
| --- | --- | --- | --- |
| Native invocation | Before iterating `Pipeline.run_with_yield` | Generator completion, including `post_run` and `end_run` | Preparation and complete batch execution; imports/Java startup excluded |
| Native module interval | First public `status_callback`, immediately before first `run_module` | Same generator completion | Excludes `prepare_run` and first `prepare_group`; includes NamesAndTypes image-provider creation and subsequent pixel reads/modules/exports |
| OpenHCS compile API | Compile request submission | Compile completion observed | Recorded separately from execution |
| OpenHCS invocation | Prepared execution request submission | Successful completion observed by client | Request processing, worker setup, complete batch execution and completion observation |
| OpenHCS axis interval | First source `AXIS_STARTED` timestamp | Successful completion observed by client | Excludes earlier request/worker/context setup; includes first axis step processing and plate-scoped exports |

Source receipts: CellProfiler's `run_with_yield` calls `prepare_run`, constructs
and enters its group, then invokes `status_callback` before each module's
`run_module`. NamesAndTypes creates image providers in its `run` method, after
that callback. OpenHCS emits `AXIS_STARTED` before entering the first context's
step loop. Completion of `execute_compiled_plate_request` includes plate-scoped
steps, analysis consolidation and completed-plate metadata; the ZMQ lifecycle
marks the execution complete only after `execute_task` returns.

The event intervals are not yet proven identical. Native `prepare_run` can
perform source/header inspection; OpenHCS compilation and pre-axis setup do
different work. The OpenHCS endpoint is a client-observed completion, so its
interval includes polling/transport delay. Raw progress events, a 50 ms requested
poll interval and both coarse invocation durations are retained. No ratio should
be derived from these intervals until timing membership is settled explicitly.

## Extension required before a corpus comparison

1. Define indivisible partition units from declared source groups, stacks and
   time series. Preserve group-dependent illumination, tracking and plate-wide
   export semantics; do not split or repeat arbitrary image sets.
2. For matched concurrency N, use one production OpenHCS server with N worker
   lanes and N native batch jobs, not N external inline OpenHCS instances.
   Retain actual assignment counts and native batch ranges.
3. Preserve native global image identities when partitioning. Comparing native
   per-job SQLite outputs with a production plate-wide export requires a
   contract-derived table union or another equivalent whole-plate observation.
   This pilot does not introduce or pretend to validate that union.
4. Settle a common completion/start boundary, including first-image reads,
   preparation, group finalization and requested exports. Prefer source-owned
   execution timestamps to a client-polling endpoint where available.
5. Check readiness RSS and available memory before larger concurrency. The host
   initially had about 7.8 GiB available RAM and already used 20 GiB of swap;
   concurrency four is not automatically a clean throughput observation.
6. Run repeated observations across the supported corpus only after those
   ownership/boundary checks, retaining source, input, environment and raw result
   provenance. Historical 30-workflow and dated value-extension evidence remain
   separate.

## Native runner

`benchmark/native_cellprofiler_batch_worker.py` is deliberately executed as a
standalone script with the native Python 3.9 interpreter. Importing the benchmark
package bootstraps OpenHCS, which requires a newer Python; the runner does not
add import-path aliases or weaken that boundary. Its JSON request and result are
derived from its dataclass declarations.

The retained candidate driver takes a task-owned output directory argument and
is a reproduction/experimental harness, not a new production API. See README.md
for the command and the observed blockers.
