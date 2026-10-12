# DL4: a custom function's preparation runs before the server reports it usable

Branch `refactor/DL4-custom-function-preparation`. Gap 5 of the Cellpose/N2V2 receipt
(`D1-cellpose-n2v2-custom-functions.md`, PR #1230). Follows R1d (#1225) and R1e (#1231).

## Owner requirement

Every one-time cost is paid during function-catalog preparation, before the server reports
ready. Nothing compiles, downloads, loads or warms up at first use, and benchmarks time
compile and execute, so neither may contain a one-time cost.

## What is wrong (measured on main `5235c1a95`, Linux, CPU only, 12 threads)

Probes are scratch (`.claude/prof/`, not committed). A probe custom function records, per
process, when its source is executed, when its declared preparation runs and when it loads
its in-memory resource. The Cellpose runs use the NumPy-declared variant of
`cellpose_segment.py` (commit `47fbed348` of the #1230 branch; the torch-declared one cannot
compile without CUDA, gap 2, owned by DL1), Cellpose 3.1.1.3, torch 2.14.1+cpu, 4 real
BBBC039 test fields, 2 workers, an empty weight cache, and count `CellposeModel`
constructions in every process.

1. **A custom function is never in the set that serving preparation prepares.**
   `RegistryService.prepare_in_current_process` enumerates the catalogue and prepares it;
   the server loads the persisted custom sources afterwards
   (`FunctionCatalogService.prepare_projections` -> `synchronize_custom_function_sources`).
   Loading a source prepared nothing. The preparation then ran in the first compile that
   named the function (`normalize_prepared_function_pattern`), after readiness.
2. **A source stored while the server is ready** (the editor writes the file in the GUI
   process) reaches the server when a pipeline's code imports it: loaded and prepared inside
   that compile.
3. **Fork workers do not hold what the server prepared late.** The 12 prepared workers are
   forked before readiness. The preparation ran later, in the server, so no worker inherited
   the loaded resource; each loads it at its first call. A run leases the first idle workers
   and returns them to the end of the list, so successive runs reach workers that have not
   loaded yet: this is the "reload on each run" (2 new loads per run with 2 workers, until
   all 12 have loaded).
4. **Spawn workers are new processes in every execution.** `WorkerExecutorFactory.create`
   (`worker_execution.py`) builds a `ProcessPoolExecutor` per execution for the spawn start
   method, which is the configured default and is forced for GPU steps
   (`worker_start_policy.py`). Every run starts interpreters, imports, executes the custom
   source again and loads the resource at first call. Not fixed here; see "Not done".

## Design

**One rule, one mechanism.** A process that has prepared its catalogue for serving
(`CallablePreparation.prepare_for_serving`, the mechanism catalogued functions use) keeps
"prepared before usable" for everything published afterwards: loading a custom source in
such a process runs the source's declared preparation through the same call, before the
function is published. Authoring processes (the GUI, a client) load without preparing, as
R1e established.

- *Startup.* The server prepares the catalogue, then loads the persisted custom sources;
  each is prepared as it loads, before readiness and before the workers are forked.
- *Stored while the server is ready.* Preparation runs in the server when the server loads
  the source, as part of loading: through the registration request
  (`FunctionCatalogService.register_custom_function`), or, for a file another process
  wrote, through the catalogue-preparation request
  (`FunctionCatalogPreparationStartRequest`), during which the server reports the catalogue
  pending and reports ready only when the preparation has finished.
- *Failure.* A preparation that raises is a load failure of that source alone, listed as a
  `CustomFunctionLoadFailure` with file, line and error; a registration request fails and
  publishes nothing. No second channel.
- *Who holds a prepared resource.* The server loads it once; fork workers inherit it. When
  the server prepares something after its workers were forked, it forks the idle workers
  again and replaces leased ones when they return
  (`PreparedForkWorkerLaneRunner.replace_with_current_forks`), so no worker loads anything
  inside an execution.

## Done

- `CallablePreparation.prepare_published` (`openhcs/core/processing_preparation.py`): in a
  serving process, prepare a callable published after serving preparation; elsewhere do
  nothing. The serving fact is set by `prepare_for_serving` and inherited by forks.
- `CustomFunctionManager._prepare_source` calls it after projecting the declaration. The
  outcome is shared per source revision by the existing `prepare_source_once`, so a source
  is prepared once and a failure is that revision's outcome.
- `PreparedForkWorkerLaneRunner.replace_with_current_forks`; the execution server
  subscribes it to `custom_function_changed`.

## Measurements (same machine, other agents' jobs running: wall times are noisy, counts exact)

Cellpose `nuclei`, 4 fields, 2 workers, cold weight cache (26.6 MB download):

| | main, fork | branch, fork | main, spawn | branch, spawn |
| --- | --- | --- | --- | --- |
| Weight download + model load | first compile, 4.86 s | preparation, 6.35 s | first compile, 3.23 s | preparation, 5.63 s |
| Warm-up call | first compile, 0.40 s | preparation, 1.73 s | first compile, 0.20 s | preparation, 5.43 s |
| First compile / second compile | 5.46 s / 0.09 s | 0.21 s / 0.09 s | 3.58 s / 0.07 s | 0.14 s / 0.11 s |
| Model loads in the server | 1, after readiness | 1, before readiness | 1, after readiness | 1, before readiness |
| Model loads per worker, run 1 / run 2 | 1 / 1 (new workers each run) | 0 / 0 | 1 / 1 (new processes) | 1 / 1 (new processes) |
| Execute, run 1 / run 2 | 8.57 s / 8.78 s | 9.25 s / 9.38 s | 18.29 s / 16.13 s | 23.61 s / 23.92 s |

The 13.3 s of the D1 receipt (weights, load and warm-up in the first compile) is the first
two rows: on main it is inside the first compile after readiness; on this branch it is
inside preparation before readiness, and the first compile equals the second within noise.
A worker's own load from the cached weights is 0.11 to 0.28 s; with fork workers it is gone.
Execute times are 4 Cellpose calls of about 4 s each and do not show a 0.2 s difference.

Probe function, fork workers, source stored while the server is ready, then the
catalogue-preparation request: prepared and loaded once in the server at 0.46 s after the
file was written; the server reported pending 30 times and then ready; the two following
compiles and executes contain no preparation and no load; no worker loaded.

## Guards and tests

- `tests/integration/test_no_jit_after_readiness.py`, three tests over one real server
  with fork workers (`helpers/prepared_resource/`), counts only: each function is prepared
  exactly once, by the server, before the readiness report that covers it (the one stored
  while ready: after it was stored and before the server reports ready again); no
  preparation and no load inside any compile or execute window; exactly one load per
  resource, in the server, and every call in every worker sees exactly one load.
- `tests/unit/test_custom_function_lifecycle.py`: a serving process prepares at
  registration and a following compile prepares nothing; an authoring process does not
  prepare; a failing preparation is a `CustomFunctionLoadFailure` of that source (file,
  line, error), the other source loads, and a registration that fails publishes nothing.
  The first and third were seen failing with the call removed.

What they cannot see: spawn workers; a GPU; a source loaded by a compile's import (below).

## Not done, and what each needs

1. **Spawn workers (default start method, and every GPU step) still start per execution
   and load per run.** The fix is a second prepared runner on the spawn context: the
   bundle is already shipped by pickle (`ExecuteShippedLane`), so the runner and
   `PreparedForkWorkerExecutorResources` do not need fork; a spawned worker inherits
   nothing, so its first command (`PrepareWorker`) must prepare the process when
   `CallablePreparation._serves_prepared_callables` is false. Open questions that need
   measuring before choosing: how many spawn workers to start and when (the worker count
   comes with a submission, not at server start), and their memory (a spawned worker with
   the whole catalogue imported is not shared copy-on-write). This is the remaining half of
   requirement 3 and is the path a GPU machine takes.
2. **Preparation that depends on a parameter** (which model). Not implemented. Proposal
   and the owner decision are below.
3. **The GUI editor does not tell a running server.** `pyqt_gui/main.py:1604` and
   `custom_function_manager_dialog.py:193` register in the GUI process only. Until the GUI
   sends the catalogue-preparation request after a registration, a source the server has
   not been told about is loaded, and therefore prepared, by the first compile that
   imports it (`openhcs.processing.custom_functions.__getattr__`). The relation holds for
   the registration request and the preparation request; this path still breaks it.
4. **A failed preparation is final for that source revision in that server** (the existing
   rule of `prepare_source_once`): a download that failed because the network was down is
   not retried until the source changes or the server restarts.
5. **GPU.** Not run (no GPU venv built). By reading: a preparation that initialises CUDA in
   the server before the workers fork would break fork workers, but GPU steps resolve to
   spawn workers, which inherit nothing; so on a GPU machine this branch moves the download
   and the server's own load before readiness, the server holds a model it does not use
   (as on main), and each spawn worker still loads per run (item 1).
6. The catalogue-preparation request takes about 7 s in the server for one new source
   (it rebuilds every catalogue projection); the preparation itself ran in the first 0.5 s.
   While the server forks its workers again one status request went unanswered for 1 s.

## Owner decision: what to prepare when preparation depends on a parameter

The hook takes no arguments, so `cellpose_segment` hard-codes `NUCLEI` and the device in
`_warm_up`: a pipeline that selects `CYTO3` downloads and loads at first use.

The benchmark (`benchmark/well_throughput_scaling.py:2165-2201`) reports the server's
compile job, the server's pipeline job, and `total_seconds`, a client wall clock around the
whole submission. Anything done per pipeline after submission is inside `total_seconds`.

- **Option A, proposed: the hook declares what it can prepare, all before readiness.** The
  hook names parameters of its function; the platform calls it once per value of each
  parameter's declared type (`def _warm_up(model: CellposeModel)` is called for `NUCLEI`,
  `CYTO3`, `CYTO2`). The author limits it by annotating the hook narrower than the
  function (`model: Literal[CellposeModel.NUCLEI]`). A compile whose step selects a value
  outside the prepared set is refused with the prepared values named. Nothing is added to
  compile or execute. Cost: every declared model is downloaded and loaded at every server
  start (three 26.6 MB Cellpose 3 models here; Cellpose-SAM's are 1.2 GB each), held in
  the server and, on a GPU, in each worker.
- **Option B: a per-pipeline preparation phase.** The server prepares exactly what the
  compiled pipeline selects (`CYTO3` on the device the compiler assigned), in the workers
  that will run it, as a phase it reports. To stay out of the timed numbers it must be a
  separate request the benchmark sends before starting its clock; done inside the
  submission it lands in `total_seconds` of the first run, which is what the owner ruled
  out ("it'll make them mad noisy").

Concrete example: a server with `cellpose_segment` (3 models) and a GPU with 8 GB. Under A
the server start downloads 80 MB and loads three models; 12 workers each holding one
0.9 GB model do not fit the card, so A needs a limit on GPU workers as well. Under B a
pipeline that uses `CYTO3` with 2 workers loads one model in 2 workers, and the first
`run-well-throughput` row needs a "prepare" request before its clock. A is what the
standing rule asks for and fits CPU; B is what a GPU needs. The choice also decides item 1
(how many spawn workers exist before a pipeline is known).

## Gates

See the PR description.
