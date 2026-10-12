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

## Owner decision taken (2026-10-12): both, split by the kind of cost

"A for what is one-time per machine, B for what is bound by memory."

A function's preparation has two declared parts with different lifetimes:

| Part | Declared with | Runs | Called with |
| --- | --- | --- | --- |
| Acquire: put a resource on this machine (kernel cache, weights) | `prepare=` of the memory decorator, or `@processing_prepare(fn)` | catalogue preparation, before the server reports ready | once per value of each hook parameter's declared type |
| Load: put a resource into a process or onto a device (model, warm-up) | `load=` of the memory decorator, or `@processing_load(fn)` | "prepare this pipeline", in each worker that will run the pipeline | the values the compiled step selects, inside the device scope the compiler assigned |

As the author writes it (what `cellpose_segment.py` on the #1230 branch should become; that
branch is not edited here):

```python
class CellposeModel(Enum):
    NUCLEI = "nuclei"; CYTO3 = "cyto3"; CYTO2 = "cyto2"

def _download_weights(model: CellposeModel) -> None:       # acquire: every member
    cellpose.models.cache_model_path(model.value)          # (narrow it with Literal[...])

def _load_model(model: CellposeModel) -> None:             # load: the selected member,
    _model(model).eval(np.zeros((1, 64, 64), np.float32))  # on the assigned device

@numpy(prepare=_download_weights, load=_load_model)
def cellpose_segment(image, model: CellposeModel = CellposeModel.NUCLEI, diameter: float = 30.0):
    return _model(model).eval(image, diameter=diameter)[0]
```

The hook names parameters of its function; each must be annotated with an `Enum` (every
member) or a `Literal` (those values). A hook without parameters is the single empty
combination, which is every existing Numba kernel hook: the catalogued functions use the
same declaration and the same operation (`AcquireHookPreparation`), not a parallel one.

**Unprepared pipelines: prepared implicitly, as their own phase, never refused.** The GUI
(`Session.run_datasets`) and every existing client submit compile then execute; refusing
would break them and would add a job round trip to every run of a pipeline that loads
nothing. An execution first runs the load phase for its leased workers
(`WorkerExecutorResources.load_pipeline_resources`), which finishes before any lane starts
and sends nothing to a worker that already holds the loads; it logs its count and seconds.
`run_compiled_pipeline` (the benchmark's path) sends the explicit request, so the
`SERVER_COMPILATION_JOB` and `SERVER_PIPELINE_JOB` it reports contain no load.

### Done in this pass (item 1 of the hand-off)

- `openhcs/core/processing_preparation.py`: `declared_hook_arguments`,
  `selected_hook_arguments`, `AcquireHookPreparation`, `LoadHookPreparation` (identity
  includes arguments and device), `CallablePreparation.acquisitions / prepare_for_call /
  prepare_selected / selected_load`, `UnpreparedValueError`.
- Compile (`normalize_prepared_function_pattern` -> `CallableProjection.prepared_callable(kwargs)`):
  a serving process refuses a selection it did not acquire, naming the acquired values; a
  process that does not serve (a script, a direct orchestrator) acquires only the selected value.
- `openhcs/core/orchestrator/worker_execution.py`: `PipelineResourceLoads` (derived from the
  compiled bundle), worker command `LoadPipelineResources`, `load_pipeline_resources` on the
  resources family, `WorkerProcess.loaded`; released workers go back to the front of the
  prepared set so the same pipeline is given the same processes.
- "Prepare this pipeline" is its own queued job: `ZMQAuxiliaryExecutionParams.prepare_workers_only`
  on a request that names the compile artifact (`ZMQExecutionRequestBuilder.with_worker_preparation`),
  served by `ZMQExecutionServer._prepare_pipeline_workers`; `run_compiled_pipeline` sends it
  (`ZMQPipelineRunPhase.SUBMIT_PREPARATION / WAIT_PREPARATION`, `ZMQCompiledPipelineRun.preparation_record`).
- Tests: three new tests in `tests/integration/test_no_jit_after_readiness.py` over the
  real server with a probe function (acquire declared for `small`, `large`; the function
  also accepts `undeclared`), fork workers, 2 workers. See "Measurements of this pass".

### Measurements of this pass (probe function, fork workers, 2 workers, 4 wells, CPU, loaded machine)

`tests/integration/test_no_jit_after_readiness.py`, custom-function tests: 6 passed.
Counts are exact; times are one run.

| | first run | second run |
| --- | --- | --- |
| acquisitions (server, before readiness) | 2 (`small`, `large`), none later | 0 |
| "prepare this pipeline" job, client wall | 0.03 s, 2 loads (one per worker) | 0.04 s, 0 loads |
| loads inside compile or execute | 0 | 0 |
| execute, client wall | 0.08 s | 0.07 s |
| worker processes that execute | the 2 that were prepared | the same 2 |

A compile selecting `undeclared` is refused: "'probe' was not prepared for
model='undeclared'. Prepared before this server reported ready: model='small';
model='large'." Seen failing first: with the load hook looked up on the compiler's
reference instead of the declared function, the prepare job loaded nothing and both loads
landed in the first execute; the guard reported exactly that.

Not run in this pass: `guardrails_local.sh` (origin/main not merged), the two Numba tests
of the same file, the full suite. Unit files run and passing: `test_processing_preparation`,
`test_preparation_admission`, `test_callable_contract`, `test_custom_function_lifecycle`,
`test_fork_compiler_preparation`, `test_zmq_execution_server`, `test_zmq_compiled_pipeline_run`,
`test_openhcs_adapter`, `test_openhcs_measured_run`, `test_g7_runtime_protocol_guards`,
`test_orchestrator_lane_planning` and the other unit files that import `worker_execution`
or `zmq_execution_signature` (before the last two fixes: 282 passed, 2 failed, both fixed
and rerun).

### What remains (exact, in order)

0. Merge `origin/main`, run `guardrails_local.sh` (not run; `declared_hook_arguments` has one
   `isinstance(annotation, type) and issubclass(annotation, enum.Enum)` and one
   `get_origin(...) is Literal`, which a ratchet may count), then the full gates.

1. **Spawn workers (hand-off item 2), not started.** `ProcessWorkerExecutorResources.load_pipeline_resources`
   returns 0: the spawn pool's processes are created per execution by
   `WorkerExecutorFactory.create` (a `ProcessPoolExecutor` per call), so nothing can persist
   from "prepare" to "execute". Needed: a prepared runner on the spawn context
   (`PreparedForkWorkerLaneRunner` does not need fork except `inherited_parent_connections`
   in `_serve_worker` and the `PrepareWorker` first command, which for a spawned process must
   run `_configure_worker_process` and load the custom sources), started at "prepare this
   pipeline" with the pipeline's worker count, kept by the server. A spawned worker resolves
   a custom function through `openhcs.processing.custom_functions.__getattr__`
   (`FunctionReferenceTransportAuthority.importable_function`), so that hook cannot be
   deleted until the spawned worker loads the sources at start. No limit on accelerator
   workers exists in `openhcs/core/config.py` (only `num_workers`); one must be declared
   there. Memory: each worker of a pipeline holds one copy of each selected model
   (2 workers x 1 model here; 12 x 0.9 GB does not fit 8 GB).
2. **The implicit load phase is logged, not a field of the execution record**, so
   `end_time - start_time` of an execution that was not prepared includes it. It should be
   an extra of the record (`BundleExecutionExtras`) and subtracted by `benchmark/timing.py`.
3. **`total_seconds` of `benchmark/well_throughput_scaling.py` (2165-2201)** is a client
   clock around `run_compiled_pipeline`, so it now contains the prepare job (and it already
   contained server start on the owned-server path). The benchmark must send the prepare
   request before starting that clock; `compile_seconds` and `execute_seconds` are already clean.
4. **Numba kernels in a spawned worker**: the kernel hooks are acquire-only; a spawned
   worker loads a cached kernel at first call. Declaring the kernel hooks as loads too is
   one line per hook, after item 1.
5. **Names**: `processing_prepare` / `prepare=` / `__openhcs_prepare__` now mean "acquire";
   rename to `processing_acquire` / `acquire=` (35 files mention them).
6. Hand-off items 3 (registering tells running servers; GUI "preparing" state; edit and
   delete over the wire, which have no request today), 4 (retry of a failed acquisition),
   5 (the 7 s catalogue-preparation request: `_clear_caches` drops
   `RegistryService._metadata_cache`, the reload makes a new dict, and
   `FunctionCatalogService._search_projections` compares by dict identity, so every
   function is projected again) are not started.
7. GPU run, after 1: build the venv of DL-COMMON (`torch 2.6.0+cu124`, `cupy-cuda12x`,
   `cellpose==3.1.1.3`), store the example above with `@torch`, then
   `python tests/integration/helpers/prepared_resource/run_custom_function_pipelines.py <dir>`
   with `OPENHCS_PREPARED_RESOURCE_TRACE=<dir>/trace.jsonl` and without `OPENHCS_CPU_ONLY`,
   and count `load` events per worker pid and `nvidia-smi --query-compute-apps=pid,used_memory --format=csv`.

## Third leg

### 1. Registering a custom function tells the running servers (done)

Relation: registering is making the function usable, and usable includes acquired on every
server that will run it. One owner states it: the manager's three operations
(`register_from_code` with `persist`, `update_custom_function`, `delete_custom_function`)
each tell `connected_servers` (`openhcs/processing/custom_functions/connected_servers.py`).
The GUI dialog, `pyqt_gui/main.py` and any script call the manager and add nothing.

- **Which servers.** Every `ZMQExecutionClient` adds itself to `connected_servers` when it is
  constructed (weakly held); "connected" is asked of the client when a change is told, and
  two clients of one server process count once. A process with no connected client (a
  server, a worker, a script) tells nobody.
- **The change family** (`catalogue_changes.py`): `CustomFunctionChange` with members
  `CustomFunctionCreated(name, code)`, `CustomFunctionEdited(old_name, name, code)`,
  `CustomFunctionDeleted(name)`. The member is the wire payload (control message type
  `openhcs_custom_function_change`; one route, the family member says what happened) and
  carries its effect in a server, `apply_on_server`: make the server's store hold what the
  session's holds (`CustomFunctionManager.hold_source` / `drop_source`; a server that shares
  the session's store finds the bytes already there and writes nothing; a write passes the
  server's path policy), then `load_all_custom_functions`. Loading in a serving process
  acquires (first leg), so: created is prepared, edited is prepared again and its old
  revision withdrawn, deleted is withdrawn.
- **In the server** (`FunctionCatalogPreparation.follow_custom_function_change`): the change
  runs on the catalogue-preparation owner's own future, after any preparation under way, so
  the server's existing status reports pending until the change is loaded and acquired and
  the projections are current. `openhcs_custom_function_state` answers
  `ServerCatalogueState(pending, loaded, failed)`.
- **What the session shows.** `connected_servers.tell` returns at once; a thread sends the
  change and asks for the state until it is not pending. Meanwhile
  `list_custom_functions` lists the function as `CustomFunctionPreparing`
  ("name (preparing)"). A source the server could not load or acquire is listed through the
  existing `CustomFunctionLoadFailure` ("name (failed to load)", "On the execution server:
  ..., line N"). When the server settles, `custom_function_changed` is emitted, which is
  what refreshes the dialog.
- **A compile naming a deleted function** is refused by the lookup owner:
  "Custom function 'followed' was deleted, so this server withdrew it. Register it again,
  or remove the step that names it." (`WithdrawnCustomFunctionError`; before: "Unknown
  canonical function ID 'openhcs:followed'").
- **A server started later** loads the persisted sources at its own start (first leg;
  guarded by the "stored before start" function of `test_no_jit_after_readiness.py`).
- Not notified: a registration with `persist=False` (MCP's ephemeral path, which already
  registers in the server through `openhcs_custom_function_register`).
- `load_all_custom_functions` now always announces a changed source set (before: only when
  something loaded or failed, so deleting the last function left forked workers stale).

Tests. `tests/integration/test_custom_function_changes_reach_servers.py` (six tests, one
real server, fork workers; the driver `helpers/prepared_resource/run_custom_function_changes.py`
only calls the manager): created while ready is acquired by the server and no compile or
execute contains an acquisition; listed as preparing until the server holds it; an edit is
acquired again, the server publishes only the new revision and calls run the new code; an
acquisition that fails on the server is listed as failed to load with the cause; a deleted
function is withdrawn and the compile naming it is refused with the message above.
`tests/unit/test_custom_function_lifecycle.py` (four tests, scripted server): one request
per change and per server process, none to a client that is not connected; preparing until
the server reports; failed to load from the server's report; each member's effect on a
server's store.

Measured (same loaded machine): the server ran the acquisition 0.14 s after `create`; it
reported pending for 6.9 s after that (the catalogue re-projection, item 7 below).

## Gates

See the PR description.
