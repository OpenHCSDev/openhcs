# Benchmark integration: ordinary pipeline, measured execution

## Scope decision

The infrastructure is the current priority. Do not run a new comparative
benchmark, change SLAS performance claims, or plot a speedup until this boundary
is implemented and validated. A benchmark is an ordinary OpenHCS pipeline run
with declared input selection, repetition, measurement, comparison, and retained
evidence. It is not a second pipeline model or execution engine.

The generic benchmark infrastructure must accept an ordinary OpenHCS pipeline
document without requiring CellProfiler. `.cppipe` conversion is one optional
scenario preparation path, and native CellProfiler comparison is one optional
comparison path. Neither belongs in the generic measured-run lifecycle.

Source baseline: `openhcsdev/main` at `0ba01b29c` (2026-09-22). The working tree
already contains unrelated untracked pilot outputs and `uv.lock`; preserve them.

## Ownership contract

| Fact or behavior | Owner | Benchmark-specific addition |
| --- | --- | --- |
| Steps, configuration, source bindings | `PipelineDocument` and normal OpenHCS config declarations | Select an existing document and input scope; do not copy step/config semantics into a benchmark case. |
| Compilation, execution, status, cancellation, worker scheduling | Ordinary runtime beneath the GUI and agent execution services | Request the same operation with an observation policy. If an operation is missing, add it once to the operational owner, not to an agent-only facade. |
| CellProfiler translation | Public CellProfiler importer and source-workspace preparation | Select a source `.cppipe` and retain its identity; do not implement another translator. |
| Inputs, repeat/group membership | Benchmark manifest/case declaration | State the scientific sampling design and exact source identities. |
| Timing and resources | Source-owned runtime observations plus benchmark metric declarations | Declare measurement intervals, repetition and aggregation; never reconstruct execution state from logs or poll timing. |
| Native reference and equivalence | Native adapter plus typed OpenHCS equivalence policies | Select reference artifacts and comparison tolerances, then retain per-artifact outcomes. |
| Run lifecycle and provenance | One typed benchmark receipt derived from the request and ordinary execution observations | Record benchmark-only design, environment, versions and evidence paths; do not maintain another status authority. |
| CLI and MCP | Existing benchmark command declarations and agent capability registry | Project the same benchmark request/receipt; MCP must not acquire a parallel run implementation. |

The intended dependency direction is:

```text
benchmark scenario (inputs, repeats, observations, comparisons)
    -> ordinary PipelineDocument + GlobalPipelineConfig
    -> ordinary runtime compile / execute / status
    -> runtime observation + materialized outputs
    -> benchmark measurements / comparisons / immutable receipt
```

The benchmark scenario does not own steps, function parameters, compiled plans,
worker scheduling, or output routing. A scenario may refer to a source `.cppipe`
only through the existing importer, which produces the ordinary document before
the generic measured-run boundary.

The ordinary `OpenHCSExecutionSubmission` is already the typed single-pipeline
run declaration; do not invent a parallel measured-pipeline request just to
rename it. An external CLI/MCP selector may resolve source and plate paths to
that submission, then add only benchmark-specific observation, repetition and
comparison policy. Its receipt should derive execution identity, outputs,
phase timings and provenance from the submission and completed runtime result;
it must not copy runtime job state into a second benchmark status enum. The existing
`ComparisonSuiteRunDeclaration`/`Receipt` remains a specialised multi-case
comparison-suite aggregate: native-reference paths and speedup targets do not
belong in the generic single-pipeline contract. Likewise, legacy log parsing
in `benchmark/progress.py` is diagnostic history, not the new status authority.

## Current duplication to retire

- The CellProfiler adapter historically owned compile-submit-wait-execute and
  rebuilt one `PipelineDocument` for both submissions. The ordinary runtime now
  owns that sequence and compile-artifact reuse; the remaining adapter helper
  prepares a document and calls the generic measured-run wrapper.
- `benchmark/contracts/pipeline.py` and `benchmark/pipelines/registry.py` name a
  `PipelineSpec`, but source tracing shows it currently selects a benchmark
  scenario (not executable steps). Keep that selection role; separate its
  input/reference/measurement choices from the actual `PipelineDocument` and
  remove any suggestion that it is a second executable pipeline authority.
- `ToolAdapter.run` and several callers pass open-ended `pipeline_params`
  mappings. Move benchmark-only choices to a typed scenario/request; pass
  OpenHCS pipeline state only as a `PipelineDocument`.
- The current CLI is CellProfiler-comparison-oriented and the expert MCP
  extension only inspects completed runs. Keep CP commands as a specialization,
  but expose generic measured ordinary-pipeline operation through one typed
  scenario and receipt shared by CLI and MCP. Do not build a separate MCP
  runner or a second benchmark-only execution server.
- Existing `openhcs_inspect_benchmark_run` is useful read-only evidence
  projection. It is expert-only and hidden by the default desktop MCP profile.
  Keep that profile policy; the integration should not make benchmark execution
  a default desktop action.
- `benchmark/well_throughput_scaling.py::run_case_well_throughput` remains a
  legacy direct-`PipelineOrchestrator` execution route, reached by
  `scripts/benchmark_cppipe_well_throughput.py`. It owns compile/execute timing,
  progress queues, and worker cleanup outside the ordinary measured-run path.
  Its presentation/reporting code can remain benchmark-specific, but execution
  must be migrated to the ordinary submission and observation owners before the
  *whole* benchmark surface can be called nonduplicating. Preserve historical
  CSV readers and figure inputs; do not reinterpret old timing rows as receipts
  from the new boundary. `benchmark/throughput_scaling.py` already calls the
  OpenHCS adapter and is a different, process-per-job workload.
  The migration cannot simply request the current full runtime-observation
  export: the legacy run explicitly uses `RuntimeObservationMode.OMIT` and
  disables artifact materialization, whereas an export currently strengthens
  retention to `MERGE_INTO_PARENT`. That would move potentially large runtime
  values into the server process and change the resource/timing experiment.
  First add an ordinary typed outcome-only observation that retains per-axis
  success, progress/timing boundaries and environment without transferring
  runtime arrays. Then make the legacy runner a scenario over the ordinary
  submission/result, with a route/version marker so old CSV rows are not
  silently pooled with new measurements.

## Infrastructure continuation (2026-09-22)

- Ordinary ZMQ execution now accepts a typed `outcomes` observation scope.
  It exports per-axis status and failure diagnostics, output roots, and the
  server-owned environment snapshot, but does not require worker runtime values
  to be returned to the parent when the compiled plan itself does not need them.
  The prior `values` export remains the default and retains its schema.
- The shared measured-run finalizer accepts either scope and records it in the
  same receipt. A declared expected axis count is checked before any success
  receipt or finalizer artifact is written. Outcome-only receipts do not claim
  value or output-equivalence validation. The CLI wrapper also records the
  compilation and execution server-job start/end intervals from ordinary
  status; throughput uses those boundaries rather than progress-event windows.
  The legacy throughput CLI requires a client-owned server for a measured run;
  it refuses an already-running endpoint rather than silently changing its
  memory/timing boundary. `--execution-port` selects an unused port explicitly.
- `run_case_well_throughput` now prepares its CellProfiler-derived ordinary
  `PipelineDocument` and submits it through the shared ZMQ measured-run wrapper.
  The original dataset is the source identity; the replicated workspace is the
  execution plate identity. The runner's unused open-ended `pipeline_params`
  forwarding was removed; selection remains on the imported case declaration.
  Its progress CSVs remain benchmark-specific projections of ordinary progress
  events. It no longer owns an orchestrator, compile call, progress queue, or
  worker execution call. New rows carry `ordinary-zmq-outcomes-v1`; older CSVs
  decode as `legacy-direct-v1`. Resume refuses an old-route CSV before running
  and requests a new output root; figure generation also refuses mixed routes.
- Focused unit tests cover export-scope transport and retention policy, typed
  outcome serialization, server dispatch, shared receipt finalization, and the
  legacy runner's ordinary submission. Live synthetic ZMQ executions prove both
  the outcome-only export/finalizer and the migrated throughput wrapper's real
  compile/execute path, including source-versus-execution plate identity and
  client-owned-server admission. This is infrastructure evidence, not a new
  CellProfiler/OpenHCS performance comparison.
- The ordinary headless execution submission now exposes the same typed
  observation scope through its service and declaration-derived MCP request.
  The generic `run-measured` CLI selects it from the runtime enum rather than
  maintaining a benchmark-local choice list. Outcome-only CLI measurements
  use the same ordinary source session and finalizer as full-value runs;
  requesting outcome-only without an export path fails before submission.

## Migration sequence

1. Characterize ordinary pipeline execution and observation contracts across
   GUI, agent, and benchmark clients. The agent session service currently
   accepts authored source plus config IDs, while the benchmark needs a derived
   `GlobalPipelineConfig`; it cannot be reused as a benchmark execution API
   without introducing an agent-specific dependency. Test source identity,
   compile artifact, execution completion, cancellation, and output retention.
   Identify the real source-owned timing boundaries before exposing a
   benchmark API.
2. Add the minimum generic observation hook to the ordinary execution owner.
   Benchmark metric declarations select observations but do not implement
   transport, scheduling, or status. Do not add a benchmark-specific ZMQ client.
3. Reuse `OpenHCSExecutionSubmission` as the generic run declaration. Add only
   benchmark-specific measurement/repetition, optional comparison, and
   retention policy at the scenario boundary. Parse old manifest parameter
   maps once; do not propagate raw keys through adapters. The OpenHCS adapter
   should remain a thin scenario-to-document preparation and result-comparison
   wrapper. Keep CellProfiler import and native comparison as declared
   specialisations.
4. Derive CLI and expert MCP projections from the same typed scenario and
   receipt. The MCP path should invoke or hand off to the ordinary pipeline
   operations; it should not reimplement run, cancel, or polling semantics.
5. Remove obsolete parameter maps, duplicate receipt/status projections and
   dead compatibility code after whole-repository consumer checks. Preserve
   historical file formats and read old receipts with explicit warnings.

## Evidence gates

- Full-context NRA scan: 79 detectors analyzed, zero omitted, seven reported
  findings. This is architectural evidence, not proof that the unreported
  execution duplication is absent. The certified mirrors in
  `cellprofiler_reference_exports.py` and `throughput_scaling.py` should be
  considered in the larger ownership migration, not patched in isolation.
- First operational identity cleanup: `OpenHCSExecutionSubmission` can derive
  its execution request from the same compile request and completed artifact
  ID. The benchmark adapter now uses that method instead of rebuilding a
  `PipelineDocument`; transport and adapter tests verify both submissions
  share the exact document object. This does not yet eliminate the benchmark's
  private submit/wait lifecycle.
- The underlying `zmqruntime` client already owns cancellation. OpenHCS now
  exposes a bounded cancellation request through its ordinary headless
  execution service and declaration-derived MCP capability; the benchmark
  layer must reuse this job control instead of introducing its own cancel
  state. A fake-client service test verifies exact job routing, timeout
  propagation, terminal status, and no duplicate request after cancellation.
  A live-server cancellation test remains required.
- The compile-then-execute ordering, accepted-response checks, compile-artifact
  reuse, and terminal-result checks now live in ordinary
  `openhcs.runtime.zmq_execution_client.run_compiled_pipeline`. Its phase
  context is generic; the benchmark adapter projects those phases onto
  benchmark timing records and retains benchmark-only observation/equivalence
  handling. Direct runtime tests cover successful order and fail-closed compile
  and execution results. The benchmark adapter still owns endpoint provenance
  and observation-file handling; the generic measured-run declaration is not
  implemented yet.
- The converted-CellProfiler OpenHCS adapter now decodes its legacy parameter
  map once into typed benchmark-policy fields. It retains the existing
  `CPPipeSourceRequest` as the source of dataset ID and output directory instead
  of copying those facts into a second dataclass. This is a compatibility
  bridge, not the final generic benchmark scenario: the manifest and native
  adapter still pass open-ended parameter maps.
- Auxiliary execution options are now one typed declaration shared by the
  normal ZMQ client and server. The benchmark requests observation export
  through `OpenHCSExecutionSubmission.with_auxiliary_params` instead of
  spelling a transport key. NRA preflight identified the result-summary
  filename as the complete dependency closure for extracting the generic
  measured-run declarations; the clean extraction moved timing, endpoint
  provenance, ordinary compile/run invocation, and observation loading into
  `benchmark/openhcs_measured_run.py`. The CellProfiler adapter only prepares
  the document and selects benchmark policy. The wrapper reuses
  ordinary ZMQ client's application-version admission and context manager for
  one disconnect. A direct test of the new wrapper uses a
  normal `PipelineDocument` with no `.cppipe` or native reference.
- The normal headless `openhcs_submit_pipeline_execution` request now accepts
  an optional runtime observation export path. The existing execution session
  service checks its writable-root policy and rejects an existing target,
  then composes the typed auxiliary option into its ordinary submission.
  Existing status and cancellation job control remain unchanged. This is a
  bridge toward measurement through MCP, not a generic benchmark receipt or
  report generator yet. A fresh-server integration test executes an ordinary
  synthetic-plate pipeline through that service and reads the valid exported
  observation. This proves the option reaches the runtime; it does not establish
  benchmark timing, repeated-run, or installed-client behavior.
- The post-change uncached NRA scan completed in `exact_compact_global` mode
  with 79 detectors analyzed, zero omitted, and seven findings. The quick
  cached scan was partial (43 analyzed, 36 omitted) and is not used as global
  evidence.
- A fresh interpreter in the current editable environment discovers the
  benchmark inspector in the full local capability profile but not desktop;
  the new ordinary cancellation capability appears in both. This verifies
  declaration/profile projection, not a fresh installed wheel or a live
  server cancellation.
- Ordinary source-backed execution sessions now accept an explicit prepared
  plate while retaining the original plate identity and one Python pipeline
  authority. The execution service retains the exact submitted request,
  accepting endpoint handshake, and typed server completion record after job
  termination. The expert benchmark finalizer consumes that completed ordinary
  job and the shared measured-run evidence writer; it does not submit a second
  job or mirror status. The normal ZMQ client now enforces application-version
  admission before either compile or execute submission. A live synthetic-plate
  MCP call proves finalization and receipt retention. The finalizer labels its
  server start/end interval ``SERVER_PIPELINE_JOB`` because an execution request
  may include inline compilation; it retains the compile artifact identifier
  when one was supplied. This is infrastructure evidence, not a comparative
  throughput claim.
- The registered ``openhcs-benchmark run-measured`` command now adapts a Python
  source file and plate paths into that same ordinary source-backed session,
  waits through its existing job control, then invokes the same finalization
  service as MCP. The runtime observation filename is declared once by the
  measured-run artifact enum and reused by the CLI and CellProfiler adapter.
  A live synthetic-plate test verifies the CLI receipt and source evidence.
- A separate live-server test submits an ordinary source-backed job, cancels it
  through the existing session service, observes the terminal cancelled state,
  and proves that a cancelled job cannot be finalized as successful evidence.
  The installed MCP smoke explicitly grants its fixture directory through the
  declared agent path-policy keys because macOS parent and child interpreters
  may resolve different temporary roots.
- A fresh MCP stdio process now has an opt-in installed-client smoke that
  generates a tiny synthetic plate, creates a normal source-backed session,
  submits and waits for its pipeline job, finalizes measured evidence, and
  checks the retained source. The wheel-integration CI job runs this one
  end-to-end smoke; the installer matrix keeps its lightweight discovery and
  inspection smoke. The same path passed locally against the development
  environment, while installed-wheel CI remains the publication gate. The
  wheel workflow runs that smoke in its own step before the long integration
  suite so its installed-client verdict is visible independently.
- The opt-in smoke now also invokes the installed `openhcs-benchmark
  run-measured` console script against a separately copied execution plate
  after the MCP process closes. It requires both receipts to agree on declared
  source/configuration identities and original plate, to carry server
  provenance, and to retain distinct job and output-root identities. This
  passed once in a local editable-environment live run; the installed-wheel
  step on the next exact CI head is still the publication gate.
- The measured-run artifact declaration now owns which files are produced by
  runtime execution and which by evidence finalization. The shared evidence
  writer checks for existing finalizer outputs before writing, so the direct
  wrapper, CLI, and MCP path all refuse to overwrite retained evidence under
  one rule rather than maintaining a separate MCP-only collision guard. The
  converted-CellProfiler parity integration now uses distinct evidence
  directories for the reference and second run, preserving the first output
  while it is used as a comparison input.
- The ordinary execution server now captures its Python identity and installed
  distribution versions once at startup and includes that snapshot in runtime
  observation exports. The benchmark receipt projects the snapshot from that
  export rather than guessing the remote environment from the client or adding
  a benchmark-only probe. Version-5 observation exports remain readable with
  no server snapshot. This establishes server provenance, not proof that remote
  workers run in an identical environment; matched comparisons must retain or
  verify worker provenance separately if workers can differ.
- Source-level tests must show the benchmark wrapper selects the same
  `PipelineDocument`, compiled plan, execution server, progress, and output
  artifacts as a normal run. No benchmark-only bypass may turn a failed compile
  or runtime validation into a successful observation.
- Fresh-process installed CLI and full-profile MCP tests must agree on request
  identity and receipt projection. Default desktop and hosted surfaces must
  remain intentionally bounded. Verify the new wheel-integration smoke against
  the exact PR head before calling the installed-client boundary closed.
- Run a small deterministic fixture for lifecycle/overhead checks; do not run
  the 30-workflow corpus or publish performance numbers in this infrastructure
  phase. A later matched experiment needs separately approved design and
  evidence review.

### 26 September verification checkpoint

The ordinary-pipeline benchmark wrapper landed in merged PR #128
(`1700acb45f578273edfc8530162040f0dbb52cac`). Its exact-head CI completed
successfully, including `wheel-integration-test`, whose installed-wheel smoke
invokes `--exercise-measured-execution`. On the local checkout, the focused
measured-run and benchmark-control unit tests passed 50/50, and the live ZMQ
observation-export integration tests passed 9/9. The first local unit attempt
used `/tmp` and failed with disk quota errors; the same tests passed with a
small exact test directory under `/home`, which was then removed. These checks
support infrastructure readiness for ordinary source-backed execution and
measured evidence finalization. They do not validate a 30-workflow four-mode
benchmark, a matched speedup, or the biological interpretation of any image
analysis result.

On the same local checkout after the 26 September analysis-side changes,
the focused measured-run, benchmark-control, and well-throughput unit files
passed 89/89 tests. Their 7 MiB temporary directory was removed after the
run. This is a current source-level regression check; the merged PR's
installed-wheel CI remains the separate installed-client evidence.

The generic measured-run CLI and expert finalization request now accept an
optional positive `expected_axis_count` and pass it to the existing shared
receipt finalizer. This is a declared workload-coverage check, not a second
execution status: an observed count mismatch prevents a success receipt.
The unmodified compiler-owned axis membership check still rejects missing or
unexpected axis identities even when callers omit the optional count. Focused
benchmark-control and measured-run unit tests plus a live synthetic CLI test
passed 55/55 on 26 September; the CLI test asserted a one-axis receipt carrying
both expected and observed counts. The temporary test directory was removed.
This new checkout state has not yet received installed-wheel CI verification.
An additional focused service test passed and proves the expert finalizer
forwards the declared count to the shared receipt writer. A fresh live MCP
integration attempt did **not** reach finalization: its new execution server
timed out while loading the cached function catalog (startup trace ended in
`preparing_capabilities`, with no server-ready event). The fresh CLI integration
above passed, but the MCP path's new count field is presently covered only by
the service-level test, not a completed live MCP run on these bytes. The failed
test's temporary directory was removed.
The generated expert MCP input schema was also checked in-process on these
bytes: it exposes `expected_axis_count` from the typed finalization request
without a benchmark-only hand-written schema; that focused test passed. The
fresh long-lived OpenHCS MCP process itself remains stale after analysis-side
source edits and requires its client-owned reconnect before further live tool
use. This does not invalidate the prior installed-wheel smoke on PR #128, but
it does leave this new field's fresh-process live MCP path unverified.
The positive-axis-count rule is now one function in the measured-receipt
contract, used by the CLI preflight, typed MCP request, shared finalizer, and
receipt validation. This also rejects booleans, rather than silently treating
`True` as one axis. The two focused benchmark-control/measured-run unit files
passed 57/57 on the current checkout; their 1.5 MiB `/tmp` test directory was
removed. This is not a replacement for the still-missing fresh-process MCP
end-to-end proof on the changed bytes.
Two additional focused receipt-construction checks passed: the same shared
rule rejects boolean expected and observed axis counts. The 40 KiB temporary
test directory was removed. The previous 57/57 run predates these two tests;
do not silently relabel it as a broader fresh-suite result.
The kernel journal for that failed startup records global out-of-memory kills
at 11:21:40 on 26 September, during the same capability-preparation window.
The killed processes shown were Brave helpers, not the test's Python server,
so this is evidence of host memory pressure rather than proof of the exact
server failure mechanism. Do not interpret the connection failure as a
benchmark-finalizer regression, or retry the heavy live test while RAM/swap
remain saturated. Keep the fresh-process MCP gate open for a healthy host.

### Current readiness boundary

- **Ordinary execution ownership:** the active benchmark adapter and
  throughput route call the shared measured-run wrapper, which delegates
  compile/execute to `run_compiled_pipeline`; the CLI and MCP finalizer use
  ordinary headless job control. A source scan found no active
  `PipelineOrchestrator` call under `benchmark/`. The direct client in
  `benchmark/results/matched_batch_pilot_20260915/pilot_driver.py` is a
  retained historical pilot, not an active registered command.
- **Evidence semantics:** value-scope exports validate compiled artifact
  expectations; outcome-scope exports validate exact compiled-axis membership
  and success but deliberately do not claim output-value equivalence. The
  caller may additionally declare an expected axis count through the shared
  contract. The expert MCP schema projects that field as an optional integer;
  its focused schema test passed.
- **Still open on these bytes:** a fresh-process live MCP finalization and
  installed-wheel test of the new count field, then a healthy-host check of
  the intended paper benchmark configuration. The prior green PR #128 wheel
  CI proves the pre-count-gate infrastructure, not this changed checkout.
  None of the tests so far proves a matched performance comparison or a
  biological analysis result.

The generated MCP integer schema alone was insufficient to prove strict input
handling: FastMCP/Pydantic coerced JSON `true` to integer `1` and dispatched
the finalizer to job lookup. The request now declares a strict integer, and
the generic dataclass-tool binding preserves `Annotated` metadata from the
typed request. A direct in-process MCP call with `expected_axis_count=true`
now fails argument validation before finalizer dispatch. The focused MCP
regression plus benchmark-control/self-description checks passed 57/57 on
26 September. This is source-level evidence only; the long-lived MCP server
reports stale source after the binding edit and requires a client-owned
reconnect. A fresh-process live finalization and wheel test remain open.

The installed-wheel smoke now declares one expected compiled axis through both
its expert MCP finalizer call and its ordinary measured CLI invocation,
asserts expected/observed counts in both receipts, and checks that a boolean
MCP axis count is rejected before job lookup. It now also tries to finalize
the same completed synthetic job with a deliberately wrong count of two,
requires the structured mismatch error and absence of a receipt, then
finalizes with the correct count of one. An in-process MCP service test proves
that mismatch-then-success sequence on these source bytes. The smoke's four
ownership unit tests passed. A local 0.8.6 wheel built from these checkout
bytes; its packaged benchmark request, measured CLI, measured-run wrapper,
and MCP server files
matched the source byte-for-byte. An isolated `--target` install outside the
checkout imported those wheel modules and its in-process MCP tool rejected
`expected_axis_count=true` with a strict-integer `ToolError`. This is stronger
than source-only testing, but it is not the fresh stdio execution smoke or
CI's fully installed environment. Those remain open while host swap is full.
The disposable local wheel was `openhcs-0.8.6-py3-none-any.whl` with SHA-256
`10f141a8e99d5776e0534c4c7b6c7e93bcf41601a5f25a14bad70205f6946293`;
the temporary install was removed after verification.
The current benchmark-control, measured-run, throughput-scaling, and installed
smoke ownership unit files passed together (103/103); their disposable
temporary directory was removed. This still does not execute the changed
installed smoke through a fresh stdio server.

A read-only reinspection of the retained eight-well BBBC022 matched pilot
(`benchmark/results/matched_bbbc022_20260923_rc5/`) found both the warm-up and
timed measured receipts valid under the current receipt inspector, with no
retained-evidence warnings. Each outcome-scope receipt declares and observes
eight axes. The inspector verifies the receipt's source, observation, and job
evidence, **not** the raw SQLite output values; those remain local to the
original pilot and its report. The pilot's one timed repetition and unequal
native/OpenHCS lifecycle boundaries do not establish a general speedup or
throughput ranking. This retrospective check supports the wrapper's retained
evidence path, not the changed installed MCP smoke or a new performance claim.
The retained pilot report itself records eight declared/output files on each
side and zero database/image differences in both repetitions, but a fresh
read-only rerun of the strict SQLite/properties comparator did not complete
within a 90-second bound on this swap-saturated host. Its timeout produced no
comparison verdict; do not relabel the historical report as newly reverified
value parity.
The 32 retained SQLite/CPA output files (eight native and eight OpenHCS files
in each of two repetitions) were independently hashed against that report's
per-file SHA-256 inventory: every digest matched, with no missing or
unexpected `.db`/`.properties` file. Thus the report still refers to these
exact local output bytes, although its semantic comparison has not been
re-executed on the current host.

### 26 September current-byte verification continuation

After the strict axis-count and analysis-side streaming changes, the focused
benchmark-control, measured-run, well-throughput, installed-smoke ownership,
plate-streaming, and viewer-streaming unit suite passed **144/144**. A small
live synthetic ZMQ integration test passed **1/1**: ordinary source-backed
submission exported its observation, and the in-process MCP finalizer retained
a receipt with expected and observed axis counts of one. This does not assert
biology or benchmark speedup.

A fresh local `openhcs-0.8.6` wheel was built from these checkout bytes
(SHA-256 `312adba0eed8959d742b45e4785ca631e7fede1126213f34fcf502e9090c03d4`),
installed into an isolated target outside the source tree, and confirmed as
the imported package. The opt-in installed-client smoke then completed with
exit code zero through a **fresh stdio MCP process** and the installed CLI.
It verified full-profile expert capability discovery, strict rejection of a
boolean `expected_axis_count` before job lookup, rejection of a deliberate
two-axis mismatch without a receipt, successful one-axis finalization and
inspection, and distinct ordinary execution IDs for MCP and CLI runs
(`f2917e7c-71db-4ab6-a2bf-0e7b642c8f5b` and
`35a6fd43-d8f7-4413-8ec3-04b0d0007a16`). This closes the earlier
fresh-process **local installed-client** gap for the changed field. It is not
CI on an exact published head, a 30-workflow matched comparison, output-value
parity, or a performance claim. Host swap remained full despite about 12 GiB
available RAM; the successful smoke is direct evidence for this bounded path,
not proof of memory safety under larger workloads.
