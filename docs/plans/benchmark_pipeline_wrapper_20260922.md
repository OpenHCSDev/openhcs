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
- The measured-run artifact declaration now owns which files are produced by
  runtime execution and which by evidence finalization. The shared evidence
  writer checks for existing finalizer outputs before writing, so the direct
  wrapper, CLI, and MCP path all refuse to overwrite retained evidence under
  one rule rather than maintaining a separate MCP-only collision guard. The
  converted-CellProfiler parity integration now uses distinct evidence
  directories for the reference and second run, preserving the first output
  while it is used as a comparison input.
- Environment evidence is still incomplete: the receipt records client
  interpreter/package location, OpenHCS application versions and endpoint
  identity, but not the server/worker Python and dependency versions that a
  matched comparison would need. Capture those at the ordinary runtime owner
  and project them into the receipt; do not infer a remote server environment
  from the client or add a benchmark-only server probe.
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
