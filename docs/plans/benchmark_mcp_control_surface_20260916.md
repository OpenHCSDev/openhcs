# Benchmark MCP control-surface ownership plan

## Scope and safety boundary

This plan is based on committed `main` revision
`b2f3cf83b70238856193d669c0893d32ad958362`.  It intentionally excludes the
dirty shared checkout, the running Official30 proof, native reference trees,
and paper figure work.  Implementation and validation run only in the
disposable worktree `/tmp/openhcs-benchmark-mcp-20260916`.

## Ownership inventory

| Semantic question | Current owner | Derived consumers | Gap |
|---|---|---|---|
| Which benchmark commands exist? | `BenchmarkCliCommand.__registry__` | `scripts/benchmark_cellprofiler_vs_openhcs.py` argparse construction | The command family is source-checkout-only and has no reusable catalog projection. |
| Which cases and roots belong to a comparison? | `ComparisonManifest` and manifest JSON | comparison loader, compatibility report | Preserve this authority; do not introduce an MCP manifest registry. |
| Which settings govern one comparison run? | `ComparisonSuiteRunContext` | case runner and `suite_metadata.json` | The metadata writer manually mirrors six context fields and omits status, expected work, manifest identity, and rerun invocation. |
| What progress has completed? | append-only `observations.jsonl` plus the run context's expected case/repeat count | CSV summaries | There is no agent-facing projection.  The separate log parser is not needed for comparison-suite progress. |
| Where are result artifacts? | Files written below the selected output directory | plotting and audit scripts | Filenames are repeated at call sites and agents must know repository scripts.  The control surface can derive the current artifact set from the directory rather than add another list. |
| Which MCP tools exist? | `AgentCapabilityDeclaration.__registry__` | FastMCP generated bindings and capability registry | No benchmark capability is declared. |

### Concrete surface inventory

- Registered CLI commands: `run`, `official-cp3-manifest`, `plot`,
  `plot-well-throughput-presentation`, and `bioformats-hcs-validate`.  The
  source-checkout script rebuilt their root parser even though the subcommands
  were already registered declarations.
- Maintained comparison manifests: focused translocation, two legacy expanded
  official sets, the portable Official30, the 2026-09-14 existing-image refresh,
  and the 2026-09-14 value-completion set.  Their JSON plus
  `ComparisonManifest` remain the case/path authority; none are copied into the
  MCP layer.
- Comparison result schema: append-only `observations.jsonl`, observation and
  phase CSVs, aggregate `summary.csv`, `suite_metadata.json`, and four
  registry-derived module-coverage artifacts.  Historical lab-meeting and
  diagnostic directories contain compatible subsets plus figure inputs; they
  are evidence, not a result registry.
- Generation/plotting entry points: the registered `plot` and
  `plot-well-throughput-presentation` commands call
  `benchmark.reports.cppipe_figures` and `WellThroughputPresentationReport`;
  older `scripts/generate_*benchmark_figures.py` wrappers remain separate
  historical/convenience surfaces.  This slice exposes the registered command
  family and does not expand those older scripts into MCP tools.
- Progress surfaces: comparison execution incrementally appends
  `observations.jsonl`; well-throughput execution writes typed progress CSVs;
  `benchmark.progress` parses retained console logs but has no production
  consumer.  The bounded MCP inspection uses the comparison observation
  authority and leaves log-parser ownership for a later refactor.

## NRA evidence

The full-context NRA scan covered `benchmark`, `openhcs/agent`, and
`openhcs/mcp` with 79 analyzed detectors and zero omissions.  It reported 39
findings.  The directly relevant certified finding is
`semantic_mirror_without_descent` at
`benchmark/cellprofiler_comparison.py:1055`: the `suite_metadata.json` payload
mirrors six members of `ComparisonSuiteRunContext`.  NRA also reported that the
benchmark log progress enum is dispatched externally; that larger log-parser
redesign is outside this bounded slice because comparison progress is already
available from the append-only observation artifact.

## Bounded migration closure

1. Introduce a nominal `ComparisonSuiteRunReceipt` at the benchmark contract
   boundary.  It owns schema-derived parsing, validation, and atomic JSON
   serialization; the runtime context only constructs the typed receipt.
2. Have the comparison runner write that receipt with the typed
   `ComparisonSuiteRunStatus` as `running`, `failed`, or `completed`, while
   retaining all existing scientific observation and CSV semantics.
3. Move parser construction into the registered command module and expose an
   installed `openhcs-benchmark` entry point.  Parser construction remains
   derived from `BenchmarkCliCommand.registered_commands()`; the MCP discovery
   path imports only lightweight contracts and does not eagerly import this
   execution module.
4. Add a read-only benchmark inspection service that validates the requested
   directory through `AgentPathPolicy`, reads exact rerun arguments from the
   run receipt and progress from append-only observations, and discovers
   structured files from the directory.  Lifecycle and artifact identities
   remain enums until the existing MCP JSON projection edge.
5. Declare one expert, local-only `AgentCapabilityDeclaration` for that request.
   Existing generated MCP dataclass-request binding must expose it; no MCP
   server registration branch is added.
6. Prove run-receipt behavior, artifact/progress inspection, registry discovery,
   generated MCP binding, and package inclusion with focused tests, then run the
   broader agent/MCP and benchmark contract suites that exercise the shared
   boundaries.

## Deliberately deferred

- Launching or cancelling benchmarks through MCP.
- Migrating throughput and Bio-Formats result schemas into the comparison-run
  receipt.
- Redesigning `benchmark.progress.BenchmarkProgressEventKind` dispatch.
- Reworking historical result directories that predate the receipt fields.
- Any execution of the Official30 manifest or mutation of retained references.
