Analysis consolidation system
=============================

Analysis consolidation is a post-plate operation over materialised tabular
artifacts. It is separate from callable execution and does not reopen an output
path to rediscover content already recorded by the runtime.

Consolidation is a microscopy post-execute hook. ``AnalysisConsolidationHook``
is a ``PostExecuteHook`` bound from the global ``AnalysisConsolidationConfig``
and ``PlateMetadataConfig`` and carried by each compiled processing context.
When a step saves CSV outputs, the hook records the exact text the writer saved,
keeping only files the consolidation selection includes; explicitly reused debug
outputs are read back through their compiled backend. These observations travel
in each context's runtime observation. After every partition succeeds, they are
combined, grouped by materialisation directory, and passed to the analysis
consolidation functions. Each directory retains its compiled persistent
destination. Consolidation therefore neither renders outputs again, scans a
results directory, nor treats a virtual backend address as a host file.

The generic consolidation layer reads ``AnalysisTableSource`` values and writes
through an ``AnalysisSummaryWriter`` ABC. Local desktop consolidation uses a
filesystem writer. Compiled execution uses a FileManager writer bound to the
exact persistent backend and obtains save context through that backend's
``DataSink`` declaration. Per-result summaries use their owning step's storage
context, including step-specific output subdirectories. The global table is
merged in memory and written beneath the compiled output plate root using the
shared main-flow storage context. It does not write into the input plate.

Ownership
---------

- callable or module declarations own artifact production semantics;
- the compiler owns artifact satisfaction and materialisation plans;
- the runtime records typed addresses and values produced by the exact
  execution;
- each ``DataSink`` owns contextual persistence arguments for its backend;
- the consolidation layer owns well extraction, exclusions, merging, summary
  rendering, and summary filenames.

Consolidation never infers missing artifacts from step names and does not mutate
compiled plans. A source or destination failure is raised as an execution
failure rather than logged and discarded. Manual desktop consolidation uses the
same analysis functions on an explicitly selected results directory.

See :doc:`artifact_contract_system` and
:doc:`../user_guide/analysis_consolidation`.
