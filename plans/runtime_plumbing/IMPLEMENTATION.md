# Runtime performance plan integration

User input: `plans/perofrmance_plan.zip`, SHA256 `52949085276b0974243b54c3a2766e2ffae77c691e40a3796aa072eb34bd061b`. The seven supplied documents in this directory are unchanged. Their reference source is main `3f76f5e1`; implementation starts from main `175262f0` after #641.

The active performance objective remains execution and total pipeline latency, with CellProfiler parity. Server startup is excluded. Refactoring completion and measured runtime improvement are separate claims.

| Surface | Existing determining owners | Integration status and obligations |
|---|---|---|
| P0 | RuntimeProfileLogger; worker/run lifecycle | In progress first. Consolidate all profile emitters into a run-owned raw event buffer; flush outside callable/chain timed regions, retain failure cleanup and independent worker/run lifetimes. Capture baseline before execution refactors. |
| P1 | CompiledFunctionInvocation; CallableContract; CompiledStepPlan | Compile fixed memory, ABI, bindings and return-layout decisions. Adapter requests/current pixels/active edges remain invocation-owned. Build debug parameters only for debug or the existing declaration-error diagnostics. Preserve eager adapter binding and error epochs. |
| P2 | Plate inventory and declared source bindings | Parse physical source filenames once and index components. Produced filename aliases remain live; do not reintroduce the stale alias cache removed by #638. |
| P3 | StepOutputManifestStore; compiled pattern/step declaration | Replace whole-cohort rebuilds and global invalidation with incremental per-producer records. Preserve inherited-domain replacement, insertion order, last-write replacement, begin-step epochs and live aliases. |
| P4 | ProcessingContext; source projection authority; manifest | Hold context-owned projections, lazy log formatting, producer order derived from P3. Preserve ambiguity/cohort admission before cached payload return. |
| P5 | CompiledStepPlan; compiled invocation; device scope | Plan memory/device boundaries across steps. Keep preprocessing InputConversionPlan distinct from runtime placement. Validate mixed CPU/GPU semantics separately; a CPU-only profile cannot prove a GPU gain. |

#641 is merged and removes post-compilation kernel warming; normal registry READY is the only child-cache consumer. Full catalog READY qualification passed. #630 (runtime ownership refactor), #635 (intensity maxima) and #597 (saved compiler resolution) remain drafts with negative whole-pipeline observations. They are not performance acceptance for this plan.

Required final evidence: corrected baseline and integrated execution profile on the same real pipeline; production benchmark before/after execution and total time; affected parity, MCP and GUI behavior; mixed-device receiving for P5. Each implementation PR must close its corresponding issue and declare any persisted format changes.
