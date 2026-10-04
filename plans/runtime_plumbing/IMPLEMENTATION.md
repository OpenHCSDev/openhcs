# Runtime performance plan integration

User input: `plans/perofrmance_plan.zip`, SHA256 `52949085276b0974243b54c3a2766e2ffae77c691e40a3796aa072eb34bd061b`. The seven supplied documents in this directory are unchanged. Their reference source is main `3f76f5e1`; implementation starts from main `175262f0` after #641.

The active performance objective remains execution and total pipeline latency, with CellProfiler parity. Server startup is excluded. Refactoring completion and measured runtime improvement are separate claims.

| Surface | Existing determining owners | Integration status and obligations |
|---|---|---|
| P0 | RuntimeProfileLogger; worker/run lifecycle | Implemented in #645 and integrated here. One raw worker-run buffer and final flush; independent failure/fork/thread lifetimes. Real 3D diagnostic completed, with strict comparison against both retained native outputs. Observer disposition is separate from ordinary latency. |
| P1 | CompiledFunctionInvocation; CallableContract; CompiledStepPlan | Compile fixed memory, ABI, bindings and return-layout decisions. Adapter requests/current pixels/active edges remain invocation-owned. Build debug parameters only for debug or the existing declaration-error diagnostics. Preserve eager adapter binding and error epochs. |
| P2 | RuntimePatternDiscoveryCache; declared source bindings | Implemented in c1650d8. Production consumer probe confirms one physical filename parse across discovery, matching and indexed group selection, and re-admission when parser semantics change. Produced filename aliases remain live. |
| P3 | StepOutputManifestStore; CompiledFunctionPattern | Implemented in 88522fb. Ordered address maps update only new records; producer-scoped invalidation eliminates revision counters. Existing immutable DurableSourceMetadata fixes publication slots; source metadata and filename aliases remain live. Publication policy explicitly approved by user. Derived path order is retained without changing insertion order. |
| P4 | ProcessingContext; source projection authority; manifest | Implemented in c1650d8. Held authority rebinds strong owners; optional file eligibility and document changes remain live. Lazy logging and retained P3 order remove per-group formatting/sorting. Ambiguity admission still precedes cached payload return. |
| P5 | CompiledStepPlan; compiled invocation; device scope | Plan memory/device boundaries across steps. Keep preprocessing InputConversionPlan distinct from runtime placement. Validate mixed CPU/GPU semantics separately; a CPU-only profile cannot prove a GPU gain. |

#641 is merged and removes post-compilation kernel warming; normal registry READY is the only child-cache consumer. Full catalog READY qualification passed. #630 (runtime ownership refactor), #635 (intensity maxima) and #597 (saved compiler resolution) remain drafts with negative whole-pipeline observations. They are not performance acceptance for this plan.

Required final evidence: corrected baseline and integrated execution profile on the same real pipeline; production benchmark before/after execution and total time; affected parity, MCP and GUI behavior; mixed-device receiving for P5. Each implementation PR must close its corresponding issue and declare any persisted format changes.

Implementation is tracked by #647 and closing draft #648. Current source merges P0 head 1236f744 and main 602d577. The integrated source/projection/manifest/profile gate passes 127 controls in 2.51s; this verifies behavior and metadata pickle/cloudpickle transport, not runtime improvement. Actual parse/rebind/optional-document production receiving is retained under the runtime-file-inventory receipts in the maintenance namespace. P1/P5 remain active and no integrated speedup is accepted yet.
