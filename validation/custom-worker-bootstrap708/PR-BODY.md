Addresses #708. Implemented source/process checkpoint; installed public receiving remains pending.

The determining native traceback fails in `multiprocessing.reduction.dump(process_obj)`, while starting the first spawned worker—not while pickling the normalized task. `ValidatedCompiledPlateExecution` was passed as initializer progress context despite carrying rich pipeline/runtime contexts. The initializer never used its identity fields.

This deletes that unused argument, factory field and sole production constructor input. The original queue, lane identity, custom-source revision registry and FunctionReference task transport remain owners. No export alias, second registry, serializer, compatibility argument or timeout change.

Qualification:

- Real `WorkerExecutorFactory` spawn resolves two persisted custom declarations, invokes them, returns nominal helper rows and emits exact execution/plate/PID success progress on the original queue.
- 37 lane/factory controls passed, including inline/thread/fork. One pre-existing stale cancellation fixture was migrated to `WorkerLaneExecutionContext`, preserving its assertion; focused cancellation + spawn: 2 PASS.
- Original source-backing/setup failures and the stale fixture failure are preserved byte-exact, not relabeled product failures or omitted.
- Existing audit parser: all 701 production / 705 test modules parsed; 42/57 complete relevant ASTs retained, plus original stdlib spawn/pool/queue dependencies. Original two-file R0: no positive deltas, no parse omissions. No global R1 claim.

Source/process acceptance is not installed/public readiness. Planck owns ONE future whole 697/709/706 bundle; Singer owns public registered custom-source validation/compile/execute with two workers/tiny axes, progress/terminal/artifact verification and exact closure. The original failed science job is never replayed; frozen SCI08 is unchanged. No hosted CI hold.

Full receipt: `docs/validation/custom-worker-bootstrap-20261004.rst`; original source/log/AST archive: `docs/validation/custom-worker-bootstrap-20261004.tar.gz` (SHA256 `43720aec4cb68ab5bc84ab39022402029566e1c83a8284577088477da1467a45`). Normal current-main integration leaves both qualified production files byte-identical. All eight foreign gitlink modifications and prior evidence are preserved.
