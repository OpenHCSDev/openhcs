# OpenHCS runtime plumbing

**Head:** OpenHCS `main` at `3f76f5e1`. **Rules:** `docs/refactor/00-RULES.md`. Line numbers refer to that head.

## The question

Generic runtime plumbing takes too long relative to the callables it runs. Reading the execution path from `PatternGroupRuntime.run` (`openhcs/core/steps/function_runtime.py:1454`) through `execute` (`:1058`) and `invoke` (`:1159`) gives one answer: **facts that are fixed for a step, a plate or a run are re-derived per pattern group or per function call, because no object owns them.** The `PipelineCompiler` exists so the runtime can be thin; these are compile-time facts the runtime recomputes. It's the same defect as duplicated authority, appearing as cost.

## What runs, and how often

| Work | Recurs per | Depends only on |
|---|---|---|
| Memory types, target device | function call | contract, execution plan |
| A newly constructed runtime adapter | function call | plan, plus group-invariant payload metadata |
| Main-flow projection through the contract | function call | contract's declared processing and raw ABI |
| A new `RuntimeReturnedOutputMatcher` | function call | contract, output plans |
| Two copies of the arguments, one only for debugging | function call | nothing |
| `logger.info(f"Executing function: …")`, formatted at any level | function call | nothing |
| Filename parsing and component lookup | pattern group, every step | the file name |
| A new `VirtualWorkspaceSourceProjectionAuthority` | pattern group | the context |
| Rebuilding all of a step's output records, and clearing every selection cache | pattern group | grows with groups done: quadratic per step and well |
| Memory conversion | function call | the step sequence's memory types |

## Surfaces

| ID | Fix | Recurs per |
|---|---|---|
| [P0](P0-trustworthy-profile.md) | The profiler stops measuring itself | every record |
| [P1](P1-compiled-invocation.md) | A compiled invocation | function call |
| [P2](P2-parse-once.md) | Filenames parsed once, files indexed by component | pattern group and step |
| [P3](P3-manifest-store.md) | The output manifest grows linearly | pattern group |
| [P4](P4-held-and-lazy.md) | Held objects and lazy logging | pattern group and call |
| [P5](P5-memory-plan.md) | Conversions planned across steps | function call |

## Order

1. **P0 first,** so every measurement after it is trustworthy. Record the baseline split between plumbing and callable time on a real pipeline with it.
2. **P1 and P2,** the most frequent costs, in parallel.
3. **P3 and P4.**
4. **P5,** which needs compiler work, last.
5. Re-run the corrected profiler on the same pipeline and post the before-and-after split.

## Crossings

- **#394** (`perf/shared-runtime-plumbing`) added `CallableContractRuntimeCache` and an identity-bound process cache. P1 builds on that intent; a cache still pays a key and a lookup per call, while a compiled invocation held by the runtime pays nothing.
- **S4** (pipeline compilation) in `docs/refactor/` owns `PipelineCompiler`; P1 and P5 extend what it produces, so whoever takes P1 coordinates with S4's owner.
- **P2** gives the plate's file inventory ownership of filename metadata, which the source-binding rules already require: no filename parsing outside the declared source bindings.
