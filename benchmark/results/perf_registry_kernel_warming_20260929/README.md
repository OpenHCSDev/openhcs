# Kernel caches through registry warming

The ZMQ endpoint's existing lazy catalog preparation now prepares persistent kernels through its supervised registry child. The admitted catalog callables derive the existing `PreparationCacheBatch` and `CallablePreparation` obligations. A valid metadata cache still triggers kernel warming. The same Future publishes readiness only after preparation; cancellation propagates to that child and stops/reaps its exact fork workers. Direct pipeline compilation continues to prepare its selected callables, without waiting for an unrelated full catalog.

Two preparation omissions found in the first production replay were also corrected: the Sobel family now declares compiler preparation through its existing registered strategies, and expand/shrink warmup derives all registered operations against point and region fixtures instead of a manual two-strategy roster. These cover Sobel and int32 shrink signatures observed compiling during execution.

| Observation | Seconds |
| --- | ---: |
| Full catalog warmup, valid metadata / empty explicit kernel cache | 53.529 |
| Subsequent fresh ordinary 1w_1t compilation | 3.277 |
| Subsequent ordinary execution, including export | 18.875 |
| Subsequent ordinary total | 24.893 |

Warmup started with zero `.nbi` files and ended with 205, for 266 catalog functions. The subsequent fresh endpoint loaded 65 Numba cached artifacts and saved zero. CSV output is byte-identical to the previous ordinary output: 11,550,064 bytes, SHA256 `3e00436ae1500047fd2605021ae055492b17dbe0b4aa4ddbe2f62af6f8e073be`.

This is advance preparation amortized across future pipelines. **The 53.529-second warmup is excluded from the 24.893-second ordinary total**; including both would cost 78.422 seconds. It does not reduce first-ever cold end-to-end latency, establish a statistically meaningful execution speedup, prove all runtime signatures for every pipeline are cached, or prove cache=False kernel reuse. That work remains under #162 and the performance goal. Native CP was not rerun for this preparation-only change.

Fresh spawned-interpreter evidence is retained separately: two workers hydrate representative intensity and shape families from this registry-populated cache, with twelve cache hits and zero misses each. The probe covers those families, not every catalog function.

821 focused tests pass in three disjoint suites: 65 preparation/discovery/ZMQ/kernel coverage, 206 compiler/runtime/source identity, and 550 backend/module tests. A live SIGTERM regression starts two slow forked workers, cancels their catalog parent, and verifies both workers are reaped. An isolated cold-cache regression asserts preparation prevents new Sobel/int32-shrink dispatcher signatures and misses at runtime. Black, diff checks, and no-new-Ruff checks pass.

Source authority: main fbf6b2d91 plus this PR. Shared Python 3.12 environment uses current main dependency revisions, including PolyStore 1209068. See the receipt for installed distributions, source roots, submission identities and phase timings; input staging precedes the ordinary total timer. The initial global NRA syntax/class census and focused ownership decision are not a full semantic proof.
