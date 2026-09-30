# Own slice projection at the image payload layer

The existing `ImagePayloadSliceProjector` now lives in `runtime_image_values` beside the payload metadata it projects. Scalar context and standalone mask helpers derive from this owner, and aligned batch unstacking and CellProfiler colocalization consume it. The duplicate scalar algorithm, separate masked-batch metadata reconstruction and unused metadata forwarding helper are removed. Each child receives a fresh metadata snapshot shared by its pixels and mask validation. No persistent mutable cache, function-name switch, new registry or new wrapper class is added.

Batch masks keep exact leading cardinality and bool conversion. Scalar source-binding masks may be shared spatial masks and preserve dtype. These different policies remain explicit on the same owner. Malformed batch cardinality is checked before child metadata axis errors. Alignment still owns paired output contexts and packing; source provenance still owns source identity and contributor semantics.

This is the user's requested ownership cleanup and a prerequisite for subsequent metadata work. Direct thread-local timers on unchanged main measured source metadata merging at 0.899s and leading-plane metadata selection at 0.793s within a 9.319s execution. Those inclusive scopes overlap and must not be summed. Slice duplication's estimated whole-well payoff is only 0.15–0.25s; it cannot close the whole performance target alone. The slower persistent metadata-index prototype was rejected. The query-local batch merge prototype was not promoted as a dominant fix.

Sequential ABBA replay of three saved real 60-plane bundles, eleven samples per observation:

| Step | Main medians | Candidate medians |
|---|---:|---:|
| Resize, 1 | 14.49 / 14.63ms | 7.57 / 7.58ms |
| ImageMath, 13 | 8.23 / 8.12ms | 6.58 / 6.57ms |
| Threshold, 17 | 14.97 / 14.77ms | 7.84 / 7.81ms |

Every replay checks exact payload types, metadata, contexts, pixels and mask dtype/values against the saved outputs. These are microreplays, not whole-runtime speedup evidence. All timed runs are sequential, pinned to CPU5, with tests/audits/builds stopped.

458 consumer tests pass, including the complete CellProfiler module execution file, provenance and source matching consumers, plane contracts, mutation isolation, distinct scalar/batch mask contracts and malformed-cardinality precedence. The unchanged scientific assertions remain exact. The shared environment passes dependency checking from `/tmp` with PYTHONPATH unset.

The original NRA census covers 702 modules and 5121 original ClassDefs: 5109 projected, 12 retained OPEN. The prior census is authenticated through unchanged OpenHCS/setup source to base 702b2c2c; a fresh after census preserves every original row. The ownership receipt names required/forbidden pairs and counterevidence. Exact revision-checked NRA transactions select and relocate the existing owner and remove duplicates. Their authored replacements check source and syntax, not arbitrary native equivalence; executed consumer and saved-artifact gates provide bounded behavior evidence. Dynamic external imports/pickles of the transient projector's old module path remain outside the platform serialization contract.

## Corrected diagnostic scope

Ordinary CPython 3.12.14 cProfile monitoring admits other threads into a profiler with one shared stack. The retained minimal reproduction records unrelated background sleeps and miscounts a function invoked once. Filtering all four callback families to the owner thread removes the unrelated events. The diagnostic-only subclass relies on private CPython callbacks and is not installed as a production abstraction. [CPython's profiler source](https://github.com/python/cpython/blob/v3.12.14/Modules/_lsprof.c) supplies those callbacks.

Historical cProfile phase timings and call-graph attribution in the header-reuse and aligned-output reports are qualified: they cannot establish causal phase reductions. Unprofiled public wall clocks, native header replay and exact output comparisons remain valid. The replacement diagnostic uses thread-local explicit timers and does not run cProfile. Its receipt records 32 pattern groups, 26821 metadata merge calls and 6540 leading-plane projection calls with the scopes stated above.

Scientific parity and whole-runtime acceptance are recorded separately from microreplay and structural checks. Pipeline clocks exclude ZMQ startup/shutdown; mandatory registry/callable/kernel preparation completes before readiness and workers use fork. Native CellProfiler and multiwell scaling are still pending for the newest changes; older native timings are not presented as fresh results.

Refs #318, #319, #162. The broad performance goal remains active.
