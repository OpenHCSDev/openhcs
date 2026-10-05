# Shared owners for output projection and lexical path reuse

`AlignedImageStack.projected_output_slices()` owns one correlated payload/context traversal. `ImageOutputBundle` inherits the exact same implementation. Existing flattening consumers derive from this owner; the separate context traversal is deleted. Existing `PatternGroupOutputData.from_aligned_stack()` materializes the runtime result and preserves its original stack policy. The generic runtime invokes that contract instead of reconstructing image metadata a second time merely to count contexts. No function-name, pipeline-name, or mask-specific runtime optimization is introduced.

The existing `source_path_identity` module owns one bounded immutable native `Path` cache. Filename, stem, parent, absolute and POSIX views derive from it; relative and join derivations preserve native lexical semantics and errors. Ten duplicate helpers in five consumers are removed. Source membership, output provenance, manifest indexing and writer-specific naming remain on their domain owners. No mutable metadata, pixels, filesystem contents or live handles are retained by this lexical cache.

## Ownership audit

The full original-class census covers 702 modules and 5121 original classes; 5109 are projected and 12 original unprojected declarations remain OPEN. The separate NRA lexical cache inventory retains 103 cached declarations and 14 cache-family declarations. That inventory is retrieval evidence, not a universal purity or live-binding proof. The bounded decision receipt traces concrete declarations, consumers, required/forbidden pairs and counterevidence.

| Fact family | Existing determining owner | Decision |
|---|---|---|
| Aligned output payload/context fanout | `AlignedImageStack` | Move shared algorithm here; inherited by output bundles |
| Runtime output materialization | `PatternGroupOutputData` | Preserve stack policy and derive from paired projection |
| Lexical path reuse | `source_path_identity` / immutable native `Path` | Delete ten local caches and migrate their consumers |
| Declared callable/kernel preparation | `PreparationOperation`, `CallablePreparation`, `PreparationCacheBatch`, `RegistryService` | Retain generic pre-readiness orchestration |
| Invocation contracts and execution-local stacks | `FunctionInvocationCallableResolver`, existing runtime lifecycle | Retain shared infrastructure |
| Successful immutable file headers | `ImageFileFormat` and `ImageFileRevision` | Retain format-owned revision cache; concrete readers parse |
| Correlated source membership | `SourceIdentityResolutionContext` | Retain query-local membership authority |
| Producer tokens and provenance | `StepOutputManifestStore`, `FunctionOutputIdentityCache` | Retain their domain indices; derive lexical views |
| Mathematical keys, ranks and kernel declarations | Concrete numerical/provider families | Retain intrinsic numerical behavior; platform consumes nominal batch declarations |

No new registry, wrapper class, manual roster or competing authority is added. The old Costes-specific field is already absent from `ProcessingContext`; declared `RuntimeBatchProgram` consumers own orchestration. This is a bounded audit and migration, not a claim that every remaining cache has been formally proved correctly owned.

## Performance and parity

**Diagnostic qualification:** a subsequent [thread-isolation reproduction and direct-timer replacement](../perf_payload_slice_projection_owner_20260930/README.md#corrected-diagnostic-scope) shows that CPython 3.12.14 cProfile can admit unrelated background threads into its shared stack. The historical profiled phase timings and call-graph attribution below are archived observations, not reliable evidence of causal phase reductions. The unprofiled ABBA, sequential saved-input replay and exact output parity remain valid.

Earlier fresh installed profiling attributed 1.941s to output validation/unstacking, with 2820 scalar image projections; pixel stack calls across the measured phases cost approximately 0.057s. Metadata/provenance reconstruction, rather than raw image stacking, dominates this measured overhead. The estimated payoff of removing the duplicate traversal was only 0.2–0.3s per 19-bundle well: a structural prerequisite for the larger metadata improvement, not a whole-execution target achievement.

Sequential production replay on three actual saved 60-plane bundles (seven samples each, no overlapping checks) has median projection times of 29.07→14.50ms, 16.88→8.21ms and 30.04→15.13ms. Metadata, masks, pixels and contexts match saved outputs exactly. One earlier replay accidentally overlapped audits and its counterpart; its timing is explicitly rejected and retained, not pooled with the accepted replay. Replay revisions are c2d82ba23 / 3b6f39c9b, before the subsequent viewer merge; the common projection source is unchanged in that merge.

Current-main d1c6ab72c versus installed candidate c20b56b41, separate unprofiled ABBA:

| Mean, two observations per version | Main | Candidate |
|---|---:|---:|
| Compilation | 1.679s | 1.765s |
| Execution | 9.366s | 9.715s |
| Pipeline total | 11.783s | 12.195s |

**No overall speedup is demonstrated in this series.** Candidate execution observations are 10.572s and 8.858s; the measured mean is higher. Do not causally attribute this variance without separate evidence. The archived installed diagnostic recorded scalar image projections 2820→1680, leading-plane metadata reconstructions 4320→2580 and profiled output validation/unstacking 1.941→1.265s. Those cProfile observations are subject to the thread-isolation qualification above; they do not confirm causal phase savings. Continue the larger shared metadata/provenance improvement using isolated diagnostics and unprofiled clocks.

All 24 complete measurement CSVs and 480 label images across the four observations match the saved successful control exactly. Both filenames and label dtype/shape/pixels are checked. The distinct profiled candidate also checks complete output parity. No scientific assertion or tolerance was loosened.

Pipeline clocks exclude ZMQ server startup and shutdown. Mandatory registry/callable/kernel preparation completes before endpoint readiness; workers fork. These observations use CPU5, 1w_1t and a shared warm on-disk Numba cache. CLI clocks are recorded separately. No timed pipeline/prewarm/replay overlaps our tests, audits, builds or other benchmarks. Native CP and multiwell scaling were not rerun in this checkpoint.

## Validation and integration

Current main and all current dependency pins were normally merged before the final gates and installed ABI3 wheel benchmark. Source hashes for all eight refactor modules and five newly merged viewer modules are recorded. The shared environment uses normally resolving editable installations. The initial source-directory pip check missed a stale duplicate editable record; [outside-source correction and merged-main acceptance](../../../docs/validation/duplicate_editable_metadata_20260930/README.md) retain that failure and establish one active distribution with clean dependency resolution.

769 affected consumer tests pass, including masked/unmasked, named/anonymous, shallow nesting, strict cardinality, shared parent method lookup, fresh metadata snapshots after source mutation, output manifests, path planning, provenance, source admission and current calibration consumers. Three initial failing fixture cases were independently reproduced on unchanged main. Two fixture declarations were corrected to the existing strict contract while preserving every assertion: declare consumed artifact parameters, and keep a stored auxiliary fixture out of the admitted main-flow set. Original failures and main counterexamples are retained.

Scoped current-main R0/R1 show no increases; the existing redundant type-check finding remains visible. R1 materializes the complete committed parent/dependency context (3030 projections/version), reporting only eight changed production modules. Authored NRA transactions check exact revisions and syntax; they do not automatically prove native constructors, metaclasses, effects or execution equivalence. The executed consumers, saved-input replay and installed complete parity supply the bounded behavior evidence.

See [ownership decision](validation/perf-runtime-projection-ownership-decision-20260930.json), [cache inventory](validation/perf-runtime-projection-global-cache-declaration-inventory-20260930.json), [provenance](validation/perf-runtime-projection-platform-current-provenance-20260930.json), [complete observations](validation/perf-runtime-projection-platform-abba-observations-20260930.json), [parity and means](validation/perf-runtime-projection-platform-comparison-20260930.json), [profiled phase transfer](validation/perf-runtime-projection-platform-phase-comparison-20260930.json), [structural scope](validation/structural_checks.json), and [figure](comparison.png). Reproduction recipes and exact NRA transactions are retained under `recipes/`. Full census, native images, captured bundles and profiles remain in `/home/ts/code/projects/openhcs-benchmark-runs/`.

Fixes #307. Refs #162. The broad execution performance goal remains active.
