Runtime owner consolidation
===========================

These changes remove parallel runtime representations and move their behavior
onto existing authorities. They support further optimization; class deletion is
not evidence of an end-to-end speedup.

Ownership and consumer closure
------------------------------

``RuntimeArtifactInputRequest`` is removed. The existing CP artifact strategy
family consumes ``ArtifactSpec`` and the resolved value directly. Input
selection, raw versus normalized values, source axes and post-call source
resolution retain their existing owners. This change is merged into main as
PR #535, closing #534. The clean main candidate ``c828acaee`` passes all 541
module, shape, source, store and direct-value controls. Shape fixtures follow
the current declared label domain and completed CP ordinals, including missing
entries; original stale-fixture failures are retained.

``PatternGroupOutputData`` and its validation/unstack endpoint are removed.
``PatternGroupRuntime`` publishes the original output. ``AlignedImageStack``
owns topology; ``ImagePayloadStackComposition`` owns independent buffers and
saved context; produced records determine cleanup. The sole-consumer
``RuntimeSliceAlignedImageOutputContext`` is also removed, with its algorithm
on the existing source strategy. The source-qualified output gate passes 238
tests, including real partial writes, masks, opaque/source-bound domains,
duplicate-path preservation and subclass effects.

The attempted deletion of ``ProjectedFunctionOutputContextStrategy`` failed
the registered-family gate: its inheritance carries fallback precedence.
The class remains and owns the actual common algorithm. The obsolete
grandparent-forwarding implementation is removed. The selector is unchanged.
The initial failed source and control receipts are retained.

``FunctionInvocationArtifactScope`` is folded into its only concrete consumer,
``FunctionCoreExecutor``. The existing seven field declarations and method
bodies are unchanged. Constructor order, frozen slots, pickle, metadata-edge
polymorphism, debug behavior and first errors pass 158 controls. Historical
reports naming the old scope remain as evidence of their original source.

Publication reader consolidation uses the existing document handler and source
projection builder. Required projection-only viewer consumers remain. Its 94
reader controls pass; four saved-operand replays remove 151ms median locally
while preserving ordered paths and five complete atomic transaction results.
This duplicate read exists in the draft branch. Main already reads once, so
no separate main performance PR is warranted for this change.

Checkpoint ownership correction
-------------------------------

The identical current-main checkpoint fixture passes its required 48 files
while the draft branch originally produced only 24 named files. Issue #536
tracks this branch regression. Named artifact materialization and ordinary
checkpoint publication were assigning the same artifact-name qualifier.

Commit ``0dd77da46`` derives topology once at the existing save boundary.
Unwrapped canonical returns use ordinary source filenames while retaining
typed producer context; explicit named aligned outputs retain qualifiers.
The materialization owner keeps its explicit artifact-name policy. No extra
copy, wrapper or per-function flag is introduced. All 199 relevant controls
pass, including unchanged 48-file inventories, metadata reopening, yeast,
labels, table passthrough and opaque domains. The original saver reproduces
the new unwrapped-path control failure.

Evidence scope
--------------

The source-qualified gates above overlap and refer to separate revisions;
their counts are not a combined whole-branch pass. NRA original-class census,
family projection and method comparison support ownership inspection, not
complete runtime equivalence. Unchanged method bodies do not prove constructor
or effect behavior; those have separate executed controls.

PR #394 remains draft. Its original whole-branch R0/R1 obligations, installed
consumer acceptance, full-catalog parity and fresh full30/scaling figures
remain open. Startup and required library/kernel preparation remain outside
pipeline clocks. The performance goal remains active.
