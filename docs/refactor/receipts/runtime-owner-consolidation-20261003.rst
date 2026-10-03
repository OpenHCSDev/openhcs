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

``RuntimeImageRequest`` and ``RuntimeFunctionInvocationRequest`` are removed.
``CellProfilerImageRequest`` owns the image domain and actual callable kwargs
through execution and output recording, eliminating the five-field copy-back
step. Original aliases survive object-driven changes in image shape/count.
The shared ``RuntimeImageExecutionContext`` remains the parent for genuine
batch and measurement consumers. This lane is merged into main as PR #538,
closing #537. The clean main candidate ``7e2f97f80`` passes all 780 tests in
the 17-file execution, library, recording, binding, axis and stream gate.
The pre-existing retained-plane shape fixture now explicitly declares its
object plane domain; its Area and true-volume assertions remain intact.

The parsed-module contract boundary now uses the existing prepared-callable
factory, matching authored compilation. The original Crop equality failure
reproduces before the carrier deletion. Commit ``5c3e12ecd`` fixes its actual
production boundary; all 641 execution/library/binding controls pass without
removing signature fields from equality or changing the original assertion.
Two additional declaration fixtures failed identically before that fix: they
omitted the existing seven QA outputs and the step-owned Costes runtime input.
Their updated assertions retain original ABI counts and add complete diagnostic
names/roles and runtime parameter checks. The final six-module contract gate
passes all 100 tests. After merging PR #538, the exact retained-plane and alias
controls pass all ten tests; an identical test duplicated by Git's merge is
removed, leaving its original definition intact.

``CellProfilerOutputRecordRequest`` now specializes the existing input-binding
owner. Adapter, kwargs and current image are inherited once, and two temporary
binding-holder constructions are removed. The binding edge operation remains
``artifact_value(edge)``; the record's distinct declaration operation is
``declared_artifact_value(spec)``. Output-plan admission, exact endpoints,
reference broadcasts, live per-read validation and mutation epochs remain
separate and tested. Explicit subsets satisfy the inherited admission law;
record construction is keyword-only. PR #544 is merged, closing #542. After
merging latest main ``8ab4a0df7``, its clean candidate ``a23978e3c`` passes
all 470 tests in the seven-file CP gate. No pipeline timing gain is claimed
for this lane.

``PatternGroupData`` now specializes ``PatternGroupExecutionScope`` and owns
one complete loaded cohort. ``FunctionRuntimeScope`` and its execution bridge
are deleted. ``FunctionCoreExecutor`` consumes the cohort directly; the two
adapter factories and the artifact-input forwarding helper are removed.
Image composition moves to the existing ``ImagePayloadStackComposition`` owner.
Initial source coordinates and plane count remain captured at their original
load boundary; mutable plan selectors remain live, and later image/memory
progression remains separate from that initial cohort. Frozen slots, transport
serialization, first errors, debug events and alias/mutation controls pass.
The exact migration has 844 wholly passing tests. An additional consumer shard
has 167 passes and three dynamic producer-record failures reproduced unchanged
with the three original production modules. Those failures remain open consumer
work, not waived tests. The bounded NRA census changes from 164 to 163 classes.
No pipeline timing gain is claimed; this is part of a larger semantic batch.

The next coherent batch removes four producer/stream representations:
``FunctionStepOutputProducerIdentityRequest``,
``FunctionStepOutputProducerIdentityAuthority``, ``ProducedMemoryPathsAuthority``
and ``StreamOutputProjectionRequest``. ``CompiledStepPlan`` derives producer
identity from the original main-flow/artifact declaration; ``ProducedOutputSemantics``
derives memory paths and current source metadata; ``StepOutputManifestStore``
selects current image cohorts. Save, materialization, viewer validation,
publication and all three preset consumers migrate together. ``StreamOutputBatch``
owns admission and projection. Correlated one-pass grouping replaces a complete
record scan for each producer projection, preserving first-seen group order,
within-group order, frozen input-list structure and original projector errors.
Actual writer reloads and persisted-format decisions retain their original epochs.
The producer/source gate passes 112 tests, stream/output gate 70 and
artifact/viewer gate 79. Three stale CP fixtures now declare their producer-owned
locations; all 248 related tests pass, including missing/wrong-location rejection.
The production input-selection law is unchanged.

The same batch removes ``AlignedImageStackKwargResolutionStrategy`` and its
seven concrete leaves. Their operation now belongs to the existing
``RuntimeSliceProjectionStrategy`` family. Ordinary projection and argument
alignment remain distinct operations: tuple recursion versus list passthrough,
whole image spatial alignment, label projection before spatial alignment, and
nested outer-stack selection keep their original laws. Operation participation
and nominal members derive from existing declarations and method ownership,
with one shared MRO ordering algorithm and cached type selection. Narrower child
declarations and dynamic extensions are covered by the 517-test family/CP gate.
External extensions must use the existing projection family; equal-distance
virtual-ABC ties follow its stable registration order. The separate registry's
independent tie order and removed APIs have no compatibility aliases.
A genuine old aligned-value bug also closes: the removed strategy called a
nonexistent ``projection_axis.aligned_value``. The merged leaf invokes the
existing value owner's ``value_for_aligned_slice`` capability, with exact outer
count/index controls. Original ``AttributeError`` evidence is retained.

The final combined 22-file execution, projection, image topology, save,
publication, artifact, debug, framework, path and CP gate passes all 1,247 tests
in 18.97 seconds. This validates the structural batch together. No new ordinary
pipeline timing has yet been measured for this revision. An isolated main
cherry-pick of the loaded-cohort change was rejected because it depends on the
earlier executor/output consolidation; that temporary operation was aborted,
its conflict evidence retained, and the empty branch removed. The coherent
implementation remains in the formally linked draft PR #394.

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

Fresh paired evidence at ``c59eaa55f`` is retained under
``benchmark/results/perf_invocation_owner_paired_20261003``. All eight strict
scientific comparisons pass. Mean 3D execution is 9.021577s versus native
14.793260s (1.640x); Speckles is 1.554196s versus 1.964025s (1.264x).
Two observations have substantial spread and do not establish a causal gain.
This source precedes the output-record specialization. Its remaining execution
gap to 2x is 1.624947s for 3D and 0.572183s for Speckles.

PR #394 remains draft. Its original whole-branch R0/R1 obligations, installed
consumer acceptance, full-catalog parity and fresh full30/scaling figures
remain open. Startup and required library/kernel preparation remain outside
pipeline clocks. The performance goal remains active.
