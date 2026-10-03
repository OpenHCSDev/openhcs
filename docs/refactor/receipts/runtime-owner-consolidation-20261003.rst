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

The combined 22-file execution, projection, image topology, save,
publication, artifact, debug, framework, path and CP gate passes all 1,247 tests
in 18.97 seconds. This validates the structural batch together. The subsequent
paired measurement below does not establish a material speedup. An isolated main
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

Typed publication and input source resolution
--------------------------------------------

Produced output projections now stay typed through the atomic publication
transaction. The existing ``VirtualWorkspaceSourceProjectionEntries`` admits
incoming projection/path pairs, merges them with the current durable document,
and supplies serialization at the disk boundary. Producer ``metadata_dict``
construction and the atomic writer's raw-field merge are deleted. Incoming
projections are not decoded; unreplaced durable records are decoded once.
The shared owner retains duplicate-identity admission, replacement repair,
path order, concurrent-well retention and final reconciliation pruning.
Metadata-disabled transactions retain opaque existing wire annotations and
orphan mapping entries. The internal incoming API intentionally requires typed
entries; persisted JSON remains the external format.

Input source-context queries now consume the value already bound and projected
by ``RuntimeInputBindingRequest``. They no longer repeat image aliasing,
intensity normalization or object-label binding. Each post-call source read
still resolves the current input, including callback mutations.

One output identity owner
-------------------------

``FunctionOutputIdentity`` now owns construction, component and extension
normalization, qualifiers, filenames and paths. ``ProducedOutputSemantics``
inherits these operations. The five detached identity/path/component/extension/
qualifier facades are deleted and their production consumers migrated.
Semantic coordinates remain distinct from storage filename coordinates;
the external parser and execution-local caches retain their own roles.

The unused five-class ``core.progress.emitters`` family and its public
reexports are deleted. Actual emission still uses the required progress queue,
the execution server's emitter, and the GUI's event registry.

The publication, source-binding, identity and progress changes pass one coupled
22-file gate covering execution, recording, masks, live mutations, materialization,
persisted reopening, projection and progress (971 controls, 10.92s). This is a
behavioral check of the combined source, not evidence of speedup.

The proposed metadata-only input lane was withdrawn before publication. A real
compile-only inventory admitted seven 3D groups and no Speckles groups; existing
cache hits already avoid assembly. The proposed broader lazy composition was
also rejected: eliminating source snapshots changes in-place callable isolation,
while preserving them retains the copying cost. Neither route is promoted as
an unconsumed capability or a dominant performance fix.

Canonical producer transport and measurement rosters
---------------------------------------------------

An input edge now retains its exact producer storage independently of its
semantic primary-image projection. The redundant ``consumes_main_flow`` flag
is removed. Artifact-owned execution admits an independent pixel/mask buffer
directly from those producers instead of unstacking, saving, discovering and
reloading an unnamed checkpoint. ``CompiledStepPlan`` derives checkpoint demand
from actual consumers and propagates that demand through preserved main flow.
Path-based conversion, sequential filters, implicit raw inputs and unavailable
same-step producers retain their required transport.

``RuntimeArtifactInput`` owns producer selection and candidate coordinates;
runtime scope joins retain whole correlated rows and permit compatible partial
contexts. Original filename metadata does not replace producer coordinates.
The existing artifact type owns image-context extraction, and the existing
stack composition owns independent buffer admission. No address or data cache
is introduced.

The importer preserves a native measurement module's full image/object roster.
The existing measurement executor owns its Cartesian measurement traversal and
batch kernels. NATURAL object measurements resolve that roster once, without
building an unused composed image request; COMPOSED and selected-plane source
identity retain their declared behavior.

Explicit roster compilation belongs to the adapter and declaration owners,
while raw scalar argument multiplicity remains on the raw binder. Omitted
object selection still fails when more than one subject is available. Recorded
measurement payload owners validate named subject multiplicity after the common
row scope/id-field checks.

Invocation selection now also owns the source-origin view: represented inputs
retain the current payload epoch, and unrepresented explicit original images
resolve through their exact matched source binding. The separate source-input
selection pass is removed. An absent stored primary cannot be replaced by its
producer's older value. Exact producer-group selection is distinct from
additional image-set fixed coordinates; discovery retains actual produced
coordinates, while site, time, Z and genuinely fixed-channel constraints remain.
Physical publication loads original memory addresses and writes manifest-owned
destinations under the current output root; preserved outputs no longer write
back into the input plate.

Current runtime and transport boundaries
----------------------------------------

Commit ``9d79c4289`` repairs the declared runtime/transport ownership boundary
(#558). Objectstate serialization resolution returns ordinary processing
contexts unchanged; the two bundle maps therefore previously shared plans,
and transport normalization rewrote the prepared runtime graph. The existing
bundle now derives separate transport context/plan snapshots. Inline, fork and
thread resources consume rich contexts directly; queued process workers and
public serialization consume transport snapshots. Stores, pixels, configuration
and service lifetimes retain their existing sharing. This is not a claim that
all compiled plans have been sealed. Actual warmed callable identity and pickle
roundtrip controls pass. Commit ``65a76d7e9`` also strips process-local hooks
from the compiled contract metadata on its transport view, preserving the
rich contract identity; both callable-reference and contract fields are
covered by the same real pickle control.

Commit ``ad4670f20`` folds producer path admission into
``ProducedPathRecordIndex``. ``ProducedPathSet``, ``ProducedPathPatternSelector``
and the detached producer-pattern path cache are removed. A loader resolves one
current record cohort and derives its paths, retaining cardinality admission
after source-context construction and before cache/pixel access. Source-only
and pipeline-start requests do not acquire producer records.

The same batch puts source transformations on ``NamedSourceBinding`` and deletes
``source_image_semantics.py``. The physical metadata context retains header,
calibration and crop geometry; a binding's already-resolved channel axis remains
authoritative after missing-context merge, including declared grayscale absence.
Mutable scalar provenance remains independent. One coupled source, producer,
calibration and original measurement journey gate passes 236 controls. This
later source is not included in the paired performance evidence below; no
additional speedup is claimed before its scientific comparison.

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

The subsequent ordinary paired run at ``74693f589`` measures mean 3D execution
8.841s, total 10.823s and native warm invocation 15.230s: 1.723x execution and
1.407x total. Speckles measures execution 1.415s, total 2.216s and native
1.896s: 1.340x execution and 0.856x total. All eight scientific comparisons
pass. The 0.180s difference from the previous 3D execution mean lies within
the observed spread and is not a causal performance claim. The execution gap
to 2x native remains 1.227s. Local timing and qualification records are retained
under ``owner-consolidation-746-paired-v1`` and its preparation sibling in the
20261003 maintenance evidence root. The typed publication, input binding and
identity changes described above follow this measurement and remain unmeasured.

The original-pipeline campaigns under ``canonical-producer-transport-paired-v1``
and ``v2`` failed at compilation and runtime respectively; their clocks are not
qualified performance evidence. The ``v3`` campaign at ``c50a947f4`` completed
both ordinary sweeps and fresh native runs but failed strict comparison with
42 missing origMemb intensity features. Its faster timings are also unqualified.
The missing explicit source-roster edge is repaired by the invocation selector;
the corrected scientific comparison below covers both original pipelines.
All failed campaigns are retained, and no output exclusion or tolerance change
is admitted.

The corrected ``canonical-producer-transport-paired-v5`` campaign at
``102d6e491`` passes all eight strict scientific comparisons, including complete
measurement inventories and images with existing CP tolerances. Active source
aliases derive from the current payload for each invocation, preserving outputs
and mutations within a function chain. The existing artifact source-relation
family supplies the explicitly selected image-set context to object inputs;
exact producer addresses and unrelated fixed coordinates remain strict.

Means of two independent ordinary and two fresh native observations are:

* 3D: compile 1.112773s, execution 7.401238s, total 9.284819s, native invocation
  14.204229s; 1.919169x execution and 1.529834x total.
* Speckles: compile 0.677950s, execution 1.290954s, total 2.292555s, native
  invocation 1.930783s; 1.495625x execution and 0.842197x total.

These observations do not establish a causal gain or full30/scaling behavior.
Speckles still loses on total. The existing benchmark figure owner produces
fresh PNG/SVG runtime and speedup figures in the campaign's ``figures-v2``
directory (corrected target labels in ``figures-v3``). Native invocation includes its pre-first-module work; startup,
imports/JVM setup and the excluded warmup observation are outside this clock.
Ordinary total includes compilation and normal OUTCOMES/RSS completion.
The ``v4`` namespace is explicitly aborted before measurement, after independent
review found stale binding selection within a multi-function chain.

PR #394 remains draft. Its original whole-branch R0/R1 obligations, installed
consumer acceptance, full-catalog parity and fresh full30/scaling figures
remain open. Startup and required library/kernel preparation remain outside
pipeline clocks. The performance goal remains active.
