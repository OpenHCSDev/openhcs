Runtime plumbing frontier: current measurements and rejected routes
=================================================================

This checkpoint supports PR #394 and issue #496. It records measurements and
remaining investigation, not a new production optimization. Main #498 was
normally merged and pushed at ``093c2f42d1235b5e218800f57937b6a52b4f5255``.
That transition changed documentation only; production sources remain identical
to the earlier native-qualified integrated source.

Timing boundaries
-----------------

Every run uses the original public benchmark driver, one worker and one CPU
thread, default OUTCOMES completion and the ordinary memory observer. Mandatory
registry/library/kernel preparation completes before server READY. Server
startup, preparation and shutdown are outside pipeline clocks. Execution excludes
compilation; total includes compilation and completion. Single-worker execution
is inline. The retained native invocation clock excludes import/JVM/pipeline
loading and includes prepare, modules, post-run and closure.

Diagnostic nested exclusive clocks partition their original execution root.
They include observer overhead and required work. A callable boundary includes
its filtering, conversion and metadata behavior; it is not a pure-kernel clock.
Inclusive descendants cannot be added to their ancestor. Correct output bytes
do not establish performance improvement, input immutability or callback purity.

Fresh ordinary Speckles
-----------------------

Two independent uninstrumented invocations on the current source produced
execution times of 1.199828148s and 1.159908533s. Their means are:

* Execution: 1.179868340s.
* Compilation: 1.067295671s.
* Total: 2.514483608s.

Both complete five-file inventories, including all three scientific CSVs,
are byte identical to the qualified baseline. Physical images, pipeline,
configuration, server environment, dependencies and native evidence are joined
to the original receipts. Compared descriptively with the retained native
invocation mean of 1.915068373s, execution is 1.6231x faster and total is 0.7616x
as fast. The execution gap to 2x is 0.222334154s. Native was not rerun for this
checkpoint; two observations do not establish statistical significance or a
causal source improvement.

The earlier and current pipelines both invoke IdentifyPrimaryObjects twice.
Their relevant source bodies and settings are identical. The prior slower
timing therefore has no established code-change explanation. The current
ordinary progress spans put about 0.820924s in those two steps, approximately
70 percent of execution.

Actual declumping inputs and boolean output oracles were separately captured
under unchanged storage limits. The original two stage bodies took 0.070122s
and 0.001791s, totaling 0.071913s. Capture overhead was excluded from these
stage clocks. Even eliminating that stage cannot bridge the measured gap, so
the seed optimization route is stopped before a candidate or replay is built.
The original diagnostic wrapper import failure is retained separately; the
successful harness passed controls for all five actual installed hooks.

Current 3D plumbing
-------------------

An unchanged 24-boundary diagnostic on the current source completed with both
profilers disabled. Its execution root is 8.958889063s, partitioned into
4.163085915s at 211 callable boundaries and 4.795803148s outside them. The latter
is approximately 53.5 percent of execution. Selected disjoint exclusive terms:

* Stack loading: 0.965303496s across 32 calls.
* Output saving: 0.608366542s across 28 calls.
* Worker-lane residual: 0.619469857s.
* Image-request construction: 0.390939402s across 30 calls.
* Module-output recording: 0.413856133s across 26 calls.
* Metadata publication: 0.493661132s across five calls.
* Artifact metadata reconciliation: 0.288939269s.
* Validation and unstacking: 0.189130950s across 28 calls.

There are zero feature-query calls. The complete six-CSV/120-TIFF scientific
bytes match the qualified ordinary baseline, all 128 inventory paths match,
and three physical input volumes, the pipeline and retained native logical
volume/plane witnesses are verified. Only the managed metadata JSON differs,
with both hashes explicitly reported. This is a diagnostic breakdown, not an
accepted ordinary runtime gain.

The prior ordinary 3D execution of 8.536s versus native 14.396s leaves roughly
1.34s to reach 2x execution. Publication and reconciliation together have only
a 0.7826s diagnostic ceiling before mandatory work. A publication-only change
is therefore insufficient. The investigation must span shared producer/source
derivation across loading, image requests, recording, saving and publication.
The existing nominal authorities are the intended owners; no extra mirror,
global cache, per-function shortcut or delayed per-step visibility is admitted.

Measurement frontier and architectural constraints
--------------------------------------------------

The separate 42-boundary Beginner diagnostic measures a disjoint table
assembly/query/pivot envelope of 1.462782s. Native CSV rendering is another
0.163899s. All nine scientific output files and complete physical inventory
match the native-qualified baseline. Its occurrence graph reaches the original
4,096-event limit and remains RED independently of scientific correctness.
The complete Speckles graph demonstrates repeated access to one table and
object-label vector, but that entire measurement lane is only about 0.038s.
Neither query-only nor the 16-call intensity projection route can close the
dominant gaps, and the measurement fold is not a 3D optimization: that workload
does not perform these queries.

Existing serialization views have distinct semantics. Raw projection source
metadata and enriched SOURCE_METADATA cannot share one output dictionary.
The transaction overlays raw path records before decoding surviving entries;
decoding overwritten malformed entries earlier would change first errors.
Serializer callbacks, independently mutable outputs, current per-step
publication visibility and concurrent-axis final pruning remain obligations.
A frozen projection declaration does not establish deep immutability of its
image metadata. Ownership proposals remain provisional until those laws and
representative replay show a sufficient end-to-end payoff.

Retained evidence
-----------------

The following local receipts contain exact source/controller/environment/input
pins, original commands, file inventories and hashes:

* ``/var/tmp/openhcs-current-speckles-ordinary-pair-v1-20261003/observations.json``:
  SHA-256 ``d08f35061285e8a4d543377c1de7993623654844eddcaea806d269672a0bf4a1``.
* ``/var/tmp/openhcs-speckles-seed-capture-v4-scientific-byte-gate-20261003.json``:
  SHA-256 ``4da188db100b9526f18a6a02ce98872dad6e7ee5dca60c1b85e7052e1287e301``.
* ``/var/tmp/openhcs-current-3d-runtime-ledger-v1-scientific-byte-gate-20261003.json``:
  SHA-256 ``36a4f2cdcc14baaa38f027a6dc759facd1229cc1f5960ddb063cbe689efda0cf``.
* ``/var/tmp/openhcs-measurement-occurrence-ledger-v1-scientific-byte-gate-v2-20261003.json``:
  SHA-256 ``4352fa24e8984e0f4c67587ae674ff28085ed134531dea28fe7d5b8517671f99``.

PR #394 remains draft. Whole-branch original R0 and the #479 per-file R1
failures remain explicit and unwaived; installed consumer acceptance,
full-catalog/scaling measurements and fresh figures remain unfinished.
The performance goal remains active.

Deeper current 3D attribution and producer ownership
---------------------------------------------------

Two further diagnostics use clean source ``396379b06769a3f5afe92413b7d9d6a21dd3f66f``.
Its production, test and benchmark driver bytes are unchanged from the preceding
``093c2f42`` source. Both preserve mandatory READY warmup, inline 1w_1t execution,
OUTCOMES export, the normal memory observer and both disabled profilers. Neither
is a new ordinary performance comparison.

The 36-hook run separates metadata normalization and provenance operations from
their actual nested callers. It observes 29,701 normalization calls outside raw
callable boundaries, totaling 0.317682s exclusive. Ordinary normalization creates
a fresh scalar identity and reuses the cached plane collection; it does not copy
the complete 60-plane lineage. Whole-plane merges and derived naming do rebuild
plane/contributor snapshots. Those operations retain live-mutation and fresh
snapshot obligations. Their observed costs do not admit a standalone fix large
enough to close the 1.338s qualified execution gap.

Several large isolated stalls prompted a separate 25-hook run with passive GC
callbacks. It does not disable GC, freeze objects, change thresholds, force a
collection or replace existing callbacks. Startup has no active pipeline root.
Its execution root is 8.462928s: 3.803686s within the 211 declared callable
boundaries and 4.659242s outside them. The public diagnostic clocks are execution
8.490154s, compilation 1.824986s and total 11.210223s. GC consumes 0.285505s,
including one 0.196025s generation-two collection during saving. Collection
durations overlap the owner clocks; adding them to plumbing would double count.
GC alone cannot explain or close the remaining gap, so a GC-policy optimization
is rejected. Different diagnostic clocks on identical production bytes are not
evidence of a production gain or regression.

Both diagnostics match all six CSVs and 120 TIFFs byte for byte against the same
native-qualified baseline, with complete 128-file inventories and physical
input joins. No fresh native repetition is claimed. The 36-hook scientific
output is retained in a lossless, individually hash-verified archive at
``/var/tmp/openhcs-current-3d-owner-ledger-v2-20261003/scientific-output.tar.gz``;
its custody receipt records every original path, mode, size and hash. Later
readers must use or restore that archive rather than assume those extracted
files remain present. The 25-hook output uses the same verified custody protocol
at ``/var/tmp/openhcs-current-3d-gc-ledger-v1-20261003/scientific-output.tar.gz``.
Previous baselines and frozen failures are unchanged.

Source and consumer audits reject two tempting shortcuts. Artifact-only groups
already return ``NoMainFlowOutput`` and skip unstacking and saving. Canonical CP
publication already reuses the stored runtime artifact payload. Downstream CP
inputs deliberately distinguish stored secondary artifacts from relation-owned
current main flow. The latter has an independent mutable whole buffer and final
filename/source-component context. Repeated cache hits share that buffer. A
direct stored-artifact substitution would change these relationships and, in a
saved determining case, 62 metadata facts. The final named output bundle can
also retain earlier sibling outputs, so the last canonical return roster cannot
stand in for the complete main-flow cohort.

The remaining structural route belongs to existing ``PatternGroupOutputData``,
``AlignedImageStack``, manifest and runtime-input owners: derive physical plane
views and final context from the exact correlated producer occurrence, preserving
the independent main-flow buffer, rather than repeatedly project and recompose
the whole cohort. The seven marked load/request/record/unstack/save/publication/
reconciliation spans total 3.432617s in the GC diagnostic. This is an upper
envelope containing mandatory work, not a claimed removable cost. Before a
candidate, representative replay must retain the stored occurrence, actual
merged bundle, projected leaves, final records and cache, filename/path prestates,
and next consumer edge in one graph. No fake processing context, new cache,
canonical-roster shortcut or zero-copy assumption is admitted.

Additional retained receipts:

* ``/var/tmp/openhcs-current-3d-owner-ledger-v2-scientific-byte-gate-20261003.json``:
  SHA-256 ``df4f6548f4459c6a55ea5dc182ac52a5472eaacace572ae60740a9409377ca89``.
* ``/var/tmp/openhcs-current-3d-gc-ledger-v1-scientific-byte-gate-20261003.json``:
  SHA-256 ``d0b8d6af1b8a1777b03624cf6435d67b04746e9477a5cefbc7a962feaa2d667d``.
* ``/var/tmp/openhcs-current3d-canonical-mainflow-CP-owner-review-v1-20261003.json``:
  SHA-256 ``9c264eaa2a735388f5694a305dcbf8ff61258ed959adb4819ffacfcb39235bbf``.
* ``/var/tmp/openhcs-current3d-canonical-mainflow-macro-owner-audit-v4-20261003.json``:
  SHA-256 ``c589df6f3c28d6d3a3dc668adc696089bc4aeb68aa2d762a0128592e8d67b891``.

This checkpoint changes documentation only. No optimization, merge, original
R0/R1 waiver, installed acceptance or full-catalog/scaling completion is claimed.

Current producer/consumer evidence and compilation frontier
----------------------------------------------------------

Fresh diagnostics at ``bb9c49c2ad70f1cee49fa0cde47592681edb2be3`` preserve
main ``87d9a99a9``, shared dependency/native/input pins, normal READY warmup,
inline 1w_1t execution, OUTCOMES completion and the normal memory observer.
Their observation clocks are not ordinary performance improvements.

The bounded V7 capture retains four actual step-13 ImageMath producer and
step-14 Resize load states, totaling 856,419,294 bytes under the unchanged
384 MiB per-item and 1 GiB total limits. Its full six-CSV/120-TIFF parity,
complete scientific inventory, all 180 ordered physical source references,
and three native input-volume witnesses pass. Original step-13 replay matches
all 60 records, named/VFS/cache outputs and the complete 123-array identity,
sharing, dtype, stride and writeability graph.

Original step-14 replay is RED before cache lookup: the actual producer
manifest lives in module ``_STEP_OUTPUT_MANIFESTS``, a WeakKeyDictionary outside
ProcessingContext transport. Reconstructing it from the separate producer
oracle would fabricate a receiver state and is rejected. Independently,
RuntimeSourceBindingContextCache deliberately drops four derived caches through
its reducer. The actual after-load graph proves the result is the retained
whole image for its exact 60-path cache key, but cold restored clocks cannot
represent warm pipeline work. A future replay must carry actual manifest/cache
owners in the same graph and rekey identity indexes only from real owner
references, or obtain live production confirmation. Original failed artifacts
remain preserved; schema completeness is not complete transaction state.

A six-group ephemeral layout experiment validates the proposed existing-class
projection ancestor layout, constructor signatures, default factories, frozen
assignment, cooperative projection order, errors and fresh public provenance.
This proves layout feasibility only. Lazy read algorithms, custom subclass
behavior, combined transaction acceptance and sufficient elapsed savings
remain unproved. No new wrapper or cache authority is implemented.

Illumination remains the weakest known total comparison. Its current V3
diagnostic records compilation 1.125192s, execution job 0.377852s and total
1.844212s, with both authored NPY files, full inventory and actual physical
TIFF/pipeline/native witnesses matching the retained qualified reference.
The compilation partition places 0.302983s exclusive in dataclass analysis
and 0.285258s in nested documentation extraction: 0.588241s together. Four
client pipeline renders plus three config renders take 0.235231s. The joint
0.823472s envelope contains required work; it is not a saving estimate.
Ten effective-config getters include the schema/state subtree and cannot be
added to it. Completion alone is too small to close the remaining gap.

The separate V4 diagnostic also passes full science and distinguishes actual
cache topology: compilation has 40 successful first-use misses and 338 hits
across 44 class identities; execution has 94 hits. There are no uncached empty
results. This rejects repeated failing analysis or fresh proxy churn as the
mechanism. Exact runtime class names were not retained because the diagnostic
read a type-owned attribute from the class dictionary; that metadata omission
is explicit. A separate declaration inspection finds 22 registered public/proxy
pairs and 95 differing fields, including Optional annotations and None defaults.
Canonical-class ParameterInfo substitution would change real reset and
reconstruction consumers, so it is rejected. The remaining candidate must
separate reusable declaration work from correctly timed value/default-factory
evaluation using the existing schema and preparation owners.

Local source-qualified receipts:

* ``/home/ts/.local/state/openhcs-maintenance/20261003/current-cohort-capture-v7-science-verification-v2.json``
  (SHA-256 ``99f2f830861eb1ecd1492c50ff6bbb2a66172674211e0a925f9f6a85359a1be0``).
* ``/home/ts/.local/state/openhcs-maintenance/20261003/current-cohort-v7-original-replay-v3.json``.
* ``/home/ts/.local/state/openhcs-maintenance/20261003/current-cohort-v7-load-owned-role-review.json``
  (SHA-256 ``bd08002bbb535911ba189b1b97bf8cbceb03c938b89c5ec8d0c061e4743735a7``).
* ``/home/ts/.local/state/openhcs-maintenance/20261003/projection_ancestor_feasibility_bb9c_v3.json``
  (SHA-256 ``b5ff353e33c70d4066de5315c0bef2046e1e8680056125404a7c393eb2e531ae``).
* ``/home/ts/.local/state/openhcs-maintenance/20261003/illumination-compiler-ledger-v3-science.json``
  (SHA-256 ``e042e25aa0fd9e087459c77613150f0db6447e91d0fc943acf2ea638312cc850``).
* ``/home/ts/.local/state/openhcs-maintenance/20261003/illumination-schema-cache-topology-v4-20261003.json``
  (SHA-256 ``134244ea39004ccfc86d20fa14d4fdc49e78aa72f4a92349092c6f420c1b89e3``).

The preceding V3/V4 diagnostics are attribution only. They do not establish a
production saving, new native repetition, original R0/R1 waiver or
full-catalog/scaling completion.

Registered configuration source readiness
-----------------------------------------

The decisive source-only prototype found repeated Python 3.10--3.12 class
source lookup walking the complete config module. The existing
``SignatureAnalyzer`` now derives bounded module AST and qualified-class source
views from current immutable source contents. Python 3.13 and newer retain the
native locator. Live annotations, factories, mutable field/inherited docs,
loader invalidation and the original completed value-analysis cache remain at
their existing observation points. Earlier class-identity snapshots failed
real mutation controls and were rejected.

``LazyDataclassFactory.registered_type_pairs()`` projects the existing registry
without a second roster or constructing values. ``RegistryService`` prepares
both public and proxy declarations after callable hooks and before READY,
including declarations registered after the catalog was cached. Default
factories are not evaluated during source preparation.

At OpenHCS ``7258826d7198f2bb7010763276dba02320d62142``, four ordinary public
Illumination runs in ABBA order measured:

.. list-table:: Ordinary 1w_1t mean seconds; two observations per variant
   :header-rows: 1

   * - Phase
     - Prior source
     - Prepared source
   * - Compilation
     - 0.962152
     - 0.587605
   * - Execution job
     - 0.382655
     - 0.400589
   * - Total pipeline
     - 1.693765
     - 1.363694

Compilation saves 0.374547s (38.9%); total saves 0.330070s (19.5%). No execution
gain is claimed. All four runs use CPU5, INLINE one-worker execution, normal
OUTCOMES and the default memory observer, without hooks or profilers. Mandatory
server startup/preparation and shutdown are outside total pipeline timing.
Exactly three owned source files vary; immutable before/after hashes identify
actual baseline contents separately from containing dependency Git HEADs.
All source, dependencies, native binaries, environment and physical inputs were
checked before/after each run; the clean candidate was restored afterward.

All four complete authored output inventories retain both NPY artifacts exactly
and match the qualified physical TIFF/pipeline/native evidence. The workload
authors no tables. Native CellProfiler was not rerun in this experiment; broad
scaling or new native speedup claims are not made. Science receipt SHA-256:
``918c36612ec20738ad2d2760da85c9e9be07e81d4cd4bf0f60ec91dfcf906488``.

The 136 upstream, 25 existing lazy-factory and 119 OpenHCS readiness/catalog/
startup tests pass. python-introspect PR #6 and ObjectState PR #9 are merged and
formally close their issues #5 and #8. Their merge commits change no measured
source bytes. OpenHCS wiring is pushed in draft #394; a small main-only readiness
change can be isolated without merging the unresolved broad branch.
The reviewable measurement receipt and immutable recipe links/hashes are under
``benchmark/results/perf_schema_source_readiness_20261003``. Redundant tracked
local recipe copies were removed; the originals, source variants and immutable
outputs/freeze remain under the corresponding maintenance ABBA directory.
Those recipes depend on local paths and are not turnkey portable commands.
Runtime plumbing, full-catalog/scaling measurements, fresh native repetitions
and figures remain outstanding. Original whole-branch R0/R1 failures remain
explicit and unwaived.

Canonical provenance identity integration
------------------------------------------

Main readiness #514 is merged into this branch. The overlapping readiness
regression was removed from the callable ABI suite; the dedicated main test
remains authoritative. Callable canonical-signature preparation still precedes
registered declaration preparation and kernel readiness.

The existing ``SourceMetadataFields.provenance_identity_items`` now derives its
representation from ``identity_items``. Equal nested field mappings have equal
provenance fingerprints independent of insertion order. Raw wire order, real
value differences, ordered planes and lifetime-selected views remain intact.
Existing birth fingerprints are preserved by pickle/cloudpickle; they are not
recomputed from subsequently mutated public fields. Historical nested-mapping
fingerprints can therefore differ from newly canonical fingerprints. A fresh
same-source capture is required before candidate fingerprint replay.

The integrated metadata/transport/readiness controls pass 86 tests in 2.40s.
The separate exact PR #494 source qualification passes its unchanged 31 writer
controls plus seven identity controls. Those writer controls cannot collect on
this branch because its independent ``PointROIOutput`` producer is absent; no
installed, native or live viewer acceptance is inferred. The integrated receipt
is ``~/.local/state/openhcs-maintenance/20261003/pr494-identity-owner-scratch/
integrated-owned-qualification-v1.json``.

V8's original producer and downstream loader replay now pass complete value,
metadata, manifest and array-alias gates, and the full six-CSV/120-TIFF science
gate passes. Serialization still drops nested metadata views and source-context
derived caches. These scoped clocks are not complete production-warm performance
evidence. The saved downstream cache hit constructs no new provenance objects;
it does not establish the payoff of a broader loading/recording/publication fix.
The next capture must retain actual nested caches in the same graph, under the
existing admission bounds, without rewarming or inventing state.
