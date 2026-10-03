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
