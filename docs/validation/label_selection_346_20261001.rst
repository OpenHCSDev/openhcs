Exact labelled maxima through shared quicksort partitions (#346)
================================================================

When a CellProfiler-compatible label query needs only maximum positions, sorting
all pixels spends time ordering positions that cannot win. ImagingFlow's 17 real
queries spent about 0.97s in this path. Retaining every possible winning tie and
sorting only partitions containing those positions removes that work while
preserving the original unstable NumPy 1.24 / SciPy 1.9 position choices.

Source checkpoint and integration
---------------------------------

Production source is ``e476974886d65cd62ea6115b5bec94cf2710a8ca``, integrated with
main ``05c3cf2883fb2ce75c14961264dabad633e639ee`` and its exact recorded dependency
pins. This includes the completed parity fixes in PR331/326/341 and the ImageXpress
inventory migration in PR338. No dependencies or reference tolerances change.
The source edits are in the shared label-geometry kernel and nominal shape
backend; documentation after this checkpoint does not change production code.

Outcome and ownership decision
-------------------------------

The representative target is the slowest ordinary Official30 pipeline,
ImagingFlow: roughly 15s execution and 17s total at one well/thread. Granularity
is still the largest module cost. Exact radix and coarse-priority reconstruction
prototypes were rejected on real inputs: the first radix input became twice as
slow, and coarse ordering regressed the third input. This retained route instead
has a measured approximately 0.66s maximum practical payoff across real selection
queries and transfers to every consumer of the shared labelled-maximum backend.
It is one incremental reduction, not completion of the subsecond execution goal.

The bounded source corpus is the original OpenHCS production ClassDef corpus
plus recorded dependency context. Existing authorities are
``ShapeMeasurementBackendStrategy``, ``NumbaShapeMeasurementMixin``, its nominal
NumPy implementations, and the shared exact indirect-ordering math kernel.
Intensity/radial geometry consumers already invoke that public backend operation;
other geometry/intensity operations still consume the full-order query.

Required production relations, licensed by the existing exact CellProfiler tie
contract and the user's shared-layer/readiness requirements:

* Both full ordering and ordered selection consume one
  ``_numpy124_partition_indices_numba`` implementation. The old private
  quicksort implementation is migrated rather than copied or forwarded.
* The labelled-maximum consumer retains all possible requested maxima, including
  ties, and derives its coordinates from their original relative order. Skipped
  partitions contain no retained positions and cannot change that relative order.
* Existing backend preparation invokes both full and selected queries for float32
  and float64 with writable/read-only label IDs. The existing registry/backend
  preparation chain owns readiness before pipeline clocks.

Forbidden relations are another sort implementation, per-module selection
workarounds, a handwritten transport preparation roster, execution-time JIT, or
replacement of the legacy tie contract with first-pixel maxima. The optional
boolean retention vector is query data within the common numeric mechanism, not
a new behavior family, case registry, or source of independently writable policy.
Original pivot swaps, partition scheduling/depth, insertion ordering and heap
fallback remain shared. Full-order callers pass no retention vector. Nonfinite
NaN queries retain the complete domain to preserve the existing comparator;
finite and infinite maxima retain every equal winner. Masks, absent/invalid IDs,
multidimensional requested IDs and original coordinate domains are preserved.

Architecture gates
------------------

* Original R0 passes all three roots with no positive metric deltas. An initial
  long boolean chain was corrected; its failed receipt remains counterevidence.
* Original NRA R1 passes its two configured detectors with recorded dependency
  sources in context and no increases. The unchanged shape-module record finding
  remains visible. This is not all-detector cleanliness or a theorem of numerical
  equivalence; the algorithm edit is authored.
* Before/after original syntax census at synchronized main/candidate: 702 modules,
  5,144 original ClassDefs, 5,132 projected, all 12 unprojected OPEN retained.
  There are no class additions/removals in this patch. The earlier 7b census
  remains historical; PR338 introduced its own three declarations on main.

Behavior and native parity
--------------------------

1,905 tests and 42 subtests pass on the final production checkpoint; one optional
Napari skip and two unchanged watershed warnings. Frozen legacy permutations and
coordinate goldens cover ties, masks, NaNs/infinities, missing/invalid labels and
both inherited backends. A readiness control rejects any unprepared dispatcher
signature after backend preparation, including read-only label IDs.

Full Official30 native-reference qualification passes 30/30, every difference count zero. Existing 1e-6 absolute/relative numeric tolerances and exact identity/discrete and declared-image checks remain unchanged. Native reference clocks are not used for performance claims.

Saved-input replay
------------------

All 17 saved real queries exactly reproduce the originally captured coordinates.
The production main replay totals 0.968238s; production candidate totals 0.310339s
(sum of per-input five-sample medians, warmed kernels). This is a microreplay,
not a pipeline clock. Source-authenticated recipes and per-input checksums are
included. The 327MB compressed source inputs remain in the benchmark workspace
under ``perf-main0c-labelled-select-inputs-20261001``. Included capture recipes
show their origin from the actual public benchmark; do not fabricate a simplified
array and present it as this real-input frontier.

Ordinary matched pipeline timing
-------------------------------

Fresh main/candidate/candidate/main production public-route observations, CPU5,
one well and one numerical thread, current pins, standard memory observer and
shared persistent Numba cache. Each observation starts with a ready registry and
kernels; pipeline clocks exclude server startup and shutdown. No tests, builds,
audits, microreplays or other timed benchmark jobs overlap these clocks.

.. list-table:: ImagingFlow seconds
   :header-rows: 1

   * - Variant
     - Compile
     - Execution
     - Total
   * - Main A0
     - 1.966862
     - 14.910172
     - 17.593219
   * - Candidate B1
     - 1.551474
     - 14.394530
     - 16.680293
   * - Candidate B2
     - 2.003625
     - 14.115476
     - 16.792311
   * - Main A3
     - 1.510475
     - 14.929483
     - 17.100487

Means: execution 14.919827 -> 14.255003 (-0.664824s, 4.46%); total
17.346853 -> 16.736302 (-0.610551s, 3.52%). These are two observations per
variant, not a universal speedup claim. Compilation means are 1.738669/1.777549;
no compilation improvement is claimed. Every full 11,535,809-byte measurement CSV
has SHA256 ``517057a4b018195cc4c57e8503be63a378a8306eb2ecc303d4a025b6eab6dd1c``.

A separate production readiness/worker-clock diagnostic succeeds with zero
Numba dispatcher compilation calls after readiness. It changes observation hooks
only, not the math path, and is not pooled into the uninstrumented timing cohort.
Earlier scratch injection cohorts remain counterevidence: the first ordinary
candidate was slower (15.665s); the later diagnostic matched cohort improved
worker CPU by 0.832s. Neither scratch cohort is relabeled as production timing,
and isolated ABI replay did not verify late JIT as the early outlier's cause.

Evidence and remaining work
---------------------------

``label_selection_346_evidence_20261001.tgz`` contains source/pin receipts, original
guards/census, tests/XML, replay and capture recipes, per-input checksums, ordinary
observations/controllers and separate readiness trace. Native qualification
records are included when its final gate completes. ``SHA256SUMS`` authenticates
included files. Large real inputs and scientific exports remain in the local
benchmark workspace; the archived recipes name their required locations.

Full native-reference qualification uses retained scientific reference outputs;
it is not a fresh CellProfiler timing/scaling experiment. Fresh native scaling
and figures, granularity and generic export cost remain in continuing issue162.
The matched gain closes issue346's bounded acceptance, not the overall latency
objective. No golden/tolerance assertions are weakened to obtain performance.
