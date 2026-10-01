# Generic runtime optimization owners — issue 323

Store-bound query-cache invalidation, provider-independent object columns, and
persistent kernel preparation now derive from nominal core owners. The obsolete
provider classes, weak-global query caches, and forwarding imports are removed.
This is the user-requested ownership repair. It is not a demonstrated pipeline
speedup, and the ImagingFlow timing concern remains open for review.

The validated production source is
`eba8e5c871a84b5ddd2581d7562798223ebd2415`, normally integrated with main
`74eac059f67389ca071055c93fcbdd556ba79f1a`. Main's artifact-publication fix and
paired-field identity fix are preserved. The independent ACK fixture repair
was merged through PR 325 and closed issue 324; it is not duplicated by this PR.

| Behavior | Determining owner | Consumers |
| --- | --- | --- |
| Store mutation and derived-query lifetime | `RuntimeValueStore` | Generic measurement table lookup and CP label/vector lookups |
| Bounded value storage | `BoundedCache` | Store query domains and the existing process cache family |
| Process singleton lifetime | `ProcessLocalBoundedCache` | Existing process-local cache subclasses |
| Complete object-column domain and shared mapping iteration | Core `ObjectMeasurementColumnarRows` | Colocalization, granularity, shape, intensity, intensity distribution, Zernike |
| CPU/persistent Numba cache admission | `PersistentNumbaKernelPreparation` | Backend families and standalone registered kernels |
| Standalone kernel identity, operation derivation, parent preparation | `RegisteredNumbaKernelPreparation` | Existing CP declarations and an independent provider exercised in tests |
| Intrinsic kernels, provider requirements, fixture effects | Numerical/provider declarations | Their existing generic preparation consumers |

Store query domains have no process-singleton API. Record, replacement, clearing,
and worker-observation merge invalidate attached query values at the store's
existing mutation point. Derived caches are excluded from serialization; tests
compare transport bytes before and after a large populated derived cache and
verify retained records/revision. The old unbounded query dictionaries now use
the shared bounded LRU (default 4,096 entries); eviction recomputes values without
changing query scope. This capacity change is explicit.

The old long-row iterator was overridden by every child, whose columns are wide;
it was removed rather than moved as dead behavior. The wide forwarding class is
also removed. Typed numerical iteration remains with its leaf. The old private
abstract-class import/pickle paths are intentionally not retained; dynamic
external callers of those paths are an OPEN boundary.

The final combined native behavior checks pass **783 tests**, with one unchanged
optional Napari skip in the headless environment. Two existing watershed warnings
are retained. Coverage includes numerical consumers, actual cache mutations and
eviction, worker transport, materialization, current-main artifact publication
and paired-field identity, fork failure/cancellation, registry independence, and
once-only preparation effects. A non-CP family runs through the existing registry
consumer and remains eligible under a CP-specific capture flag.

Original CI-pinned R0 passes for all three roots: OpenHCS has 5,243 metrics with
only `StringSubscript -2`; scripts has 228 metrics and benchmark has 409, both
unchanged. Original NRA R1 against current main completes with no increased
findings. Its complete source/dependency context has 3,058 base and 3,056 candidate
projections; the policy configures two detectors. Existing mapping reads, raw
record shapes, and redundant checks remain visible in the receipt. This is not
an all-detector clean scan or a native equivalence theorem.

The original ClassDef census covers every declaration in OpenHCS and setup.py.
The final census has 701 modules, 5,123 original classes, 5,111 projected classes,
and all 12 unprojected OPEN declarations. The ownership receipts include required
and forbidden owner/consumer pairs, independent provider effects, counterevidence,
and the original OPEN rows. NRA performs declaration-selected rename, movement,
and base introduction for kernel preparation. Consumer closure and algorithm
extraction use explicitly authored, revision-checked source patches. The empty
obsolete row module is removed with an explicit emptiness assertion because NRA
has no file-deletion primitive. Native tests and production parity supply the
executed behavior evidence; syntax/preflight does not prove authored semantics.

All timed observations use the public benchmark route, one well, one native
thread, CPU 5, current shared dependency pins and persistent declared-kernel
cache. Mandatory registry/kernel readiness precedes pipeline clocks. Server
startup and shutdown are excluded. `1w_1t` selects the **inline** executor; fork
is configured for actual multiworker execution, not these single-lane observations.
No tests, audits, builds or other replays overlap the timed observations.

| Source cohort / case | Main execution | Candidate execution | Main total | Candidate total |
| --- | ---: | ---: | ---: | ---: |
| Final kernel-owner ABBA, ImagingFlow (means of two per side) | 18.201s | 17.051s | 20.689s | 19.456s |
| Final kernel-owner ABBA, 3D (means of two per side) | 8.583s | 8.300s | 11.024s | 10.760s |
| After paired-field main integration, ImagingFlow (one per side) | 15.849s | 16.566s | 18.063s | 18.740s |
| After paired-field main integration, 3D (one per side) | 8.362s | 8.316s | 10.777s | 10.753s |

Compilation in the latest pair is 1.500/1.509s for ImagingFlow and 1.656/1.683s
for 3D (main/candidate). The latest pair is source and parity qualification, not
statistical performance evidence. Earlier ImagingFlow cohorts also showed slower
candidate averages: +2.04s and +0.73s. The favorable ABBA cohort includes a slow
19.970s main observation; all observations are retained. The sign changes across
cohorts do not establish a gain or performance neutrality. The latest +0.72s
ImagingFlow concern is not dismissed.

On the latest source, all 14 complete requested CSVs and 240 persisted label
images across the four qualification outputs match exactly. The earlier ABBA
plus diagnostic comparison checks 30 complete CSVs and 480 label images.
The extended latest-source main/candidate gate also compares **every produced
TIFF**: 128 images, all series pixels, dtype, shape, axes, physical calibration
and source metadata. Both native ROI archives decode, with 1,256 ROI geometries;
native members are byte-exact and sidecar metadata agrees. Only the explicitly
different, admitted run-directory prefixes in JSON source addresses are
normalized; no measurements, identities, coordinates or calibration fields are
discarded. ZIP container timestamps are not scientific content. This extends
the earlier `*Labels.tiff` gate, which missed eight ImagingFlow checkpoint TIFFs
and two ROI archives.

Full-step owner-thread diagnostics retain numerical, finalization and progress
phases separately from unprofiled clocks. No execution-time Numba compilation was
observed in those diagnostics. A follow-up production cache probe invalidates
the extra-hashing hypothesis: ImagingFlow does not call the store-query cache or
hash the object-label query; all bounded cache lookups/writes sum to about 2ms,
and store mutation invalidation totals about 0.13ms on each side. These cannot
explain a 0.72s difference, so this route is rejected. Diagnostic clocks are not
promoted as performance improvements or as proof that the difference is harmless.

The exact-column CSV prototype saves only about 0.19s and was rejected as a
primary runtime fix. A saved-table provenance replay costs 15.9s, but that route
was not established in live CP execution and is not presented as a production
payoff. The continuing performance work remains under issue 162; native
CellProfiler timing and scaling-figure refresh are not completed by this receipt.

Compressed original guard/census/test artifacts, raw observations, complete
parity receipts, attribution traces, transactions, and SHA256SUMS are retained
here. `*.py.txt` files are exact task-local archival recipes with historical
paths, not installed utilities or portable product examples. Production timing
is reproduced with `scripts/benchmark_cppipe_well_throughput.py`, manifest
`benchmark/manifests/official30_portable_axis1.json`, mode `1w_1t`, and the two case
names in the tables, using the recorded revisions and shared environment.

The validated source tree lists every committed Python blob and dependency
gitlink. Publication adds documentation and evidence only; its source membership
is checked against that validated tree. Hosted CI remains separate from the
locally executed, original checks above.
