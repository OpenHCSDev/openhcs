# Generic runtime optimization owners — issue 323

Current qualification is production `f7b39a2a4` on main `f24a828da`: 1,538 tests
plus 42 subtests, original guards, and all 30 native-reference cases pass. The
warmed-parent review fix, test-context isolation, exact receipts and matched
current timing limits are in [the synchronized validation note](../runtime_owner_sync_323_20261001.rst).
The source cohorts and timing observations below are historical evidence.

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


The October 1 closure is validated at
`95a98b0083aba2384c271e224746824fc9e40ce5`, against the same current main
`74eac059f67389ca071055c93fcbdd556ba79f1a`. Earlier source cohorts and concerns
above remain retained; the new source is listed separately in
`validated-source-tree-95a98b008.txt`.

Four remaining numerical caches now derive LRU storage and process lifetime from
the shared parents: granularity series, radial-label geometry, radial-spectrum
geometry and Zernike-label geometry. Each retains its existing 16-entry capacity
and numerical key/value calculation. The provider-owned OrderedDict globals,
eviction loops and granularity lock global are deleted. `SynchronizedBoundedCache`
owns granularity's individual operation locking through cooperative inheritance;
the process parent serializes first singleton construction. The executed gate
checks the MI constructor/MRO, singleton identity under simultaneous threads,
LRU promotion/eviction, registration and cleanup. Registry cleanup remains an
explicit operation, not a new automatic clearing policy between wells.

The logger-bound `RuntimeProfiler` moves from granularity to core runtime profiling.
Its eight numerical consumers now import core directly. The shared existing sink
determines environment gating and log/file output effects, covered with enabled
and disabled tests. The identically named CP module/function context profiler in
measurement execution support is a different authority; it and its bridge
consumer are byte-unchanged. NRA initially rejected the imported declaration
rename because dynamic importer exports were unresolved. The admitted sequence
migrates exact direct consumers in an authored, revision-checked stage before
guarded declaration rename/movement. The dynamic numerical export declarations
stay unchanged; this does not turn their OPEN export contract into a proved one.
The initial failed guard log, final complete simulation and recipes are retained.

The final combined execution gate passes **1,055 tests**, with the same one
optional Napari skip and two existing watershed warnings. Original CI-pinned R0
passes all three roots; OpenHCS has no increases and removes one StringDispatch,
three StringDispatchArms and two StringSubscript findings. Scripts and benchmark
are unchanged. Original NRA R1 reports no increased findings with complete
context (3,058 base / 3,056 candidate projections; the same two configured
detectors). The final original-ClassDef census has 5,128 original declarations,
5,116 projected declarations, and all 12 OPEN declarations across 701 modules.

Fresh normal public qualification uses the same single-lane route, dependency
pins, CPU 5 and shared persistent kernel directory. Mandatory readiness precedes
pipeline clocks; startup/shutdown are excluded. All four normal CLI runs report
success and one successful well. No checks or other task replays overlap them.

| Latest source / case | Main compile | Candidate compile | Main execution | Candidate execution | Main total | Candidate total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| ImagingFlow | 2.000s | 1.535s | 17.000s | 17.992s | 19.683s | 20.285s |
| 3D | 1.677s | 1.847s | 8.486s | 8.204s | 10.887s | 10.772s |

These are source/parity qualification pairs, not statistical performance proof.
The new ImagingFlow execution difference is +0.992s and its total difference is
+0.601s; the concern remains open. No speedup or neutrality is claimed. All 14
complete CSV comparisons and 240 persisted label checks pass exactly. The
extended gate also matches all 128 TIFF series, pixels, dtype, shape, axes,
calibration and source metadata, and both native ROI archives (1,256 geometries),
using only the previously admitted run-directory normalization for source
addresses and ignoring ZIP container timestamps.

A separate minimal process-global GC diagnostic on earlier candidate 00683 and
main 74e records overlap with actual step windows, including other threads.
Execution GC overlap is 0.244841s on candidate versus 0.059044s on main, a
0.185797s difference against that diagnostic pair's 0.177079s execution difference.
This explains that trace's difference, not all historical timing differences or
the latest source pair. GC is too small there to close the overall execution gap;
no production GC freezing/disabling policy was added. Public process headers
hash the embedded launch arguments; complete original traces remain in the local
run root. GC clocks remain diagnostic rather than unprofiled performance evidence.

Granularity's reconstruction is still a large intrinsic numerical term (about
2.22s in the saved live phase trace), with generic data movement around that step
small. The ownership migration intentionally leaves that numerical algorithm
with its provider. Further runtime optimization, fresh native CP timings and
scaling figures remain outstanding under the continuing performance goal.


Further October 1 diagnostics use the same production source (95a98b008); no
performance algorithm, GC policy, clock owner or export parser was added.
The normal public ImagingFlow +0.992s concern above remains unresolved.
In the minimal global-GC ABBA, execution is 16.476s / 16.868s / 24.282s / 16.122s
(main / candidate / candidate / main). The 24.282s outlier includes about 6.7s
in OverlayOutlines and its following gap; overlapping GC is only 0.231s.
Thus the earlier GC explanation does not generalize to all observations.

A separate owner-thread timeline has candidate/main execution 16.200s/16.039s.
Its 23 numerical steps total 13.494s/13.354s wall and 12.066s/11.951s owner-thread
CPU, with 1.375s/1.355s Linux scheduler run-queue wait. No Numba dispatcher
compilation is observed during those step/progress windows. These are diagnostic
clocks, not neutrality or speedup proof. The IPO progress-context path accounts
for about 0.4s; ordinary worker emits total only 6–8ms. Step sums do not include
the entire execution job. The native extension instruction and data sections
match main exactly; whole shared-object hashes differ in build-location metadata.
No cause for the scheduler wait is asserted.

Two exact-output reconstruction prototypes are rejected rather than promoted.
Against all six saved production float32 frontiers, the constant-five-spectrum
queue saves about 0.347s and the active-field queue about 0.340s across per-input
medians. The active-field version retains 64% of full field visits, insufficient
collapse to close the execution target gap. Constructing a component tree alone
costs 9.069s for the first input, versus about 0.54s for its current complete
reconstruction series; that route is rejected immediately. Task-only source and
replay receipts are retained, with no installed prototype or production claim.

Fresh native CellProfiler 4.2.8.1 uses the existing native synthetic-well batch
driver and native batch clock. One well owns six source planes and two image
sets, one native process, one native thread, CPU 5. One full warm-up batch precedes
two observed batches. First-module through post-run completion is 73.065s and
64.415s; invocation through completion is 73.194s and 64.524s. Python/JVM startup
is excluded; the worker separately records 1.004s startup after imports. No other
task benchmark, test or audit overlaps these runs. Provenance retains exact input
hashes, versions, thread policy, revisions and command-request membership.

Directly comparing raw exported tables was the wrong comparison scope: native
uses contextual headers while ordinary OpenHCS combined CSV uses flattened
headers (528 versus 595 columns). Both failed diagnostic attempts are retained;
neither is evidence of a measurement regression. The existing production
OpenHCSAdapter reference path instead compares native's contextual reference
with typed OpenHCS measurement artifacts and passes with **zero differences**
under the existing strict 1e-6 policy. No parser workaround, ignored measurement
field or relaxed tolerance was introduced. This adapter run retains value
observations for parity, whereas the normal throughput runs retain outcomes;
its 25.473s execution / 30.669s server job is a different observation scope and
must not replace the normal single-lane clocks or be claimed as a refactor
regression. Equivalence comparison (32.703s) occurs after the pipeline job.
Native image/ROI parity and the full scaling-figure refresh remain outstanding.
