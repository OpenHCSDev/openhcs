Shared runtime plumbing qualification
====================================

Issue #384 covers repeated source resolution, metadata construction and artifact
rendering outside callable execution. This branch combines three production
dependencies under their existing lifecycle owners. It does not yet establish an
end-to-end speedup.

Primary target and abstraction admission
---------------------------------------

The primary performance goal is shared runtime work outside callable execution:
invocation and adapter preparation, stack loading, output registration,
finalization, saving, publication and provenance. Each existing abstraction must
own a distinct invariant, behavior or useful validated view. Objects that only
forward or reconstruct facts already owned elsewhere should be removed, with
consumers deriving directly from the determining owner. Shared algorithms belong
on existing nominal ancestors; a new class is not evidence of improved ownership.
Small measured redundancies are folded into the coherent migration even when
they cannot independently close the performance gap.

The ordinary 3D probe at clean revision 5d2fd489946e6885f161a7379e4eec1d14e307fd
records 9.860550 seconds of public server execution. Its same-thread root takes
9.757393 seconds, including 4.097127 seconds at runtime callable boundaries and
5.118847 seconds elsewhere inside steps. Final plate publication adds 0.476819
seconds. The callable boundary includes target resolution and signature filtering;
it is not an exact naked-kernel timer. Execution is inline for this one-worker
configuration; a configured fork policy does not imply a separate worker process.

A deeper probe on the same source records 10.275668 seconds, including 0.023519
seconds of explicitly isolated input capture. Its nonoverlapping coarse phases
locate 0.697612 seconds in output recording, 0.478745 in image-request preparation,
0.795071 in three atomic publication transactions and another 0.143612 in durable
target reconciliation. Remaining loading and output-registration work takes
0.739507 and 0.722780 seconds respectively. Stack metadata composition takes only
0.102824 seconds across all consumers. These diagnostic clocks locate work and
must not substitute for an ordinary uninstrumented paired comparison.

Required output work remains included: this pipeline saves 120 TIFF planes and
six result CSVs. Some work outside the callable boundary is numerical table
assembly or actual saving, so the full noncallable duration is not asserted to be
removable indirection. Nine stack-composition calls belong to loading; nineteen
belong to unstacking. Aggregate composition counts do not establish cache misses.

Saved real-payload replays confirm that duplicated input/name resolution and
rebuilding a compiled callable contract have small individual payoffs: about
0.112 milliseconds per input pair and 4.386 milliseconds per 211 resolutions.
These are included for ownership cleanup, without attributing the larger adapter
gap to them. The direct cache payload migration removes
``RuntimeImageStackCacheValue``, which owned only a forwarded ``stack`` field;
the cache retains path/memory identity, invalidation and execution lifetime.
All 102 related lifetime/source-projection controls pass for that migration.

Complete saved atomic publication transactions retain actual parser, labels,
saved paths, pretransaction JSON, locking and filesystem writes. Deriving
geometry from the already decoded nominal projections reduces a 60-path
transaction from median 0.13556 to 0.07601 seconds and a 120-path transaction from
0.27224 to 0.15354 seconds, with byte-identical complete JSON. The production
implementation also reproduces both baseline byte hashes, and 57 metadata,
projection and image-output controls pass, including pruning, concurrent partial
inventory updates, fresh geometry and atomic rollback. This is stage replay
evidence, not an end-to-end speedup claim; integrated qualification remains in
progress.

The existing CellProfiler executor now resolves the compiled raw callable once
at its validated invocation boundary and passes that target through the existing
processing and slice dispatch. The existing callable-view policy accepts that
already resolved target; no additional generic invocation type or parallel
contract/callable fields are needed. Image source-name projection consumes the
already resolved payload through the existing artifact strategy family.

The executor does not own a second interpretation of input relations or returned
artifact contexts. ``ArtifactSpecCollection`` derives exact broadcast indices
from its ordered declarations; ``RuntimeReturnedOutputMatcher`` contextualizes
the compiled canonical return ABI. The old CP helpers are deleted. The existing
contract, collection and returned value determine these answers directly.

The deeper clean-source probe at 5d1f1a781eda851b4783b68db342b76eeef9dea9 records
10.053237 seconds of public execution, including 4.465789 seconds at the callable
boundary and 4.939001 seconds elsewhere inside steps. Loading takes 0.699904
exclusive seconds, image recording 0.519127, output identity 0.412492 and image
request preparation 0.388981. Explicit diagnostic capture costs 0.044853 seconds.
These partitions are diagnostic evidence, not accepted A/B measurements.

All 23 produced-stack cache hits correspond to previously stored output paths.
The nine misses are original inputs; seven repeat earlier source reads and cost
0.5149 seconds inclusively. Those inputs are already in memory. Caching their
mutable arrays by path alone is rejected: storage has no mutation revision and
loaded source semantics depend on binding, aliases and plane contracts.

The next shared route is metadata ownership, rather than a second pixel cache.
Changing spatial context, intensity or image names repeatedly constructs source
provenance and copies/fingerprints its component mapping. Source loading and CP
image recording consume this common path. The saved typed ImageMath fixture
retains actual nested mapping ownership for a cold-promotion and complete-workflow
replay. An isolated query-cache payoff does not admit this migration. CP-recorded
outputs already bypass generic postprocessing; removing that hypothetical second
contextualization would not affect the measured recorder.

The unmodified-main light trace located about 3.44 seconds in loading, unstacking,
saving and finalization for the representative 3D pipeline. CP request and output
context construction account for another approximately 1.216 seconds. These are
diagnostic bounds, not additive nested timer totals or accepted benchmark clocks.
Repeated artifact rendering alone is bounded at about 0.297 seconds; saved plane
projection replay estimates about 0.20 seconds for that individual component.
Neither is admitted as a sufficient standalone performance route. The integrated
boundary must demonstrate a material improvement in ordinary execution.

Production authorities
----------------------

``ImageMetadataProjection`` owns the common single-pass image metadata algorithm.
Source-plane and leading-axis specializations provide their declared projection
semantics through inheritance. Provenance constructors consume the actual
``SourceImageProvenance`` constructor defaults, avoiding absent-field allocation
without a second default roster. Mutable scalar payload metadata retains its
independent ownership and mutation controls.

``SourceMetadataRecord`` owns declared/parser/rule resolution. Its declared leaf
retains live input semantics, while its resolved leaf enforces owned immutable
metadata at construction. ``RuntimeSourceResolutionSnapshot`` belongs to the
existing context-local runtime source cache and retains its determining inputs.
Only the explicit execution factories take this boundary; direct constructors and
unknown paths preserve live resolution. Derived caches are discarded on process
transport. The original adapter provenance construction remains authoritative:
deep-freezing selector records must not change repr-based image identities.

``MaterializationBatch`` owns rendering and saving. Actual saved outputs flow into
the existing metadata target family, step observation, worker observation and
plate observation. Export paths derive from these outcomes after payload resource
release. Removed rerender helpers and the old context-derived export path API have
no remaining consumers. Historical debug reuse retains explicitly named previews;
these do not claim new successful saves. The component receipt describes the
retained CSV consolidation and independent viewer expectation consumers.

Qualification and disposition
----------------------------

The integrated source passed 1,362 behavioral tests. Each of the three components
passed the original unmodified R0 guard. Final combined R0/R1 passed against main
91dc52d4040890e1b88494acba7368196f6cd1e8 at tested source
dc1a371b06079ff249c8c6432953d21e0c05917b, without increasing debt allowances or
source checks. The main synchronization passed 85 help/output/source-resolution
controls. These source ratchets are scoped guards, not a formal proof of every
dynamic binding.

The first complete saved-native gate exposed two illumination-correction
publication failures: actual numeric NPY saves admitted directories without any
raster images into metadata publication. The inherited raster-inventory admission
now governs directories derived from successful saves. A real FileManager NPY-only
control reproduced the failure; a mixed TIFF/NPY control preserves exact pixels,
raster inventory, alias and calibration. All 269 related controls passed. The
repaired full gate completed: all 30 cases equivalent, zero differences. The
original 28-pass/two-error gate is retained.

Repaired ordinary ABBA evidence
------------------------------

Two main and two candidate observations per case were retained, without excluding
samples. Revisions are the exact dc1a371b/91dc52d4 sources above. In seconds:

========================= ======================= =======================
Case                      Mean execution          Mean pipeline total
========================= ======================= =======================
3D monolayer              10.278553 -> 9.657654    12.241441 -> 11.607624
Imaging Flow Cytometry    15.506204 -> 15.423871   17.719883 -> 17.949389
Advanced segmentation     8.658128 -> 8.887496     11.158074 -> 11.397346
========================= ======================= =======================

3D execution improves 6.04%, while advanced execution regresses 2.65%. The default
memory observer's mean peak process-tree RSS changes by +14.65% for 3D, -3.41% for
Imaging Flow Cytometry and +10.87% for advanced segmentation. Process-tree RSS can
count shared fork pages repeatedly; these figures do not prove distinct physical
allocation. Candidate memory varies substantially between the two observations.
This is mixed evidence, not an accepted broad optimization. PR394 remains draft.

The pre-publication-repair eight-sweep observations remain retained separately;
their larger improvement is not substituted for the repaired source's results.
External evidence: shared-runtime-plumbing-repaired-qualified-abba-summary-
20261001.json and every corresponding source/input/observation receipt in the
openhcs-benchmark-runs evidence directory.

Fresh native qualification and next dominant route
------------------------------------------------

The revision-pinned matched Imaging Flow Cytometry driver completed three observed
native CP/OpenHCS repetitions and one warmup. All observed repetitions have zero
output differences under the existing numerical tolerances, exact discrete/schema
checks and strict declared output inventory. The input is one well with two native
image sets, one OpenHCS worker and one native job; the configured worker start
method is fork. Native and candidate phase boundaries are retained separately.
The driver's timing_claim explicitly remains none until first-module/first-axis
boundary equivalence is qualified. No native throughput ratio is asserted here;
the physical 3D volume/plane consumer gap also remains unfinished.

Fresh paired diagnostic traces cover all three workloads with identical owner
hooks. Their high-frequency instrumentation perturbs costs, so these are authority
and call-count evidence, not accepted timing clocks. The 3D trace reduces
SourceImageIdentity construction from 142,412 to 78,769, but still calls
SourceMetadataRoleView.scalar_items 194,349 times and source metadata field identity
1,120,064 times. Image-processing invocation remains approximately unchanged in
these traces. Repeated metadata queries are the next potentially material generic
route; saved representative replay must establish its transferable payoff before
another production authority is admitted. Immutable query ownership must retain
live public mapping behavior, lazy validation, alias/role semantics and image
identity fingerprints.

Source snapshots structurally retain historical projection owners, but output
publication does not normally replace these workspaces' cached metadata documents.
The observed RSS increase is therefore not attributed to snapshot generations.
Rendered outputs also remain visible through immediate publication; many arrays
already belong to runtime storage. Per-process memory and ownership diagnostics
must distinguish extra references from newly allocated buffers before changing
that boundary.

The subsequent normal main396 merge changes documentation, knowledge resources
and five knowledge-transfer test assertions. OpenHCS production source bytes are
unchanged from the corresponding measured candidate and baseline revisions; the
existing source/benchmark evidence remains pinned to its original revisions.

Issue and branch audit
----------------------

The source components are integrated in actual draft PR394, formally linked to
issue384. A branch/history audit covered 46 local worktrees and 194 remote branches;
the two subsequently created branches have PR396 (merged) and PR397 (draft).
Current branch tips were checked beyond historical PR association, including exact
source patch equivalence for squash/rebase history. No additional useful
unpublished fix branch was identified. Rejected prototypes and obsolete planning
branches are not nominated as unfinished production fixes.

The subsequent complete audit verifies eight of 26 open issues have formal
closing PR references and exact manual ConnectedEvent entries; 18 still lack an
actual complete fixing PR. Mere cross-references and diagnosis-only drafts are
not counted. The pairs are 138/207, 213/217, 320/217, 355/358, 384/394, 386/388,
395/397 and 398/399. For the three automatically detected links whose manual
mutation was initially a no-op, the exact original PR bodies were restored after
the manual links were created. Head, base and draft state were preserved.
Audit evidence: official-development-link-final-20261001.json/.md,
manual-development-relink-exact-events-v3-20261001.json,
remaining-remote-branch-pr-audit-20261001.json and local-worktree-branch-inventory-
20261001.json in the external evidence directory. Counts describe that pinned
audit rather than future repository state.

The earlier runtime-plumbing prototype 2253ec63b is rejected. Its paired timing
did not establish a gain and its original R0 gate failed. It is not part of this
branch or the accepted evidence. Failed controls and diagnostic observations are
retained in the external benchmark evidence directory rather than replaced with
the fastest observations.

Pipeline clocks exclude ZMQ server startup, mandatory registry/kernel prewarming
and shutdown. Timed runs use the ordinary public OUTCOMES path and default memory
observer, without profiling injection. Candidate and baseline must have frozen
clean source revisions and the same dependencies, affinity and environment.
