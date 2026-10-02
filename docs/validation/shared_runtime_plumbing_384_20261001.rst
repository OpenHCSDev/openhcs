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
the compiled canonical return ABI. ``AlignedImageStack`` binds the complete
declared output roster to its exact slice contexts in one linear traversal. The
old CP and canonical-values helpers are deleted. The existing contract,
collection and returned value determine these answers directly.

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

The subsequent ownership/publication follow-up normally merges main
76a2d392056f4fa6cc74bc122a552edc32f24239 at candidate
84057fbefd0ad5469c766051e19b34f42e851102, including the declaration-owned
classification and singleton image-selection repairs. All 955 controls across
26 changed-path and relevant main-owner test files pass, with two existing
watershed warnings. Original unmodified R0 and R1 pass against that main, with
no metric budgets or exclusions changed. The R1 scan uses the current NRA
checkout's virtual environment and its original 120-second deadline. Earlier
failed owner-growth/context-inspection guards and the wrong-interpreter import
failure are retained. Evidence: shared-plumbing-final-local-gates-20261001.json
and the original R0/R1 logs in the external evidence directory.

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

Existing-owner follow-up ordinary ABBA
-------------------------------------

The synchronized follow-up compares main 76a2d392 against candidate d9c9f8fe4.
The candidate's production source is the locally qualified 84057fb revision;
subsequent changes only retain the qualification receipt. Two observations per
side use the same ordinary public path and retain every sample. In seconds:

========================= ======================= =======================
Case                      Mean execution          Mean pipeline total
========================= ======================= =======================
3D monolayer              11.173033 -> 9.979570    13.166303 -> 11.915196
Imaging Flow Cytometry    16.847054 -> 18.891492   19.058024 -> 21.417949
Advanced segmentation     8.802229 -> 8.616838     11.271471 -> 11.113117
========================= ======================= =======================

3D execution improves 10.68% and advanced execution 2.11%, while Imaging Flow
Cytometry regresses 12.14%. Its candidate observations are 17.371243 and 20.411741
seconds, compared with 17.554674 and 16.139433 for main. Compilation is also
inflated in the slower candidate sweep. These samples establish mixed evidence,
not a statistical significance or causal attribution; PR394 remains draft.

All 24 ordered Imaging Flow Cytometry step occurrences align. Most of the extra
time is inside steps, distributed across the slower candidate sweep. Between-step
gaps remain about 0.017-0.023 seconds; execution outside the complete step span
does not explain the regression. Existing output comparisons and shared metadata
ownership investigation continue before promotion. Evidence:
shared-plumbing-owner-followup-qualified-abba-20261001.json and its summary,
source receipts and all per-step/progress observations.

Across all six run pairs, Imaging Flow Cytometry's two header rows and all
1,800-by-527 measurement cells match exactly. All six 3D CSV schemas, rows and
cells match, as do all 120 TIFF arrays, shapes and dtypes. Ordinary output
inventories match. Outcome-wire differences are fresh execution UUIDs and actual
run-root path prefixes; no scientific values are present in those outcome views.
Advanced's database/properties were not numerically compared, so absence of
ordinary CSV/TIFF output does not establish its parity. Evidence:
shared-plumbing-owner-followup-abba-step-output-audit-20261001.json.

The next normal synchronization integrates main
0d07909b07870557a04f125452dc6944db77cb6c, including PR358's startup feedback and
worker-budget repair, at candidate fdf50241aa9adc6d96bc9c530dcc9acd19692b64.
The recorded ZMQRuntime dependency 668edafcb5ee530a163377c936431ae1e8334e85 is
checked out in both trees and consumed through the shared editable environment.
All 498 preparation/startup/CP integration controls pass, with six skips and two
existing warnings; original R0/R1 pass with unchanged budgets and exclusions.
Issue355 is closed by its existing merged PR. The ABBA remains pinned to its
measured sources; no timing result is projected through this synchronization.
Evidence: shared-plumbing-main355-local-gates-20261001.json.

Subsequent normal synchronization consumes documentation/knowledge changes in
main PR405 and PR406, through e66500e7ae3804abca1396681c50e1cef5e9a11e. These merges
do not change production source or dependencies. All 23 knowledge-transfer controls
pass on the final merged declarations, with two existing warnings. Benchmark and source-gate
observations remain pinned above.

Independent review of the isolated metadata-owner migration found the important
distinction between ordered selection-record equality and public mapping-content
equality. It also checked duplicate stringified keys, normalization error order,
output-extension insertion order and fields-only transport. That migration remains
outside this PR until the affected consumers preserve their existing semantics
and the complete production-owner replay and source gates pass. Review evidence:
source-metadata-owner-independent-review-20261001.json. No stage replay is promoted
as an end-to-end gain.

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

Global lifetime counterfactuals: rejected routes
----------------------------------------------

The next ordinary diagnostics and exact saved-input replays reject several
insufficient standalone routes before further implementation. These are payoff
bounds, not candidate speedups. Their observations remain revision-pinned; they
do not supersede the mixed ordinary ABBA above.

* The eight complete saved IFC geometry owners take 0.4745 seconds in aggregate
  median replay; the actual complete spreadsheet renderer takes 1.3662 seconds.
  Even eliminating both separate phases has an optimistic ceiling below two
  seconds. The isolated geometry/export route is stopped.
* On main 18317499be069fbe58387137f326ac7b6ff57988, all 634 original Advanced
  measurement queries take 0.6422 seconds, while complete CPA collection takes
  1.1943 seconds. Fabricated missing-cell counts alone do not admit this route:
  eliminating both whole phases still cannot supply two seconds. The saved
  query capture is a bounded subset, not a substitute for the complete clock.
* On that same main revision, all 32 3D stack loads and all saves take 0.9927
  and 0.9526 exclusive diagnostic seconds respectively. Eighteen loads select
  an actual previously stored named producer; all eighteen allocate independent
  main-flow pixel buffers. The full saved step-14 Resize input matches the
  stored Monolayer pixels exactly, but differs in filename-derived extension
  and per-plane source-name metadata. Direct value reuse would violate existing
  buffer isolation and provenance. A narrow named-handoff migration is stopped.
* A low-overhead aggregate diagnostic on that revision measures all 40,673
  ``ImagePayloadMetadata.__post_init__`` calls at 0.8919 inclusive seconds and
  all 147,354 ``SourceImageIdentity.__post_init__`` calls at 0.5544 inclusive
  seconds. These totals overlap and must never be added. Constructor count
  contraction alone cannot justify the multi-second target, even though counts
  identify repeated work. The proposed 44.6 percent birth reduction is not a
  measured speedup. The wider field-derivation lifetime remains unqualified.

Every diagnostic uses the ordinary OUTCOMES path, one worker/thread and the
default memory observer. Hook overhead is retained; server startup, prewarming,
compilation and shutdown are outside execution. Exact original-method timing
does not establish that the whole measured duration can be removed. Controllers,
source/dependency freezes, successful outputs and failed earlier captures are
retained under ``/var/tmp`` and the external benchmark evidence directory.

Evidence: ``measurement-lifetime-actual-input-baseline-replay-20261001/receipt.json``,
``global-plumbing-three-workload-coarse-lifetime-20261001.json``,
``runtime-value-handoff-step14-fixture-metadata-inspection-20261001.json``, and
``metadata-initialization-aggregate-decision-20261001.json``. The full query and
handoff observations reside in their corresponding ``/var/tmp`` captures.

Main 9a04107492ad90233394cf17524d0ca8e74062bb is normally integrated, including
the merged native-module source-discovery repair in PR416 and source projection
capability repair in PR418. Earlier behavior/source/performance gates retain
their exact source pins. PR394 remains a draft formally closing issue384.

The next bounded union-depth diagnostic on that main measures 3.6594 seconds
across selected metadata construction, provenance projection, component/literal
field lookup and merges. Its 972,354 selected calls enter 102,445 outer selected
regions; nested work is timed once and the final depth is zero. It retains hook
overhead, includes metadata inside callable wrappers and excludes physical
processing, I/O, complete writer preparation and publication ancestors. Thus
this is a plausible wider counterfactual scope, not 3.6594 recoverable seconds.
Reflection controls compare original and wrapped constructors: hints and errors
agree, including the original generated image-metadata constructor's existing
``NameError('InitVar')``. Actual provenance mapping decode succeeds through the
hooks. The next gate is an ordinary production comparison against the existing
nominal immutable-field owner, before further implementation or broad gates.
Evidence: ``metadata-lifetime-union-production-counterfactual-admission-20261001.json``
and ``metadata-lifetime-union-reflection-pair-control-20261001.json``.

Initial ordinary complete-field-owner counterfactual
---------------------------------------------------

The existing immutable field-owner migration is now included in this draft,
rather than left on an unpublished independent branch. ``SourceMetadataFields``
owns the common algorithms; live declared fields and owned resolved/durable
fields provide their actual lifetime through inheritance. Owned builtin values
permit local derived-view reuse, indexed lookup and readonly snapshot reuse.
Raw mutable mappings retain fresh derivation. The obsolete role/identity view
types and duplicate field algorithms are removed. Fields-only transport drops
process-local derived caches.

One initial ordinary, uninstrumented 3D pair compares main
9a04107492ad90233394cf17524d0ca8e74062bb against the complete candidate
401cd69fa718d6b19ce4dc35fb5f7c2d70f2d219:

=================== ============ ============
Metric              Main         Candidate
=================== ============ ============
Execution           11.6153 s    8.1170 s
Compilation         2.2212 s     50.7997 s
Pipeline total      14.5439 s    59.6670 s
=================== ============ ============

Execution improves by 3.4984 seconds in this initial pair; total time regresses
by 45.1231 seconds. All six actual result CSVs have exact rows and all 120 TIFF
arrays have exact dtype, shape and pixels, with equal complete inventories.
This is an initial counterfactual, not accepted ABBA or all-case native parity.

The compilation regression is not startup time: 239 Numba cache files are written
after axis compilation, over 48.2219 seconds, ending immediately before compilation
completes. The cold candidate source-path kernel cache exposes a startup regression.
Commit 2b86bfbe49f36d302dcd67c5b0a0cb4f656f1eb0 implemented registry kernel warming;
ffba8426cefcaa87b6b00ff056e4cb96855233e4 in PR358 subsequently removed that loop
and deferred readiness to selected compilation. PR420 restores the existing registry warmup lifecycle and closes issue162.
Its separate empty-cache regression gate is recorded below; the integrated
field-owner performance still requires requalification.

The field-owner integration into this draft passes 81 scoped lifetime/ownership
controls with metaclass-registry 0.2.2. A subsequent projection correctness repair
passes 173 scoped controls in its isolated source. It restores source-plane
derivation and cross-invalid field/error ordering before leading-axis guards,
shares normalization on the existing metadata owner, and deletes premature
projection properties. That repair requires performance requalification; the
initial pair is not projected through it. Arbitrary external constructor/mapping
callback equivalence remains an OPEN obligation, not a claimed proof.

Evidence: ``metadata-owner-ordinary-pair-output-parity-20261001.json``,
``metadata-owner-cold-compilation-regression-cause-20261001.json``,
``source-projection-order-384-correctness-patch-20261002.json``,
``/var/tmp/openhcs-metadata-owner-ordinary-pair-20261001/observations.json`` and
``/var/tmp/openhcs-integrated-metadata-owner-scoped-gates-20261002.log``.
Main 25d56ae3fb9b80acda80f3cf4e1c8667939147eb is normally merged; the shared
environment and PR submodule consume the declared published metaclass-registry
0.2.2 source 393a7e03003cdc56df9013f932ed4f26e632d77a. Earlier observations retain
their measured source/dependency pins.

Restored registry readiness on main
----------------------------------

PR420 merges the startup correction to main
107498cfacf3b12d926c55f84c4b3cb7c04aa50f. That main is normally merged into
this performance branch. Existing affinity admission, cancellation ownership
and compiler guards for declarations introduced after startup are retained.

An ordinary, uninstrumented 3D 1w_1t run at fix source
e55e2ec0bc98ad750837cd4dcfd830ad04096286 starts with a new empty Numba cache.
Compilation is 1.720214 s, execution 11.151797 s and pipeline total 13.637182 s.
All 481 cache files are written before pipeline submission; the last write is
6.001317 s before run creation and no cache files are written during compilation
or execution. Server startup, warmup and shutdown are excluded from pipeline
clocks. All six CSVs and 120 TIFF arrays exactly match retained main9a output,
including dtype, shape and matching inventories. This is a lifecycle regression
gate, not an ABBA performance comparison or current integrated-candidate timing.

The fix passes 37 scoped tests with five single-affinity skips and both actual
two-core fork controls. Original unmodified R0 passes for openhcs, scripts and
benchmark; R1 reports no increases against main25d56ae under its unchanged
160-second budget. The failed Python3.12 ratchet launch and uninitialized
worktree R1 launch remain retained; final guards use Python3.14 and the initialized
main repository, respectively, without modifying either detector.

Evidence: ``registry-startup-readiness-162-empty-cache-pipeline-20261002.json``,
``registry-startup-readiness-162-validation-20261001.json`` and
``registry-startup-readiness-162-original-r0-py314-20261002.log`` plus
``registry-startup-readiness-162-original-r1-initialized-root-20261002.log``.
The original 50.800-second compilation regression remains retained. Current
combined performance, IFC behavior and source guards remain draft gates.

Complete-field ordinary ABBA and current ownership repairs
---------------------------------------------------------

The completed uninstrumented ABBA at main 107498cf against candidate 02609e12
has two observations per source for each workload. Execution/total means are
11.162969/13.119510 s versus 8.295599/10.351318 s for 3D,
8.706567/11.262818 s versus 8.474416/11.132766 s for Advanced, and
16.500067/18.794964 s versus 16.920803/19.454312 s for IFC. Thus 3D saves
2.867370 s execution and 2.768192 s total, while IFC regresses 0.420735 s
execution and 0.659348 s total in these samples. No statistical significance
or noise explanation is asserted. All observations remain retained.

Original unmodified R0/R1 rejected 02609e12. The actual metadata owner now owns
normalization and leading-axis transformation; the redundant raw projected
field dictionary, provenance normalization forwarder and foreign optional-state
handling are removed. Source and axis projection roles compose through
inheritance while preserving effect/error order and independent result ownership.
Common scalar admission is shared on SourceMetadataFields. The optional
intensity-proof projection and scale queries consume their existing authorities
instead of duplicating algorithms. Component controls include 41 scalar tests,
1,212 original-source behavior comparisons and 197 metadata/proof controls.
The collected classification projection census was also repaired to skip actually
abstract parameter declarations while still checking concrete descendants;
429 focused and 1,111 broader consumer controls passed before dependency update.
The inherited census failure was reproduced on main under the same imports.

The subsequent ordinary ABBA measures frozen production candidate
90c30e1adfacd25a834ed48949b430099c866134 against the same main 107498cf:

==================== ======================== ========================
Workload             Execution main/candidate Total main/candidate
==================== ======================== ========================
3D                   11.089386 / 8.172661 s    13.063124 / 10.106094 s
Advanced             8.854658 / 8.988559 s     11.408556 / 11.590607 s
IFC                  17.382926 / 16.212604 s   19.628127 / 18.661190 s
==================== ======================== ========================

3D saves 2.916725 s execution and 2.957031 s total; compilation means are
1.214262 / 1.209572 s. Advanced regresses 0.133900 s execution and 0.182051 s
total. IFC improves 1.170322 s execution and 0.966938 s total in this batch.
These means do not erase the adverse026 IFC evidence or establish significance.
All twelve case observations succeed through ordinary OUTCOMES, default memory
observation, one well/thread and CPU5. Both sources use identical public drivers,
shared dependencies/native binaries and mandatory registry preparation before
readiness. Server startup, prewarming and shutdown are excluded. There are no
profiling hooks, captures or scientific substitutions in either ABBA.

For each ABBA, all six output pairs pass scientific comparison. All six 3D
CSV exports and all 120 TIFF arrays match exactly, including complete scientific
inventories, dtype and shape. IFC has exact headers and all 1,800 x 527 result cells.
Advanced uses the existing CellProfiler database/export comparator at absolute
and relative 1e-6, with exact schemas, cardinalities, discrete values, identifier
relationships and categorical data. Eight scientific subject tables and all
relationships are nonempty. Unsaved final segmentation masks were not observed.
The90 comparison reads actualaf45 source against its still unchanged pre-update
dependency environment, attested before and after. Output files remain unchanged.

At 90c30, original R1 passes with no increases under the unchanged 160-second
budget, and original R0 scripts/benchmark pass. R0 openhcs remains RED solely
because the scalar/container rejection classifier moved from virtual workspace
decoding to its actual field owner: source_metadata gains one local switch and
three arms, while virtual_workspace_metadata loses one switch and four arms.
The original per-file gate is not waived or declared passed. Across all changed
roots the global delta is zero switches and minus one arm; untouched files cancel
because these original metrics are file-local AST measurements. Existing error
and reported-class observation ordering is preserved rather than altered to
satisfy the metric. The global 702-module authority audit found no existing
replacement retaining that complete grammar/error contract. These are distinct
architecture and behavioral gates, not interchangeable claims.

After both ABBA and all their comparisons finished, main
c32447f1c86a1878a313d1643a398e30ac20f75e was normally merged into this branch.
The shared environment now installs declared published ArrayBridge 0.3.6 at
source 1e53d03d9f468322a1c085c8be29485fb139caf2, openhcs-basicpy 1.3.1 and
JAX/jaxlib 0.9.2. Metaclass-registry 0.2.2 source 393a7e0, NumPy/SciPy/Numba
and both native extension hashes are unchanged. Pip check reports no broken
requirements and actual package imports pass. The separate native CellProfiler
4.2.8.1 environment remains unchanged. Earlier timings retain their measured
source/dependency pins; they are not projected through this new main/environment.
New combined qualification and full native parity remain required.

A capture-free coarse diagnostic on frozen 80d92 source partitions one 9.208835 s
job into 4.164762 s inside RuntimeCallableInvocation.call and 5.044073 s outside.
The callable boundary includes decorated processing/metadata and is not a pure
image-kernel measurement. Diagnostic wrappers are not accepted performance
comparisons. Full load, unstack, save, CP image recording and image request phases
have a nonoverlapping 3.009640 s upper bound. Recovering 2 s requires eliminating
at least 66.453% of those complete phases, not just a cached recomposition or
an original-source cache miss. The existing named-value to eager-plane metadata
to MemoryVFS to whole-stack round trip is the next structural premise. Mandatory
named/mainflow pixel-copy isolation and concurrent durable publication remain
constraints. No new production route is admitted without a representative replay
showing that complete consumer closure can realize a material payoff.

Retained evidence is in the shared benchmark-runs directory:
``owned-metadata-90c30-ordinary-abba-csv-tiff-parity-20261002.json``,
``advanced-ordinary90-six-pair-sqlite-parity-20261002.json``,
``pr394-integrated-90c30-original-source-guards-20261002.json``,
``scalar-owner-original-r0-global-delta-counterevidence-20261002.json``,
``integrated90-classification-concrete-projection-census-fix-20261002.json``,
``shared-main-dependency-update-c32447-20261002.json`` and
``pr394-90c30-whole-mainflow-value-frontier-20261002.json``.
Source freezes, complete observations and diagnostic boundaries are retained in
``/var/tmp/openhcs-owned-metadata-90c30-ordinary-abba-20261002/`` and
``/var/tmp/openhcs-owned-metadata-phase-probe-20261002/``. The original 026
comparison and original failures remain separate pinned evidence.


Prepared callable owner and independent plane follow-up (2026-10-02)
------------------------------------------------------------------

Registry preparation now resolves canonical and actual raw signatures after all
function preparation hooks and before READY. Authored declarations resolve in
compilation. Immutable signature pairs travel on the existing CallableMetadata
through existing function-reference/worker transport. Runtime filtering, batch
defaults and canonical argument admission consume the associated prepared view;
three separate signature/default/type LRU caches and late kernel preparation are
removed. Server preparation remains outside pipeline clocks.

The isolated owner repair ``760e9ae8613d8737411a627b6abfe6a15f4ca0b9`` moves actual
target resolution, signature state and carrier grammar onto CallableMetadata;
CallableProjection/Reader own preparation admission, RuntimeCallablePolicy owns
invocation, and Pure2DSliceBatchExecutor owns the formerly duplicated executor
selection. Distinct actual targets always receive independent raw snapshots;
only the same actual target shares its canonical snapshot. No new wrapper class
or equality comparison over arbitrary callable defaults is introduced.

Original, unchanged R0 passes against both the prepared-callable commit and the
frozen qualification source, eliminating its new class-size, Boolean-chain and
foreign-absence debt. Original R1 passes within the unchanged 160-second budget
with 3,084 projections. These are isolated gates; the inherited scalar-owner
per-file R0 gate on the whole branch remains open. Focused owner tests pass 105
controls; the larger 648-pass/five-skip suite initially retained two baseline-red
plane-domain controls. Their failure also reproduces on untouched ``94915``.

The independent repair ``0b7f6f98a4b19d85d0dbb20f4db49e45cd0d90c1`` validates an
explicit object projection against its declared source axis and nonempty
acquisition cardinality directly. Independently authored runtime planes can own
an exact projection without acquisition-plane provenance. Physical source/label
cardinality and spatial-shape checks remain mandatory. Thirty-nine controls pass,
including both axes at one/two planes and wrong-axis refusal. No object-domain
semantics are inferred from source storage axes.

The all-30 scientific qualification on frozen ``94915`` is RED: 24 cases pass;
four fail at missing payload context in Align/Crop, one loses its server to a
confirmed kernel OOM kill, and one differs in threshold entropy. Saved input
replay traces that entropy mismatch to missing Threshold source scale/dtype at
the canonical raw boundary. Truthful declarations are being corrected without
scientific-body or tolerance changes. Linux killed endpoint PID 2412356 with
13,360,004 KiB anonymous RSS; the dominant allocation/retaining owner is still
unmeasured. Issue #433 tracks that distinct execution-server acceptance gate and
is formally linked to this draft PR. Retained native clocks are not current
paired speedup evidence.

Evidence stays in the external benchmark RUNS directory, including
``pr394-94915-all30-native-science-qualification-red-20261002.json``,
``pr394-signature-owner-760-source-inventory-20261002.json``, the original R0/R1
receipts, and ``issue419-explicit-object-plane-cardinality-followup-20261002.json``.
Two partial cohort captures complete all 31 production steps and match all six
CSV files and 120 TIFF dtype/shape/pixel arrays exactly, but each admits only six
of ten graph snapshots. V4 identifies an unsupported native allocation owner in
the four remaining before-state graphs; those graphs remain missing. Diagnostic
capture clocks do not establish a speedup, and the additional multi-second
whole-value plumbing payoff remains unmeasured.


Prepared payload contract qualification (2026-10-02)
--------------------------------------------------

The integrated library/kernel readiness run at ``1ad3898`` prepares all 267
functions and 976 targets before READY. It creates 265 distinct actual raw
signature snapshots and reuses the canonical snapshot for two identical actual
targets. Three rounds of prepared annotation, carrier, raw-signature, batch
default and invocation-construction queries perform zero additional live
signature/type-hint resolutions. The fresh-cache 90.381-second preparation is
server startup diagnostics, excluded from pipeline clocks. Later explicit-plane
validation and test-producer changes do not change these warming/signature owner
sources. This finite check does not claim zero reflection for arbitrary
unprepared authoring or unsupported callable mutation.

The annotation-only follow-up ``9ae4c9426`` corrects twelve existing context
consumers, three forwarding helpers and CropRequest.image. Existing
RuntimeArrayData preserves their nominal image payload at the actual raw
boundary; NumPy-only consumers still receive NumPy arrays. Scientific bodies,
defaults, decorators and return declarations are unchanged by AST comparison.
Frozen ``7241ca99b`` passes native-science comparison for Colocalization,
Neighbors, YeastColonies and pixel classification with zero differences.
YeastPatches passes its previous Crop failure but subsequently exposes an
incorrect RGB source domain from IdentifyObjectsInGrid.

Saved actual RGB pixels, source metadata and both 93-ID label artifacts isolate
the remaining defect: IdentifyObjectsInGrid's primary argument and its existing
request field/from_runtime argument falsely declare np.ndarray despite passing
the image to SourceImageObjectLabelBuildRequest. Their raw ABI strips the
1200-by-1600 source domain and (150, 170) crop origin, producing a (1255, 3)
domain for (835, 1255) labels. ``84e99c0dd`` changes only those declarations and
their direct RuntimeArrayData import. Scientific bodies and the refusing domain
guard are unchanged. Seventy-seven scoped controls and 127 integrated controls
pass. A fresh YeastPatches execution at that revision passes the existing native
comparator with zero differences. Its replay uses retained source-pinned native
artifacts, not newly timed native execution. The original 84-entry/38-module AST
frontier now has no remaining exact classmethod context leads; aliases, inherited
dispatch and dynamic routes remain outside that finite inventory.

The five affected cases have passed across these two targeted sources. The full
all-30 latest-head science gate, the execution-server OOM retaining-owner gate,
the whole-branch scalar per-file architecture gate and fresh ordinary performance
qualification remain open. No current native speedup is inferred from retained
clocks or instrumented captures. Evidence includes
``issue419-actual-integrated-1ad-signature-owner-readiness-20261002.json``,
``pr394-7241-context5-science-qualification-20261002.json``,
``issue419-grid-context-fix-20261002.json`` and
``pr394-84e99-grid-science-qualification-20261002.json`` in the benchmark RUNS
directory. All original failed source-pinned runs remain retained.

Graph ROI source-bearing writer integration (issue #134)
-------------------------------------------------------

The receiving owner requested narrow integration from PR #404 checkpoint
``f3e566485a391a270a6d2c40dbfddf07881dcd3d``. The exact patch binds existing
ROIArchiveSourceMetadata to graph ROI content and places the same existing
ImagePayloadMetadata on Output. Graph provenance already selects its declared
source plane; no second global-plane selection is performed. Coordinate spacing
uses existing SourceVoxelSpacing. The binder, disk ZIP transport, geometry
projection and native admission retain their existing owners and guards.

On current ``38067a4a5`` before the production patch, the receiving seven-case
fixture reproduces three source-bearing failures and four refusal controls
pass. After integration, all seven pass alongside the original graph, batch
outcome and materialization controls: 87 PASS in 2.28 seconds. The existing
geometry test obtains geometry through the original archive projection before
its unchanged coordinate and feature assertions; bound transport metadata is not
mistaken for a graph feature. An independent cooperative graph subtype and new
feature require no new writer or consumer registration. Missing, unbound, mixed
and conflicting native source declarations remain refused before transport.

This is current-source synthetic writer/disk/archive qualification. Actual
installed public/native graph reopening remains with the receiving owner, and
no performance or biological acceptance claim follows. Original failures remain
in ``pr394-38067-graph-roi-before-20261002.log``; integrated controls are in
``pr394-graph-roi-integrated-after-20261002.log`` in RUNS. The historical PR #404
branch and its older publication proposal are not merged as a whole.

Opaque image domain and current 3D frontier (2026-10-02)
------------------------------------------------------

Frozen ``45f3a721e`` diagnoses the dominant current 3D failure: scalar output
composition adds a runtime axis to an opaque whole volume. Watershed receives
``(1, 60, 128, 128)`` and fails after 118.394 seconds inside its raw callable.
The failed job peaks at 3745.977 MiB. Installed Mahotas 1.4.19's filter-offset
formula requires a 2 GiB table for that incorrect 4D seed-label neighborhood;
the singleton changes neighborhood rank without changing image voxel count.
This is a source-backed bound, not an allocator-stack capture or attribution of
the original 13.36 GB OOM. No NumBa cache files are created during the observed
pipeline window. Cache warming does not correct an invalid scientific domain.

``d092a03af`` repairs composition using the existing nominal alignment owners.
``AlignedImageStack`` retains its declared outer runtime axis; named
``ImageOutputBundle`` members supply their original individual domains.
``PatternGroupOutputData`` derives saved member declarations from those original
values, and ``ProducedOutputSemantics`` retains that domain across physical-leaf
projection and passthrough. This execution-local fact distinguishes an opaque
single-Z volume from an explicitly declared one-plane runtime stack after both
have otherwise similar leaf metadata. It does not replace durable source ingress.
Mixed cohorts cannot manufacture one combined domain. Cache misses, overwrites,
named selection and independent pixel/mask/metadata ownership are covered.
Producer and loader bundle composition use the same existing authority.

The first scoped original R0 rejects ten added lines in the oversized runtime
class. ``6dd47dd7e`` moves actual input assembly onto existing
``PatternGroupData`` and shared independent copying onto
``ImagePayloadStackComposition``, removing the input loader's call into the
output factory. Both unchanged original scoped R0 and R1 then pass against
``45f3a721e``; 271 controls pass, including retained lazy device resolution for
bundle composition. The whole-branch scalar relocation gate remains separate
and is not waived. Cross-device composition equivalence remains unqualified.

A fresh ordinary CPU5/one-inline-worker execution at frozen ``d092a03af`` gets
through the first 18 steps. The entire Watershed step completes in 0.156588
seconds. The older figure is an instrumented raw-call failure, so these are not
paired successful timings or a native speedup ratio. The full pipeline still
fails at step 18, MaskImage: a correctly selected 2D invocation receives the
opaque secondary volume without a source-proved plane projection. The refusing
2D mask guard is correct. Failure-row zero compile/execute values are wrapper
placeholders; the public compile-event span is 1.619 seconds. Pipeline clocks
exclude mandatory registry/kernel server preparation and shutdown.

The generic relation-aware repair belongs at ``RuntimeInputBindingRequest``.
MaskImage, Crop and CorrectIlluminationApply already declare
``InputStackBroadcastSourceRelation``. That declaration permits broadcasts but
does not prove spatial-Z ordering. Contributor provenance or equal array lengths
cannot supply the missing pixel-coordinate proof. ``SourceSpatialDomain`` is
currently XY-only; source/transform ownership is being traced before extending
its existing contract. No function-specific mask path or geometry-guard
relaxation is included. Latest-head all30/native parity and ordinary performance
remain open.

Main ``902913616`` (merged PR #434) is integrated at ``ff9d7c79d``. The combined
14-file source suite has 810 passes and two unary GrayToColor failures. Both
failures reproduce unchanged on clean main ``902913616``; they are retained,
not converted into successful assertions or treated as axis-fix regressions.
No foreign PR implementation is duplicated.

Three completed same-server Human jobs at ``45f3a721e`` pass their scientific
comparisons and leave zero backend image-array bytes after each job. This
rejects the proposed completed-job backend leak for that workload. Generic
worker resource release already executes for inline jobs. The older OOM's full
allocation mix remains unknown; no speculative global cleanup is added.

Receipts remain in the external benchmark RUNS directory:
``issue433-rank4-watershed-large-allocation-source-bound-20261002.json``,
``issue433-three-complete-job-retention-counterevidence-20261002.json``,
``pr394-opaque-axis-input-owner-original-r0-openhcs-20261002.json``,
``pr394-opaque-axis-input-owner-original-r1-20261002.json`` and
``d092-mask-secondary-domain-caller-audit-20261002.json``. Frozen ordinary
outputs/source hashes are retained under
``/var/tmp/openhcs-opaque-axis-d092-ordinary-20261002``. The initial failed
guard-launch arguments and the original R0 growth finding are also retained.

Persisted derived-role publication (issue #435)
----------------------------------------------

``ce1b7acfc`` repairs duplicate publication of one saved image occurrence in the
existing metadata writer. The existing output context derives the declared
source alias; anonymous main flow remains anonymous. Produced records and
successful materialization outcomes share a path index. A second projection is
omitted only when declared alias, artifact kind, producer scope, exact path,
scalar acquisition address and full persisted image metadata agree. Distinct
files with colliding identities, stale scopes, different kinds and conflicting
metadata retain their original refusal. No source-projection guard is relaxed.
The index is linear in produced records and successful outputs.

The actual writer reproducer at baseline ``130c03a26`` saves two distinct role
images with real C2 addresses and calibration, then reproduces the duplicate
projection failure. At ``ce1b7acfc``, both roles publish once and reopen through
the existing virtual workspace; exact pixels, addresses and spacing pass. All
four independent refusal controls pass, together with 232 focused controls in
9.42 seconds. These are writer/materialization/reopening controls, not an
installed five-step acceptance or a performance benchmark.

Unchanged original scoped R0 and R1 pass for ``130c03a26`` to ``ce1b7acfc``.
The first candidate ``6dfda9597`` failed original R0 for a long producer-match
Boolean and a foreign absence probe. Moving alias derivation to its existing
context owner and comparing exact producer tuples resolves those findings.
The whole-branch scalar gate remains separate. Independent review finds no
blocker; persisted occurrence identity does not prove stale in-memory pixels
equal the final overwritten file. Pixel parity remains a separate gate.

The parent has supplied the original five-step source and bounded saved-path
facts in issue comment ``5948666249``. Actual produced-record and materialized
output pairs were not serialized there. Installed original-path acceptance
remains open; no biological replay or fabricated collision pair is claimed.
The separate #437 owner retains its singleton-consumption repair.

Main ``8551a4864`` (merged #438 and #439) is integrated at ``3de415d63``.
The integrated publication, axis and new MCP compilation controls pass:
247 tests in 51.50 seconds, with two existing pytest configuration warnings.
The scoped guard receipts are retained externally as
``issue435-ce1-original-r0-retry-20261002.json`` and
``issue435-ce1-original-r1-20261002.json``; independent review is
``/var/tmp/openhcs-issue435-independent-publication-review-20261002.json``.
Original failures and failed guard launches remain retained.
