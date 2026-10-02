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

Fresh native comparison and measurement lifetime frontier (2026-10-02)
--------------------------------------------------------------------

Frozen ``919fee286f8003a00aafc023ad28767d9713842b`` completed two ordinary
public-driver observations on CPU5, one inline worker/thread, with default
OUTCOMES and the default memory observer. Server startup, mandatory registry
and kernel warmup, and shutdown are excluded from pipeline clocks.

===================== =========== ============== ============== ==============
Case                  Compilation Server job     Pipeline total Native CP run
===================== =========== ============== ============== ==============
Advanced segmentation 1.324832 s  8.078740 s     10.650795 s    34.327521 s
Imaging flow cytometry 1.941105 s  15.497744 s    18.177965 s    77.795280 s
===================== =========== ============== ============== ==============

Native CellProfiler 4.2.8.1 uses the same physical input paths and SHA256
values, CPU5 and one thread. Its invocation excludes interpreter/JVM startup,
pipeline load and one complete warmup, but includes image-set preparation,
modules, post_run and Measurements.close. These are single observations with
different explicit setup/publication accounting; they do not establish a
kernel ratio, statistical significance or a new patch's speedup.

IFC's existing strict exported-science comparison passes with zero differences
and 1800 nonempty rows in each CSV. Native has 528 physical columns and OH 527:
the native redundant Number_Object_Number equals ObjectNumber for all 1800
rows, and the existing nominal identity policy recognizes that declaration.
This is semantic measurement equality, not identical cross-tool CSV headers.
The observed native/OH ratios
are 5.019781 for server-job execution and 4.279647 for pipeline total. Unsaved
segmentation masks are outside these retained outputs. Advanced's existing
scientific database comparison also passes with zero differences, but complete
source-information acceptance remains RED: five illumination sources across
two sites have 90 NULL cells instead of native values. The original integer
gate detects 40 Frame/Series/Height/Width cells; independent inventory adds
ten Scaling and forty FileName/PathName/URL/MD5Digest cells. Issue #444 is
formally linked to PR #394. No field exclusion or tolerance change is admitted.

A separate coarse diagnostic on the same source partitions IFC's 13.838053 s
execution into 9.373829 s inside the raw-callable boundary and 4.464224 s
outside. Advanced's 8.087572 s partitions into 3.836250 s inside and 4.251322 s
outside. The callable boundary includes decorated processing and result
assembly, not just numerical kernels. Nested inclusive spans are not added.
Exclusive recording, table assembly and export work has a combined envelope
of 2.812474 s for IFC and 2.882479 s for Advanced. Saving two seconds requires
roughly 71.11% and 69.38% reduction respectively; recording alone is insufficient.
Stack loading costs 0.126811 s / 0.106307 s. Ordinary progress events bound
between-step/axis work below 17 ms and other job-minus-axis gaps at
0.196432 s / 0.100492 s. Those routes cannot close the multi-second target.
Diagnostic clocks are not ordinary speedup evidence.

Retained evidence lives under ``/var/tmp``: ordinary outputs and source freeze
in ``openhcs-latest-ordinary-advanced-ifc-20261002``, fresh native inputs,
reports and IFC comparison in
``openhcs-current-native-advanced-ifc-v2-919fee-20261002``, and coarse regions
in ``openhcs-current919-runtime-phase-probe-20261002``. Independent source-field
inventory is ``advanced-fresh-native-missing-illum-metadata-20261002.json``;
the dominant cost/owner receipt is
``openhcs-919-measurement-lifetime-frontier-20261002.json``. Original failed
native preparation and the exact metadata comparison failure remain retained.
Actual typed measurement-request/export capture is in progress; no production
optimization or replay acceptance follows from the cost envelope alone.

Latest main ``3df650bf7`` (merged #442/#443) is integrated at ``436e49755``.
The incoming BioFormats calibration, MCP streaming and existing publication/
opaque-domain controls pass: 141 tests in 16.72 seconds. The initial narrow
launch failed collection because the MCP test imports the streaming fixture
module by its short name; the corrected command includes that actual fixture
owner first. Both logs are retained in ``/var/tmp``. No source/test guard was
modified to obtain the pass.

The actual IFC capture completed the public pipeline and exact source/dependency
freeze, but its four-snapshot admission remains RED: step22 never invokes
MeasurementsOutputRecorder.record. Only the terminal spreadsheet before/after
graphs were captured (44,935,114 and 56,109,057 bytes), with no graph or budget
rejection. The nine real recorder calls publish identification/filtering/
expansion/relationship core tables. Texture and intensity-distribution tables
use the separate per-object recorder. Thus the proposed capture and the premise
that all outer recording cost is redundant wide-feature conversion are rejected.

Independent export-only qualification passes both unchanged V6 loads (615 arrays
each), exact original CSV bytes, existing strict CP science, and all determining
field/source/array aliases. Thirty-five immutable metadata owners drop their
derived views by their existing declared transport policy; every populated view
matches fresh recomputation from the same fields. Original raw-heap equality
remains RED for that intentionally untransported cache state, separately from
declared-state equality. The actual exporter graph has 31 measurement tables
and two relationship records, with no label pixels; it cannot validate a dense
label-storage optimization. Local diagnostic profiling finds repeated row
identity/axis scanning and assignment; it is not end-to-end speedup evidence.
The ordinary export ceiling is 1.4077 seconds, so export alone cannot save two
seconds. Preserving the native CSV span leaves an optimistic combined outer
recording/export ceiling of 2.4189 seconds; a two-second saving requires about
82.68% collapse. No implementation is admitted by that ceiling alone.
Receipts are ``openhcs-measurement-export-declared-state-profile-20261002`` and
``openhcs-measurement-export-declared-fields-alias-control-20261002.json`` under
``/var/tmp``. The original four-snapshot and raw-heap failures remain retained.


Current-main integration and recording attribution (2026-10-02)
---------------------------------------------------------------

Main was normally merged through 3cb701770 at 6097ec4ff. Independent PR447
merged the source-only CPA metadata repair and closed issue444. Its own
220 controls, original architecture check, public Advanced run and independent
scientific/source-identity comparison are documented in
``cpa-secondary-source-metadata-444.rst``. The larger branch still has open
acceptance gates and remains draft.

The main58ee singleton controls exposed a real prepared-ABI integration bug:
unannotated COMPOSED functions lost their nominal carrier. d4e800a75 derives
that default from the existing consumption declaration while preserving
explicit ndarray/Any/nominal ABI precedence. 136 isolated and249 integrated
controls pass; the original scoped architecture check has zero increases.

A fresh frozen746 Advanced run completed with compilation1.7983s,
execution9.4002s and total12.3852s, default observers and startup excluded.
Its scientific database comparison has zero differences. All90 previously
NULL calibration fields are present;70 match literally and20 native staging
PathName/URL strings are proven to identify the same source files using
same-inode, resolved-source and original native input-inventory SHA checks.
The raw path-string comparison remains separatelyRED. This is one observation,
not a performance benefit: colocalization and one primary identification step
were slower than frozen919, while database export changed1.8378 to1.7538s.

The first nine-recorder cProfile diagnostic is scopeRED. It omitted the
existing monitoring callback thread filter and attributed background sleeps
to arbitrary numeric callers. A separate companion-thread experiment
reproduced the error and confirmed the existing worker-profiling policy
removes it after every profiler enable. No production workaround or duplicate
issue for the already-fixed profiler infrastructure was introduced.

The corrected frozen919 diagnostic has zero foreign sleep/server/poller
events, exact original IFC CSV bytes, and zero scientific differences against
native CP for1800rows. Its disjoint recording attribution is diagnostic only:

================================  ============
Region                            Profile time
================================  ============
Centroid calculation              0.6766s
Sparse relationship row assembly  0.4404s
Repeated axis-domain scans        0.2159s
Other table assembly              0.3644s
Ownership validation              0.000027s
Measurement storage               0.0123s
================================  ============

Centroid-to-IJV conversion is nested within centroid calculation and must not
be added to it. Storage/ownership are immaterial targets for these recording
calls; centroid-only cannot deliver the multi-second goal. Recording plus
nonserialization export remains an optimistic2.4189s ceiling, not a measured
counterfactual improvement.

A real source-born3D diagnostic on isolated8dec failed mask alignment at
step18. It observed300 source births and18 completed producer groups with
no observation errors. RescaledDNA starts with60 correlated physical Z rows;
Resize preserves60planes and changes onlyXY but drops the source domain.
Resize after ImageMath repeats the loss. Source audit identifies bare ndarray
annotations on the public Resize entries despite their shared implementation
requiring metadata/masks. Direct unwrapped tests bypassed this boundary.
Issue450 is formally linked to PR394; truthful RuntimeArrayData declarations,
prepared-contract tests and a fresh production rerun are required. No source
facts are injected into legacy captures, and no3D speedup/parity claim is made.

Retained thread-scope/science receipts:
``/var/tmp/openhcs-nine-recorders-profile-thread-scope-control-20261002.json``,
``/var/tmp/openhcs-nine-recorders-profile-thread-owned-science-20261002.json``
and ``/var/tmp/openhcs-nine-recorders-thread-owned-disjoint-analysis-20261002.json``.
Actual failed3D proof:
``/var/tmp/openhcs-spatial-plane-sourceborn-diagnostic-v2-20261002/observations.json``.


Actual 3D production completion and remaining qualification (2026-10-02)
----------------------------------------------------------------------

The isolated physical-plane prototype at aba4bfaf3 normally incorporates this
branch through424bd2029. Its truthful Resize ABI declarations and prepared
FULL_STACK controls pass438 tests. The actual new production run completes
with no observer errors,780 source-plane births and32 producer groups. Resize
now retains the runtime stack axis and all60 correlated physical rows;
MonolayerMask and the primary input consequently use the existing declared
stack-binding path. The diagnostic controller had required the different
opaque-image fallback's hook. Its original observation gate remains RED;
zero calls to that fallback is not a production failure or evidence of lost
metadata. The actual route is separately adjudicated from retained producer
observations and the existing binding declaration.

Independent unchanged saved-output comparison passes all6 CSVs and120 TIFFs
exactly against the specified retained ordinary reference: headers/cells and
image dtype/shape/pixels. Receipt:
``/var/tmp/openhcs-spatial-plane-aba4-independent-historical-science-20261002.json``.
Diagnostic clocks are compilation2.1216s, execution9.7020s and total12.7136s;
they exclude server startup but do not establish a new performance benefit
or a current native CP ratio. Original R1 passes within its unchanged budget;
original R0 retains the quoted-Iterable finding. Independent actual RGB-volume
controls show identical pixels/masks but incorrect XY metadata in the
prototype: (3,3) instead of the declared channel-aware (2,3). Baseline passes.
The separate 2D RGB mask failure also occurs on baseline and is not claimed
as a new regression.

The decisive route reassessment rejects promotion of the broader physical-Z
prototype. Preserving Resize's runtime stack carrier makes the existing typed
binding sufficient here; the new opaque physical-plane binding has no actual
production consumer in this run. Synthetic controls and successful saved
science do not establish its runtime payoff. Further prototype implementation
is stopped; the next counterfactual applies only truthful carrier declarations
and existing prepared metadata/mask/stack controls to current PR394. Actual
production execution must identify any remaining necessary repair. The
original failed observer gate and the RGB counterexample remain retained;
no source facts are injected and no gate is retroactively called PASS.

PR394 normally incorporates latest main4754fbe2b at2aa930eb2. The added Napari
integration controls pass183 cases and fail the existing offscreen window
width assertion (1260 versus0). The exact isolated assertion also fails on
clean main4754fbe2b with the same values; it remains a separately recorded
inherited gate failure, not a passing full suite. Logs:
``/var/tmp/openhcs-pr394-latest-main4754-napari-controls-20261002.log`` and
``/var/tmp/openhcs-main4754-napari-layout-isolated-20261002.log``.


Qualified narrow carrier repair and fresh native 3D (2026-10-02)
---------------------------------------------------------------

The rejected physical-plane prototype is absent from PR394. Narrow commit
b7640ad61 on isolated main-synchronized2aa930eb2 changes only five geometry
annotations; no numerical body, domain, HoleRemoval or renderer changes.
Nine prepared/FULL_STACK controls establish7 failures before and9 passes
after, preserving typed masks, runtime/opaque domains and source provenance.
The related suite passes148 tests; unchanged original R0/R1 both pass within
their original budgets. Integration fecf3114a has exactly the same production
and test Git trees as the qualified isolated source; only validation prose
differs. The fix is formally carried by PR394 for issue450.

The actual uninstrumented default3D pipeline completes, with exact6CSV and
120TIFF saved science against the same retained reference. All180 actual
source-plane references belong to exactly3 physical TIFFs with indices0..59
and unchanged source-file SHA values. Both fresh native CP4.2.8.1 measured
repeats pass the existing strict6table/150key/2825fact comparison, exact two
logical uint16(60,256,256) label volumes and complete physical-file coverage.
Native comparison to the prototype plus exact prototype/reference/narrow
comparisons establishes transitive narrow parity; no direct narrow/native
comparison is claimed. The original comparison-controller API failure
(tuple subtraction from frozenset) remains RED; a separate recipe supplies
the required frozenset input views without changing any scientific gate.

Fresh current main4754fbe2b also matches the same saved reference exactly.
All clocks below use CPU5 and one thread, with startup/warmup excluded.
OpenHCS includes default OUTCOMES and memory observation; native invocation
includes prepare_run, module execution, post_run and Measurements.close,
and excludes imports/JVM/pipeline loading plus its separate warmup.

=====================  ============  ============  ============
Observation            Compilation   Execution     Total
=====================  ============  ============  ============
Main4754 ordinary      1.6754s       10.0712s       12.4766s
Narrowb764 ordinary    1.6190s       8.3008s        10.7417s
Native measured0       excluded      14.3544s      invocation
Native measured1       excluded      14.4375s      invocation
=====================  ============  ============  ============

The observed main/candidate difference is1.7704s execution and1.7349s total
for the full PR394 plus annotation repair. It is not evidence that the five
annotations alone save that time. One ordinary observation per source does
not establish repeatability or statistical significance. Native's two-run
mean is14.39595s, giving a descriptive1.7343x candidate execution ratio and
1.3402x whole-pipeline ratio under the explicitly different clock scopes.
The target gap remains: reaching2x requires about1.10s further execution
reduction, or3.54s whole-pipeline reduction. No goal completion is claimed.

Receipts:
``/var/tmp/openhcs-geometry-narrow-original-guards-20261002.json``,
``/var/tmp/openhcs-geometry-narrow-b764-3d-ordinary-20261002/observations.json``,
``/var/tmp/openhcs-geometry-narrow-b764-independent-science-and-inputs-20261002.json``,
``/var/tmp/openhcs-main4754-independent-historical-3d-science-20261002.json`` and
``/var/tmp/openhcs-native-3d-aba4-qualification-20261002/fresh-native-scientific-comparison-supplemental.json``.


Four-run 3D comparison and dominant runtime frontier (2026-10-02)
----------------------------------------------------------------

The subsequent A1/B1/B2/A2 ordinary comparison supersedes the single-pair
ratios above. A is frozen clean main4754fbe2b; B is frozen narrowb7640ad61,
including the full PR394 runtime change and five truthful annotations. Each
run uses CPU5, one worker/thread, the unchanged public driver, default OUTCOMES
and memory observation. Mandatory server/library/kernel startup and shutdown
remain outside the pipeline clocks. All four observations preserve exact six
CSV tables and120 TIFFs against the same retained reference, unchanged source
and dependency freezes, and all180 source-plane references to the same three
physical volumes used by fresh native CP.

=======================  ============  ============  ============
Observation              Compilation   Execution     Total
=======================  ============  ============  ============
Main A1                  1.6754s       10.0712s       12.4766s
Candidate B1             1.6190s       8.3008s        10.7417s
Candidate B2             1.7936s       8.7713s        11.3281s
Main A2                  1.6213s       10.0910s       12.4374s
Main mean                1.6484s       10.0811s       12.4570s
Candidate mean           1.7063s       8.5360s        11.0349s
=======================  ============  ============  ============

The descriptive mean reductions are1.5451s execution and1.4221s total.
Native warm invocation mean14.39595s gives1.6865x execution and1.3046x
total ratios under the previously stated clock scopes. Two observations per
source do not establish statistical significance or annotation-only causality.
The remaining2x gap is1.3381s execution and3.8369s total, larger than the
first-pair estimate. The complete independent receipt is
``/var/tmp/openhcs-3d-b764-abba-science-clocks-20261002.json``.

A separate source-pinned diagnostic partitions8.3448s of execution into
4.0497s inside the callable boundary and4.2951s outside it. Callable time
includes decorated metadata/control work, not only numerical kernels. The
exclusive outer terms include stack loading0.5991s, unstacking0.2126s,
saving0.3487s, output identity0.2070s across1680 calls, image recording0.2333s,
CP image requests0.2012s, SaveImages invocation preparation0.3463s, metadata
finalization0.1112s, publication0.4795s and reconciliation0.2812s. These are
diagnostic spans, not accepted speedup measurements; required copying,
validation and I/O remain within them.

The SaveImages preparation span stores memory artifacts and contextualizes
their values; it is not TIFF encoding. Actual artifact materialization has a
separate0.0831s envelope. Saved metadata contains120 SourceArtifactProjection
entries from the two SaveImages outputs. The generic main-flow metadata/VFS
reload branch is not the observed publication route. The actual joint route
is artifact invocation/store, successful materialization metadata, source
artifact projection, serialization, locked publication and reconciliation.

Publication/finalization/identity alone has an optimistic1.0789s ceiling and
is rejected as insufficient to close the current execution gap. The broader
cohort/recording/invocation/publication envelope is3.0201s and requires at
least44.3% collapse before accounting for mandatory work. Existing whole-stack
cache lookup/storage is already below1ms; dictionary tuning or assuming every
input is restacked cannot support the target. The next admission requires an
actual saved joint leaf replay preserving metadata mutation, source correlation,
custom normalization, error ordering and pixel/mask isolation. No new mutable
identity cache or production optimization has yet been admitted by this ceiling.

Diagnostic science and freeze validation:
``/var/tmp/openhcs-narrow450-phase-science-and-freeze-20261002.json``.
Global authority/consumer inventory and corrected route:
``/var/tmp/openhcs-b764-publication-authority-consumer-inventory-20261002.json``
and ``/var/tmp/openhcs-b764-coupled-publication-source-frontier-v2-20261002.json``.

Latest mainb68029c0c is normally merged atc0d78b62e. The initial MCP/agent
integration run passes131 cases and fails both MRO variants of a new cold
feedback fixture. Clean mainb680 reproduces both failures: its reporting thread
can observe published progress before the fake compiler sets its subsequent
``emitted`` marker. This identifies a fixture synchronization race, not a
demonstrated production race. The original candidate and clean-main failures
remain retained. Baseline causal receipt:
``/var/tmp/openhcs-main-b680-cold-feedback-race-baseline-20261002.json``.
Benchmark timings above remain pinned to their actual main4754/narrowb764
sources; the newer MCP merge is not silently included in their evidence.

Test-only integration3317bf9c2 sets the compiler-entry marker before publishing
progress. The actual reporting callback still releases held work; the original
three-second timeout, both cooperative MROs, ContextVar restoration, terminal
ordering and original compiler-error assertions are unchanged. No production
race workaround, retry or longer timeout is introduced. The clean-main repair
passes124 cold-feedback/agent-service controls; integrated PR394 then passes
all133 controls including the narrow prepared geometry ABI tests in13.72s.
Both initial failed runs remain retained. Integrated command, CPU3:

.. code-block:: bash

   env PYTHONDONTWRITEBYTECODE=1 \
     PYTHONPATH=/home/ts/code/projects/openhcs-shared-runtime-plumbing \
     OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 \
     NUMBA_NUM_THREADS=1 CUDA_VISIBLE_DEVICES='' taskset -c 3 \
     /home/ts/code/projects/openhcs/.venv/bin/python -m pytest -q \
     -p no:cacheprovider tests/unit/agent/test_cold_inspection_feedback.py \
     tests/unit/agent/test_agent_services.py \
     tests/unit/test_cellprofiler_geometry_prepared_payload_abi.py

Pass log:
``/var/tmp/openhcs-pr394-main-b680-repaired-integration-controls-20261002.log``.

Saved-leaf rejection and whole-worker diagnostic, 2026-10-02
----------------------------------------------------------

A second source-b764 diagnostic captures the actual contextualization,
normalization scopes, identity-cache preimages, serializer inputs and five
locked publication preimages. All39 admitted snapshots retain their original
metadata, source correlations and alias relations. Exact six CSV/120 TIFF
comparison against the same-head ordinary run and retained historical reference,
all180 physical input references and source/dependency/native freezes pass.
Injected capture work is separately timed; these are not accepted pipeline clocks.
Receipt:
``/var/tmp/openhcs-narrow450-joint-leaf-v3-science-and-freeze-20261002.json``.

An exploratory metadata projection fusion passes the11 captured valid-input
leaf comparisons but saves only4.82ms across the five actual context calls;
normalization has no measured gain. Separately, malformed self spatial-domain
metadata combined with malformed source fallback spacing changes the first
exception. The original reports the spatial-domain failure; the candidate
reports invalid spacing. This is a real correctness failure, independent of a
historical test that observes normalization phase counts. The candidate is
rejected for both inadequate payoff and error-order drift, and is not included
in this branch. Original/candidate replay receipts:
``/var/tmp/openhcs-narrow450-joint-leaf-v3-original-replay-20261002.json`` and
``/var/tmp/openhcs-narrow450-joint-leaf-v3-fusion-replay-20261002.json``.
Malformed-input witness:
``/var/tmp/repro_narrow450_fusion_domain_spacing_order_20261002.py``.

All five original locked publication transactions and both serializer calls
replay with exact ordered JSON results and argument after-state. Original replay
transaction medians sum to0.4646s; the observed callback sum is0.3760s and
lock/read/JSON-write residual0.0872s. Replacing three final transactions with one
would remove only about0.04s of this replay's I/O baseline. Standalone batching
is rejected as insufficient. These are saved-input replay clocks, not an
end-to-end speedup; original on-disk whitespace was not captured. Receipt:
``/var/tmp/openhcs-original-publication-v3-replay-20261002/receipt.json``.

One further actual public-driver diagnostic uses the existing thread-owned
worker profiling policy, with no source edits or diagnostic monkeypatches.
The worker records26,443,742 calls, including5,280 slice-context projections,
25,304 source-metadata merges,55,173 source identity constructions and248 NumPy
stack calls. The next investigation follows repeated whole-image/plane
derivations across loading, invocation, saving and publication. It does not
assume every cache hit copies or every saved plane has independent pixels:
the observed SaveImages named values, VFS planes and cache share pixels, while
the observed Resize output has independent buffers. Profiling increases the
execution clock substantially; profile times must not be scaled into ordinary
costs or reported as benchmark speedups. Exact six CSV/120 TIFF and frozen source,
dependency, native and physical-input comparisons pass. Receipts:
``/var/tmp/openhcs-narrow450-existing-worker-profile-20261002/observations.json``
and
``/var/tmp/openhcs-narrow450-existing-worker-profile-science-and-freeze-20261002.json``.

Main17c630606 is normally merged ata6abc4418. Its new lifetime controls initially
produce140 passes, two SDK failures and one teardown error in the integrated
repository suite. The generated child imports PolyStore before activating the
selected OpenHCS checkout; the intentionally failing synthetic callback also
outlives its test into autouse cleanup. Test-only789e3c304 activates OpenHCS first
and restores the callback owner in a lexical monkeypatch context. Original
failure identity, cooperative close, main-thread checks and repeated-close
assertions remain unchanged. All142 lifetime/cold-feedback/agent-service/prepared
geometry controls then pass in25.24s. This is tracked separately by issue457;
closed issue455's installed production shutdown acceptance is not reopened.
Original RED and repaired logs:
``/var/tmp/openhcs-pr394-main-17c630606-integration-controls-20261002.log`` and
``/var/tmp/openhcs-pr394-main17-lifetime-fixture-repair-controls-20261002.log``.
AST/owner receipt:
``/var/tmp/openhcs-pr394-main17-lifetime-fixture-repair-20261002.json``.

The test-only repair ships independently in merged PR460, commitb495dbb13;
issue457 is formally linked and closed. Its exact clean-main branch passes21
lifetime/stdio/dev-client controls through normal repository conftest collection
in13.21s. Main is normally merged back into this branch at01875a772; the merge
introduces no additional production diff. Clean-main qualification receipt:
``/var/tmp/openhcs-mcp-lifetime-fixture-457-main-qualification-20261002.json``.

The next ownership census uses NRA's ModuleSyntaxIndex and canonical
CompactClassFamilyIndex on all703 OpenHCS production modules and the actual
63 PolyStore,12 python-introspect and6 metaclass-registry modules. All5506
original class declarations remain represented;5493 join canonical family
declarations and13 remain unprojected OPEN. There are no parse errors.
Conditional/function-local binding, omitted numerical dependencies and native
runtime effects remain explicit proof limits. This is source discovery, not
an admitted architecture or equivalence proof. NRA revision0844525ec is pinned.
Receipt:
``/var/tmp/openhcs-b764-shared-derivation-nra-class-census-20261002.json``.

Current-main integration and acceptance findings, 2026-10-02
-----------------------------------------------------------

Main cc9fcdfd4 is normally merged at 133da74ec. The affected native
presentation/MCP, agent-service, resource-lifetime and prepared-geometry suite
passes 150 cases in 17.75s. A separate current-source owner gate passes 73
metadata-owner, live-mutation, provenance-constructor and resolution-snapshot
cases in 1.34s. These scoped gates do not erase the retained broader offscreen
window failure or qualify a new benchmark source. Logs:
``/var/tmp/openhcs-pr394-main-cc9fcdfd4-integration-controls-20261002.log`` and
``/var/tmp/openhcs-pr394-current-maincc9-source-owner-controls-20261002.log``.

The original, unchanged whole-branch R0 is rerun against cc9fcdfd4 and
133da74ec with tool revision 3b03785f4. It exits 1. Its only positive measures
remain source_metadata's one TypeSwitch and three TypeSwitchArms; the removed
virtual_workspace_metadata classifier contributes minus one switch and minus
four arms. The ownership decision retains scalar admission on
SourceMetadataFields and durable rejection on DurableSourceMetadata: the
grammar belongs to the field owner, while canonical runtime spelling and
literal durable spelling remain substitutable policies. Reintroducing the
decoder's duplicate validator or moving the grammar to an unrelated utility
would contradict that ownership. This adjudicates the relocation's architecture;
it does not declare the per-file ratchet passed or alter its implementation,
budget, exclusions or observations. Primitive/subclass admission, reported-class
read ordering, scalar/container precedence, exact errors and mutable lifetime
remain separate behavior obligations covered by the owner controls. Raw report:
``/var/tmp/openhcs-pr394-current-maincc9-original-r0-20261002.log``.

The metadata-only whole-query prototype is rejected immediately after saved
replay: its five captured context calls still take about 55ms, with no matched
speedup demonstrated. Valid saved leaf gates pass, but constructor/subclass,
malformed-input and live-mutation obligations remain unresolved. Neither its
callback-based query abstraction nor its manually replayed constructor effects
are promoted. A separate source trace falsifies wholesale stack-rebuild removal:
23 of 32 loads already hit the whole-stack cache and memory saves retain typed
payload references. The entire load/unstack/save/identity envelope is only
1.3674s before mandatory work, insufficient to close the 1.3381s execution gap.
The next route must span repeated source derivation across existing request,
recording, stack and publication owners. Receipts:
``/var/tmp/openhcs-whole-source-query-exploratory-REJECTED-20261002.json`` and
``/var/tmp/openhcs-b764-whole-cohort-cycle-dominant-route-review-20261002.json``.

Issue 435's fresh public MCP synthetic acceptance is RED on frozen 133da74ec.
The original five processing steps are unchanged; only owned output paths and
the unused required DAPI binding differ. The first attempt stops before runtime
creation because native TCP lock paths do not follow XDG storage. A fresh,
separately retained attempt admits only its declared private data/control lock
paths, completes mandatory preparation and compilation, then fails the fifth
step at the unchanged duplicate source-projection guard. Its exact owned runtime
is closed through the public API and all SDK children are terminal. This is a
real workflow failure that the existing same-occurrence unit fixture did not
cover; installed acceptance remains open. No original biological replay or
performance claim follows from this synthetic check. Source/input/dependency,
native, request/reply and failure evidence:
``/var/tmp/openhcs-derived-role-435-synthetic-acceptance-v2-20261002``.

Current main integration and publication diagnosis, 2026-10-02
-----------------------------------------------------------

Main 283119c42 is normally merged after the declared independent-plane NLM
implementation and its documentation land. The combined affected NLM,
cold-feedback, agent-service, prepared geometry, native presentation and MCP
resource-lifetime controls pass 168 cases in 25.84s. Log:
``/var/tmp/openhcs-pr394-main-283119c42-integration-controls-20261002.log``.
The qualified benchmark sources and clocks above remain unchanged.

The separately retained issue 435 public diagnostic reproduces the original
failure. Four actual projections show two correctly qualified main-flow images
but both retained artifacts address the same unqualified TIFF. The final raw
artifact overwrites the capped artifact. The same-occurrence ownership comparator
is never called: destination matching fails before that comparison. The existing
duplicate guard therefore detects a physical filename collision, not a guard
that should be relaxed. Both observer hooks call their original implementation
once; no capture errors are reported. The exact owned runtime is closed through
the public API and all SDK children are terminal. Receipt:
``/var/tmp/openhcs-derived-role-435-collision-facts-v3-20261002.json``.
An isolated repair on existing materialization-purpose and filename owners is
under review; its local test results do not yet establish public acceptance.

The owned source-field composition prototype is also rejected: the eleven
captured valid leaves and additional mutation/constructor controls agree, but
the five context, three normalization and three identity calls save only 9.24ms
warm or 5.96ms cold. No candidate pipeline qualification or PR is opened for it.
Receipt:
``/var/tmp/openhcs-owned-source-composition-exploratory-REJECTED-20261002.json``.

SaveImages reconstructs two source stacks solely for materialization metadata,
whose downstream consumer reads provenance. Its earlier 0.346s envelope includes
four contextualization children already measured elsewhere. After separating
those children in the retained diagnostics, the residual envelope is only about
0.10--0.114s. This is rejected as a standalone performance route; it cannot be
counted as an independent 0.346s saving. The complete source-query preimage was
not captured, so resulting metadata leaves are not a source-lookup replay.
Read-only audit:
``/var/tmp/openhcs-b764-save-images-artifact-subtree-readonly-audit-20261002.json``.

Automatic image-role repair and public execution, 2026-10-02
----------------------------------------------------------

Commits 0b6c66560 and 2d756646b repair the physical issue 435 collision on
existing owners. Artifact type and materialization purpose supply the retained
role; shared filename identity supplies parser-backed names. MaterializationBatch
binds the original rendering spec onto its existing context, because a public
caller may render a spec different from the compiled plan's default. The original
output plan and source references remain intact. Explicit exports keep their
authored paths. Both scalar and projected retained images preserve physical
coordinates and complete filename suffixes. Missing parsers use the existing
required-parser error policy. Strict projection and path-conflict guards remain
unchanged.

The initial candidate's two actual-purpose mismatch controls fail before this
binding repair. The initial scoped R0 also reports a foreign optional-plan probe;
the corrected owner eliminates that probe without changing the guard. Original
scoped R0 and R1 pass for the complete repair versus 51533665e. Both original
failures are retained. Related controls pass 171 cases; after normal main
283119c42 integration at 053c9d445, 183 affected controls pass. An attempted
unrelated Torch NLM control stops at collection because Torch is absent; that
failure remains separate and no dependency changes follow. Handoff:
``/var/tmp/openhcs-automatic-image-role-435-reviewed-handoff-20261002.json``.

The clean frozen 053c9d445 source completes public MCP startup preparation,
compilation and all five original processing steps. The output contains exactly
the two distinct qualified role TIFFs and two matching source-projection rows.
The fourth journey then stops at its inspection assertion: the API reports
PARTIAL with the sole missing-grid warning, because the synthetic declaration
does not supply plate grid dimensions. This original whole-journey RED is
retained; it is not a pixel-comparison failure or a completed fresh-process
readback acceptance. The runtime and all SDK children are terminal. Receipt:
``/var/tmp/openhcs-derived-role-435-synthetic-acceptance-v4-20261002/journey.json``.
Supplemental public inventory, complete pixel and fresh-process checks remain
pending on these unchanged outputs.

The reviewed source is normally integrated into PR394 at fa694eb56. Its affected
current NLM, cold-feedback, agent-service, prepared geometry, native presentation,
MCP lifetime and new role controls pass 194 cases in 20.43s. Log:
``/var/tmp/openhcs-pr394-automatic-role-435-current-integration-controls-20261002.log``.
Neither this bug repair nor its public synthetic run establishes a performance
gain. Accepted benchmark clocks remain pinned to main4754 and candidateb764.

The global runtime reassessment finds no sufficient measured optimization route
yet. Removing 485 provenance births and 485 identity births in captured context
leaves already saved only 4.82ms and changed malformed-input ordering. The next
candidate must remove whole repeated projection/adapter transactions, rather
than another constructor or field-query leaf. The strongest remaining joint
frontier is 3.0201s with incomplete whole-lane replay coverage; counts from the
instrumented profile cannot establish its reducible fraction. Audit and smallest
missing capture recipe:
``/var/tmp/openhcs-b764-whole-lifecycle-architecture-reassessment-20261002.json``.

Issue 435 supplemental public readback passes on the unchanged V4 output. Two
fresh SDK processes expose identical complete inventory, sample and projection
facts. Both 1024-by-1024 float32 role images pass the unchanged existing CP pixel
comparison with zero out-of-tolerance pixels: raw maximum difference is zero;
capped maximum difference is 1.1920928955078125e-7 under atol=rtol=1e-6. Both
roles retain physical C2 and calibration within the existing inspection spacing
tolerance of 1e-12. The original controller, journey, inputs, source, dependencies,
native binaries and all physical output hashes remain unchanged, and both reader
children exit zero. The original V4 journey remains RED. The supplemental
inspection check follows the existing status policy, retaining PARTIAL for the
sole undeclared-grid warning without fabricating grid metadata; spacing uses the
existing inspection tolerance rather than literal equality after TIFF formatting.
This is synthetic source qualification, not original biological or installed-root
acceptance. Supplemental receipt:
``/var/tmp/openhcs-derived-role-435-v4-readback-supplement-20261002/receipt.json``
(SHA256 4f0f0550e50aaff297d134ee5accf2b2da01297305394a155fe79e827b844fdf).

Current source qualification and workload priority, 2026-10-02
------------------------------------------------------------

Main 142196857 (callable documentation ownership) is normally merged at
9aa3918d2. The affected declared-documentation, agent-service, cold-feedback,
automatic-image-role and plane-NLM integration controls pass 170 cases in
14.77s. Log:
``/var/tmp/openhcs-pr394-main142-documentation-role-integration-controls-20261002.log``.

A clean frozen 9aa3918d2 ordinary public-driver observation completes one CPU5
inline worker/thread with compilation 2.103262s, execution 7.870635s and total
10.781240s. Server/library/kernel startup and shutdown remain outside pipeline
clocks. All six CSVs, 120 TIFFs, 180 disk projection references and three source
volume hashes agree exactly with the retained qualified reference and b764
output; source, dependencies, interpreter and native binaries remain unchanged.
Native science is transitive through that exact reference. This single current
observation does not replace the earlier repeated ABBA comparison or establish
a new optimization gain. Receipt:
``/var/tmp/openhcs-pr394-role-qualified-3d-science-20261002.json``.

The descriptive comparison against the two retained warm native 3D observations
(mean 14.395949s) is 1.829x execution and 1.335x total. 3D is weakest among the
three qualified representatives (3D, Advanced and IFC), whose OpenHCS revisions
differ. The global weakest case remains unknown: all30 cached native clocks
include subprocess startup and the older multicore CP scaling baseline is
projected. Historical WoundHealing, TrackObjects and worm cases require current
matched warm-native qualification before ranking the whole catalog. Receipt:
``/var/tmp/openhcs-current-native-workload-priority-revalidation-20261002.json``.

The next whole-transaction diagnostic is rejected before launch when its saved
representative identity pairs predict 2,719,141,800 bytes for three 60-request
cohorts alone, exceeding the transport's 1GiB root budget. No pipeline is run
for V4 and none of its frozen files are changed. This prediction is not an
observed complete production roster. A saved grouped-graph experiment reduces
those three representative graphs to 81,450,818 bytes while preserving actual
saved payloads; cache subsets contain no arrays. A separate V5 preparation
must capture actual ordered requests and detached pre/post cache states before
its replay or a performance candidate can be admitted. Receipts:
``/var/tmp/openhcs-whole-cohort-v4-budget-preflight-REJECTED-20261002.json`` and
``/var/tmp/openhcs-grouped-identity-budget-saved-experiment-v3-20261002/receipt.json``.

Fresh native qualification changes the primary target
---------------------------------------------------

Four additional ordinary current9aa cases now have matched source inventories
and actual warm native runs. Each native case excludes one warmup and retains
both measured repetitions. OpenHCS uses one CPU5 inline worker/thread, mandatory
READY warmup before compilation, the default OUTCOMES observer and memory policy.
Server startup and shutdown are excluded. The following ratios are descriptive:
one OpenHCS observation against the mean of two native observations, not a
repeated A/B optimization claim. Native time includes preparation, modules,
post-run and measurement closure, excluding imports, JVM startup and pipeline
loading; OpenHCS total includes compilation.

.. list-table:: Current single-worker observations, seconds
   :header-rows: 1

   * - Case
     - OpenHCS execution
     - OpenHCS total
     - Native mean
     - Execution speedup
     - Total speedup
   * - WoundHealing
     - 3.571737
     - 4.096850
     - 3.779188
     - 1.058x
     - 0.922x
   * - TrackObjects
     - 5.036489
     - 6.400329
     - 8.276148
     - 1.643x
     - 1.293x
   * - UntangleWorms
     - 2.194352
     - 3.206172
     - 2.974680
     - 1.356x
     - 0.928x
   * - UntangleWormsBrightField
     - 3.064656
     - 4.264850
     - 6.152021
     - 2.007x
     - 1.443x

All eight comparisons pass the existing measurement/schema/discrete gate and
unchanged numeric tolerances. WoundHealing and BrightField also pass complete
saved-output science. TrackObjects and UntangleWorms fail saved-image content
comparison in both repetitions; their ratios therefore have measurement-only
qualification. Physical output inventories match. All original RED receipts
remain unchanged. TrackObjects saves 21 three-panel PNGs: original-image and
outline panels agree exactly, while the tracked-object panels are gray instead
of the native colored labels and white IDs. The current callable deletes the
requested saved-image options and returns its unchanged input image. Worm
images have matching backgrounds and colors but 96 differing outline pixels
across two outputs. Sparse-overlap rendering is a candidate cause requiring
actual producer inputs, not a proved segmentation diagnosis.

WoundHealing is weakest among seven retained representative measurement-science
scopes, replacing 3D as the primary investigation. This is not a full-catalog
ranking. WoundHealing needs about 1.682142s execution reduction and 2.207256s
total reduction to reach twice its native throughput. Its native comparison
uses exactly two selected 2304-by-1536 RGB JPGs; TrackObjects uses all 21 selected
sequence frames, and both worm cases retain their actual source bindings and
training inputs. Source, dependencies, interpreter, native binaries and all
original inputs are frozen before and after. Evidence:
``/var/tmp/openhcs-current-slowcase-priority-and-png-audit-20261002.json``
(SHA256 c84d5c0f39bf2a246e00eb7cbb42a7457849efb6a974a6d78fee0e68c6c270ef).

The existing worker-owned profile on current9aa WoundHealing preserves exact
ordinary CSV outputs. It attributes 0.604904s to 22 runtime stack operations,
0.551025s to 16 image normalizations, 0.288266s to two centroid queries and
0.464524s to two color reductions. These profile durations are diagnostic costs,
not measured savings. Metadata composition itself is only 0.016512s. Source
recording's 0.251105s overlaps normalization and must not be added to it. Even
eliminating stacking, normalization and centroid costs entirely gives an
optimistic 1.444195s, below the execution gap before mandatory copies. Another
small metadata leaf is rejected as a sufficient route. Receipt:
``/var/tmp/openhcs-current9aa-wound-profile-dominant-frontier-20261002.json``.

The bounded actual-input normalization capture completes successfully: all 16
calls are recorded, with two unchanged V6 before/after graph pairs for the
large integer arrivals. Both consume the same two-frame uint8 RGB stack,
shape (2, 1536, 2304, 3), scale 255 and float32 target. Original input pixels
and public metadata remain unchanged; source/environment/native freezes pass.
Capture clocks are not performance evidence. Independent whole-output science
and original-leaf replay remain separate gates. Receipt:
``/var/tmp/openhcs-wound-intensity-leaf-capture-v1-20261002/observations.json``.
The generic consumer investigation must preserve exact compiled artifact
selection, source projection and stack-broadcast laws; raw integer pixels cannot
be relabeled as normalized unit-interval pixels to avoid a conversion.

The former 3D grouped-cohort V5 diagnostic remains prepared and unlaunched after
this priority change. No rejected route is promoted because its preparation is
already complete. The tracking renderer is being investigated in an independent
main142 worktree with actual 21-frame producer inputs and exact native panel
replay; no saved-image repair is included or claimed here yet.

Library readiness repair and latest qualification, 2026-10-02
------------------------------------------------------------

Main 3f955d3fb (MCP sampling) and cf5a83f89 (fixture CLI repair) are normally
merged. The MCP/prepared-geometry/automatic-role integration gate records 354
passes and nine failures. All nine fail identically on clean main3f955 with the
same readonly native-binary bindings: eight fixture declarations omit the
required server, and one expected stream-argument mapping omits display_config.
The first clean-main attempt refused a missing native extension at collection;
that original failure is retained before the exact-bound native supplement.
These are existing fixture failures, not a passing full suite. Numerical and
dependency sources are unchanged by the fixture-CLI merge.

The actual Illumination3 first run reached an unprepared masked polynomial
specialization. Its Numba artifacts were written inside the measured polynomial
step: 0.526s versus 0.016s when already cached. The existing callable preparation
hook now prepares masked/unmasked and readonly canonical image/mask signatures
before READY. A fresh-cache subprocess forbids all later compilation and cache
loads across 36 dtype/layout/mutability/mask combinations and verifies an
independent polynomial oracle, input isolation and geometry errors. Twenty
preparation/fitted-illumination controls pass, with two existing skips. The fix
ships independently in merged PR474, formally closing issue473; original R0
passes all three roots and original R1 passes its unchanged 160-second budget.
Main a6c18f054 is normally merged back into this branch. Its full receipt is
``docs/validation/polynomial-library-readiness-473-20261002.rst``.

The clean frozen integrated source54708367b has fresh ordinary CPU5 one-worker,
one-thread observations using the existing cache, default OUTCOMES observer and
default memory policy:

.. list-table:: Fresh post-repair observations, seconds
   :header-rows: 1

   * - Case
     - Compilation
     - Execution
     - Pipeline total
   * - Illumination3
     - 0.962373
     - 0.647611
     - 1.961545
   * - WoundHealing
     - 0.346341
     - 3.916717
     - 4.575604

Startup/library/kernel preparation and shutdown remain outside pipeline clocks.
These are single observations, with no matched repair speedup or statistical
regression claim. Wound is slower than its retained earlier single observation;
that result is preserved rather than substituting the better sample. Both
authored Illumination3 NPY images and Wound's complete two-row Image.csv agree
byte-for-byte with the qualified unchanged references. Existing complete saved
inventory and CP-tolerance comparison gates pass. Native science is transitive
through those fully qualified references. The first validator incorrectly
expected two Wound tables rather than two rows; its failure remains retained,
and the V2 supplement checks the actual authored inventory without changing any
production comparison policy. Source, dependencies, interpreter, native binaries
and all inputs remain frozen. Receipt:
``/var/tmp/openhcs-pr394-masked-prewarm-ordinary-science-v2-20261002.json``
(SHA256 21231dffa14dbe17bf824a4258f677e7d656122036da81e0b3d8c9c8bc2f9c02).

Additional native qualification and remaining execution frontier
---------------------------------------------------------------

Current9aa Vitra uses one selected joined source set containing all four physical
resources, rather than two channel-derived image sets. Its two warm native
repetitions average 3.044868s; OpenHCS is 1.615775s execution and 2.908514s total.
Complete saved science passes for 2,233 table rows and its authored image in both
native repetitions. Earlier source-set controller refusals remain retained.
Receipt:
``/var/tmp/openhcs-current-vitra-native-timing-science-v3-20261002.json``.

Illumination3's two warm native repetitions average 0.603076s. Its authored
pipeline saves two NPY images and no CSV. Complete existing inventory and image
science pass in both repetitions. The retained first OpenHCS observation is
1.309110s execution and 2.603767s total, containing the late polynomial
specialization described above; the fresh post-repair observation is recorded
separately. Cache-state differences prevent treating these as a matched repair
speedup. The global weakest full-catalog case remains unknown. Receipt:
``/var/tmp/openhcs-current-illumination3-native-timing-science-v1-20261002.json``.

Wound's actual worker profile partitions 3.387111s into 1.536850s of disjoint raw
processing and 1.850261s of other runtime/recording work. The 22 stack operations
include 0.4036s in 16 aggregate image stacks, 0.1481s in object variants, 0.0538s
in main-flow/cache and 0.0023s in initial loading. Ten source-record
normalizations account for 0.2436s of the 0.5510s normalization envelope. These
are profiled costs and overlap the earlier source-query attribution; none are
accepted saved seconds.

Actual Wound ON_DEMAND QA images are not forced by terminal OUTCOMES publication.
However, raw QA planes borrow object-variant pixels and shared validity masks;
their current aggregates establish independent mutable artifact buffers.
Deferral with equivalent eager per-plane copies cannot remove those copy bytes,
and zero-copy adoption without an ownership/lifetime proof is unsound. Existing
ArrayBridge geometry validation also forces concrete arrays at payload
construction. No lazy wrapper or second mutable identity cache is promoted.
The global AST owner/lifetime audit retains a bounded actual alias-capture plan:
``/var/tmp/openhcs-current9aa-wound-copy-lifetime-reassessment-20261002.json``.

An external shared-geometry convex prototype preserves both actual saved input
graphs exactly. The outer 256-level call's warm local median changes from
0.260906s to 0.023542s, saving 0.237364s; the nested 16-level call overlaps it
and is never added as independent work. This is useful local evidence, not a
production pipeline gain. The nominal owner audit identifies existing shared
column-envelope and Bresenham authorities and a disconnected 15-kernel legacy
component; production migration and end-to-end qualification remain separate.
The shared dense-coordinate prototype also has exact actual Wound/Track input
replays and passing scoped R0/R1 after removing duplicated admission logic.
Its pre-domain allocation behavior for very sparse large label IDs remains
under review. Neither prototype is integrated here or counted as a speedup.

Independent tracking PR468 is synced to main and passes 19 focused tests plus
unchanged scoped R0/R1. It remains draft: native saved-image differences shrink
from 77,726 to 3,340 text pixels, but full native PNG parity is still RED. It
formally links issue467. No parity gate, tolerance, scientific output or renderer
environment is weakened, and no tracking repair is included in this branch.

Remaining acceptance still includes installed-root issue419 IPO/Shape and
Morph/DISTANCE consumers; issue433's original 13.36GB OOM allocation owner and
repeated READY behavior; installed-root issue435; and issue450's installed
prepared-Resize consumer. The original whole-branch scalar-classifier R0 RED
remains separately retained. These draft closing references do not establish
completion. Full native scaling, all30 benchmark reruns and fresh figures remain
outstanding, and the long-running performance goal stays active.

Shared geometry release and coordinate-owner checkpoint
------------------------------------------------------

Main ``5b7f3c48d89da4415de001375d0e06de881153c9`` is normally merged.
Independent PR476 ships the shared quantized hull/Bresenham geometry and
officially closes issue475. Earlier hull issues158/268 and PR161 remain
completed. The full-source PR394 ABBA comparison pins eb2 versus b470:
BrightField total4.635292249 ->3.294145465s, Untangle3.234328632 ->2.311149861s,
Illumination1.988957128 ->1.892348221s. All16 complete saved outputs pass exact
science and source/env/native/input freezes. Wound is a variance control, not
an attributed hull saving. See the committed shared-quantized-hull report for
every sample, readiness/source guards and retained native-image RED.

The existing object-label storage family now owns the single shared dense
coordinate reducer. Tracking and relationships inherit/use its primitive;
two duplicate kernels are removed. Resource/domain-effect and C/F/A readiness
controls pass. Isolated100 and integrated101 tests pass, both with2 existing
skips; original scoped R0/R1 pass unchanged against eb2. Frozen b470 versus
6e69 ordinary ABBA Wound total3.866369809 ->3.562642806s; Track execution
5.338271976 ->5.052027345s, but total6.629491309 ->6.684317434s regresses
with higher compilation. All8 full saved outputs/freeze gates pass. The separate
shared-dense-coordinate report retains all samples, no causal late-JIT claim
and the original tracking image RED. No reduction resolves issue433's original
allocation owner or the whole-branch scalar-classifier R0 RED.

Owner WT remains /home/ts/code/projects/openhcs-shared-runtime-plumbing. All
production edits are committed here. Agent-owned implementation branches are
integrated; no additional unpublished production files are claimed. Frozen
benchmark WTs remain unchanged. Compared with receiving checkpoint eb2, new
production edits are precisely three CP geometry/illumination modules plus
core/runtime_object_labels.py and four CP backend/preparation/tracking/
relationships modules. These are indirect numerical/coordinate and preparation
changes beyond the receiving review's original four-file eb2/wheel delta.
Installed receiving obligations419/433/435/450, whole-branch R0, full native
image parity, full-catalog/scaling and figures remain open. A first-wave fresh
four-case ordinary/native qualification is in progress, not a completed gate.

Library readiness and saved-reader checkpoint, 2026-10-02
-------------------------------------------------------

Main ``b4405ff3541add6b91004002b7d6f389f1208636`` is normally merged.
Independent PR482 closes issue477 and PR486 closes issue481. Main's singleton
invocation fix passes 401 controls and original scoped R0/R1; its actual public
translocation observation is 1.679128s execution / 3.094840s total / 1.008657s
compilation. Both saved warm native repetitions pass full database, schema,
discrete and numerical measurements, properties, exact image and physical
inventory gates. This single main-based observation is not a measured gain.
Receipt: /var/tmp/openhcs-singleton-label-main-477-saved-native-science-20261002.json
(SHA256 5c5c4c497df1ee4b115aba42650941f451fac3ae3f784cfcfe3144e0ae94d6ac).

Issue481 prepares canonical masked float32/float64 declumping signatures through
the existing morphology backend library lifecycle. Numerical bodies are
unchanged. Eight isolated controls and original scoped R0/R1 pass; cold and
disk-cache witnesses reject subsequent compilation or cache loading. Frozen
integrated ``adef79b4ff3825b35a41ef96b60f3bc421a5ddd5`` Speckles execution is
1.915174s, total 3.212164s, compilation 0.959121s. No kernel-cache writes occur
inside execution. All three scientific CSVs match the original fully native
qualified output exactly, with complete inventory and freezes. This necessary
readiness repair does not establish a speedup. Receipt:
/var/tmp/openhcs-pr394-morphology-ready-speckles-science-20261002.json
(SHA256 29526b6c5c37bbd840c706393b9290695894bc80a2247aedc7c718cb58ee5477).

Issue479's saved relationship reader is integrated from ``2de4e021f``. It
validates directed edge declarations, object/image domains, reverse pairs and
redundant Parent/Children fields before using scalar projections. Saved
snapshots and cache transport retain endpoint correlations; typed value-only
snapshots explicitly retain UNKNOWN evidence. Both-root scoped R0 passes,
but original R1 remains RED for an unchanged validator's relocation (+1 core,
-1 interop, zero global type-check change). This is not all-guards admission.
The merged-parent controls pass 380; root integration passes 235.

Corrected saved Beginner replay uses the actual complete output root. Both
native repetitions have exact two-image agreement, complete physical-file
coverage and five matching correlation keys / 2,093 directed pairs. Full
measurement parity remains RED: 80 extra Costes features and 63 missing Nuclei
child-mean features. The earlier helper's incorrect results-directory root and
missing-image report are rejected, retained harness evidence. Reader receipt:
/var/tmp/openhcs-relationship-479-full-saved-replay-v2-20261002/receipt.json.

Issue487 isolates the first loss for unwanted Costes work: existing settings
postprocessing treats legacy Run all metrics=Accurate as true and overwrites
the five authored flags. Native CellProfiler uses this aggregate setting only
for UI visibility, including when Yes; individual choices remain authoritative.
The correct existing owner is ModuleOnlySettingBinding, with the obsolete
runtime override removed. Public-importer RED and native/global AST census are
retained. Qualification is in progress. Colocalization's ordinary 2.514475s
inclusive step cost inside 6.424050s execution is an upper bound, not measured
Costes-exclusive work or a promised saving. The separate 63 missing means
still require first-loss evidence. No numerical tolerance or parity gate changes.

Compiler profiling confirms repeated effective-configuration construction and
cold schema analysis, but its timings overlap and are diagnostic only. A
private prototype is not admitted: default-factory/callback and mutable-state
laws remain unproved. This route is deferred while the larger unauthorized
metric execution is qualified. Full scaling and fresh figures remain pending;
the long-running optimization goal remains active.

Requested CPA workspace production qualification
------------------------------------------------

Issue480 is integrated at ``38d02e20a795ad6f8c6457459c380995a798d0fe``.
The existing export settings retain authored workspace requests and panels;
nominal tool/axis leaves own the irreducible external grammar and derive
columns from the existing CPA dialect. The discarded settings validator is
removed. Publication uses the same existing export bundle/materialization
path. Full physical-file admission now consumes paths actually read by the
existing CPA equivalence report, instead of a manually synchronized suffix
roster. Unmatched files and failed readers cannot claim coverage.

Original scoped R0 across all three roots and original R1 pass against2560;
138 agent controls and 81 root integration controls pass. An actual ordinary
QualityControl public run on clean, sealed38d observes 0.652361870s execution,
2.120112958s total and 1.088341713s compilation. Startup/readiness and shutdown
are excluded. No diagnostic hooks are installed. Both immutable saved native
repetitions pass database/schema/discrete/numerical measurements, nonempty
declared two-row Image table, requested workspace meaning, every physical
output and all source/input/dependency/native/controller freezes. This is a
correctness qualification, not a paired performance gain. The original V4
missing-workspace inventory RED is retained unchanged.

Complete receipt:
/var/tmp/openhcs-cpa-workspace-480-integrated-saved-native-v1-20261002.json
SHA256 72e22c3859081de0494ad24440d36a54b306adbaa509d8afcb9db87d671ece5d.
Ordinary source-freeze SHA256:
317de6735208ed9c99149d81296bf40dd3c1e70823e198da69b7cb7575d47e5d.
Standalone main isolation and its independent source checks are in progress;
the integrated result does not claim a main-only benchmark.

The actual before-fix Beginner observation on frozen4904884 is execution
6.981277943s, total9.296563831s, compilation1.451889992s. It intentionally
preserves the reproduced issue487 metric bug and missing63parentmeans; no
parity exemption or speedup is claimed. Controller/source/environment/native
and complete actual input freezes pass. Source-freeze SHA256:
dc8a40519a10b7dd13ba9809a95bd6e2070622a326afa66ee2684adbe892a28d.
Issue487's source fix passes156 controls and original scoped R0/R1, but actual
candidate pipeline science and paired ordinary timing remain outstanding.

Metric policy, saved parity and readiness follow-up, 2026-10-02
-------------------------------------------------------------

Main3705c071b13c29d354417d85dccf78c765b4a580 is normally merged at05ea538a.
Independent PR488 closes480 and PR489 closes487. Their production changes
are already integrated; subsequent main synchronization changes documentation
only. PR489 passes156 controls and original scoped R0/R1. Existing metric
declarations now derive enabled output columns; disabled Costes computations
and columns are omitted without changing enabled numerical implementations.

Frozen baseline4904884 and sealed candidate d567d4d7 each have two cached
ordinary observations. Baseline execution5.527808428/5.327760458s and total
7.723725582/7.677667536s compare with candidate execution4.583703041/
4.648376942s and total6.814110309/6.839743058s. Means improve execution
5.427784443 to4.616039992s (0.811744451s) and total7.700696559 to6.826926684s
(0.873769875s). Startup/readiness and shutdown are excluded; one worker
executes inline, with ordinary OUTCOMES and memory observation enabled.
This is a full-branch cached comparison, not an exclusive Costes attribution,
ABBA experiment, statistical claim or fully prewarmed qualification.

The original baseline6.981277943/9.296563831s is excluded from that comparison:
three kernel overloads were written inside its pipeline timing window. The
later runs have no cache writes, which does not prove absence of cache loads.
Existing public library preparation omits object correlation and prepares
float64 threshold/RWC arrays; canonical runtime stages require float32 arrays.
A fresh private-cache public-preparation probe refuses later compilation and
cache loading: base passes; correlation, threshold and RWC fail. Requested
argument types exactly match retained production cache signatures. This is
readiness evidence using lawful synthetic values, not actual-input science
or performance evidence. Issue491 tracks canonical-stage preparation.

All seven common CSV domains and two images are unchanged;100 unauthorized
Costes columns disappear (80 canonical and20 derived parent columns).
Candidate repeat scientific bytes are exact. Complete saved native replay
still fails solely for63 missing parent-mean features in both repetitions,
with no Costes, image, other numeric or physical-inventory differences. All
five relationship correlation keys and2093 pairs agree. Numerical tolerances
and required outputs are unchanged; full-case native parity remains RED.

Issue492 identifies its first loss: all16 object-intensity tables exist, and
the producer has channel groups1/2/5/3, but compilation selects only child
channel3 for the prior-measurement input. Other channels never reach runtime
scope filtering. Repair belongs to the existing artifact relation/projection
contracts and must preserve child subject and image-set correlation. It adds
required scientific work; no speedup is claimed for this correctness repair.

The bounded joint diagnostic pipeline succeeds with exact scientific bytes,
but capture admission is RED: no batch arrays are captured, and one final
store metadata event exceeds the4MiB cap. Earlier complete selection events
establish the bounded first-loss fact. The worker profile reaches28 serial
measurement invocations and zero batch calls; the earlier assumed batch
capture route is invalidated. A narrower serial-owner capture and nominal
batch-executor transport audit are next, not a claimed admitted replay.

Cached comparison receipt:
/var/tmp/openhcs-beginner-metric-487-ordinary-cached-comparison-v1-20261002.json
SHA25636883d131c224f20b44139b02078c6ddba8b78a2e598901651910e12a92e4c2b.
Strict saved native receipt:
/var/tmp/openhcs-beginner-metric-487-strict-native-science-v1-20261002/receipt.json.
Fresh READY probe:
/var/tmp/openhcs-colocalization-public-ready-signatures-v2-20261002/observations.json.
Parent-mean first-loss receipt:
/var/tmp/openhcs-beginner-parent-means-first-loss-v2-20261002.json
SHA256c127ff3c79d82ddad4df38bb197606a25ee44a934e1909759922fc62b560f135.
Joint diagnostic admission/science receipt:
/var/tmp/issue487-joint-v2-original-admission-and-science-20261002.json
SHA256b29d5df0cd203e40a6e7f018e59b42d91e815a21af3e623811bc6b87a00ae53e.

Whole-branch scalar-classifier R0 and issue479 validator-relocation R1 remain
RED. Installed419/433/435/450, original native image differences, full30-case
and scaling reruns and fresh figures remain open. The optimization goal stays
active; these measured gains do not redefine or complete the target.

Canonical READY and current generic-query frontier
-------------------------------------------------

PR493 is merged on mainb85f1e4add6075a71f4fd4e5ba7e2512e48990e5 and
closes491. Root normally integrates it atb015526c7c491abf80ea0958a08eb8723131c152.
Canonical image/object stages replace the duplicate kernel list and threshold
arithmetic.23 focused controls and original three-root R0/R1 pass; the actual
root fresh-cache integration control passes1test/9.86s. Compilation and disk
cache loading are refused after public preparation across IMAGE/OBJECT/BOTH
and threshold/Costes option states. This establishes readiness, not a speedup.

One source-pinned Beginner diagnostic on clean b015 completes with exactly one
existing worker profile, nonempty existing runtime events,108 actual CP
executor calls,133 declared callable calls and no diagnostic errors. Profile
and event files occupy1.19MiB. Ten prelaunch controls preserve original calls,
errors, alias/mutation, descriptor/loader and thread partition behavior. The
instrumented12.9997s execution/15.2588s total is not an ordinary benchmark or
a regression. Profiling overhead is substantial and nonuniform.

The same-thread orchestrator region partitions exactly12.988882s. This region
omits prior source/config decode; it is not the complete server-job clock.
Disjoint instrumented exclusive costs include module-output recording4.918576s,
declared callable invocations2.300491s, stack loading1.007764s, per-object output
recording0.920284s and worker residual0.861094s. cProfile costs overlap these
regions and must not be added or scaled to ordinary clocks.

The determining generic query path makes312 full-column queries directly from
upstream parent-mean derivation:803488 structural-missing checks and195808
qualification calls within those queries. Whole-worker structural checks are
1187866. Qualification precedes feature/source/row/object selection. Issue496
tracks an operation-local schema/index fold on the existing nominal owners.
Opaque callback order, errors and mutation must remain observable; explicit
NaN propagation differs from default finite-value qualification. No new cache,
callback-identity dispatch or per-Relate numerical optimization is admitted.

Strict replay of this diagnostic retains exactly63 missing parent means in both
saved native repetitions, with zero other numeric, image or inventory failures.
All seven CSVs/two TIFFs are byte-identical to ordinary candidated567; full
physical inventories agree and five correlation keys/2093pairs match. Source,
outputs, inputs, native and dependencies remain unchanged through replay.
Final all-zero science assertion correctly fails: no63-feature waiver exists.
Receipt /var/tmp/openhcs-current-generic-job-profile-strict-native-science-v1-20261002/receipt.json
SHA256bbc135e6de97628ddbabe8d350381a76a8af3000b4fba28f19e1879c27a220a8.

Saved CSV readers cannot reconstruct preexport long rows, structural padding,
explicit missing cells, ownership or query order. That route is rejected;
metadata/relationship reader-domain errors are harness counterevidence, not
science failures. A bounded post492 actual logical-column/query capture must
demonstrate material absolute payoff before production optimization. The prior
ordinary Relate span near0.8s is only a whole-operation ceiling; the corrected
four-channel frontier and transfer remain unmeasured.

Independent client residual evidence is0.818/0.804s for cached Beginner and
0.379s for QC. Two submissions occupy0.367/0.368s and0.120s respectively;
waiting beyond server clocks occupies0.03-0.08s. Four pipeline renders and
three config renders are observed in source, but their exact elapsed and byte
equality remain unproved. Blind memoization is rejected because shallow-frozen
documents contain mutable steps. This client-only route cannot remove server
execution work or independently close the seconds-wide target gap.

Issue492's prepared four-channel/two-site repair passes its original controls
and guards. New prerequisite495 proves complete dynamic queries previously
ignored compiled producer path/backend, allowing foreign locations or an
ambiguous retained producer after legal rebinding. Existing planned query and
location authorities own the repair and point-in-time address law. Combined
qualification and actual full native63-field acceptance remain pending.

The shared /home filesystem temporarily blocked Git commits. Only the owned
mutable worktree's website projection was made sparse through standard Git;
all75 website files were first preserved byte-exact at
/var/tmp/openhcs-owned-runtime-website-sparse-preserved-20261002/website with
their manifest receipt. Git objects retain the same files. This freed27MiB;
canonical ROOT, source code, benchmark inputs/outputs, dependencies and shared
caches were untouched. Earlier b015 source freezes completed before this
projection change; future freezes must explicitly record the sparse website.
All remaining acceptance and full-catalog/scaling/figure obligations stay open.
