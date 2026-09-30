# R0 working guardrails checkpoint

Latest integrated base: OpenHCS main `fb5fea4f1aa7cc4f195d25a0122b13ded4ffde16`
(merged PR205 and PR259), normally integrated here after scanner termination.
Original checks below name their older tested bases. R0 owner: Lovelace, PR263.
Read OWNER-OVERRIDES first: hosted CI waiting is deferred, not local evidence.

## Owners and crossings

Checked current OWNERSHIP, the agent registry, and open OpenHCS PRs before
workflow edits. No competing R0 implementation claim was found. The broader
archive/refactoring agent remains unidentified; coordination is not confirmed.
Write set: the new guardrail workflow, parity scope/status wiring in the existing
integration workflow, PR template, R1 policy consumer, focused CI tests, and this
planning receipt. No production or installed source edits. PR256 remains separate.
Tool tests now live in `.github/tests`, selected unconditionally by the R1 job,
so normal application test collection does not acquire NRA as a new dependency.

PR259 `5c1adc9c6` was reviewed against `c86f562e`: callable ABI projection belongs
to CallableContract and ProcessingContractDeclaration; PURE2D retains the plane
carrier until slicing, and the existing registry projects the raw argument at
invocation. The label carrier extends the existing output strategy family and
shares SourceImageObjectLabelBuildRequest with NumPy output. Crossings: S4
callable ABI, S6 runtime context, S2/S5 processing-contract invocation. No new
registry, ndim/squeeze branch, or default metadata was introduced. This is source
ownership review, not a rerun of the landed repair. Socrates owns PR262/257/264
materialization; Zeno owns PR205 measurement; parent owns installation/live checks.

## Mechanisms and concrete pattern review

- AGENT-8, IMPL-12: use the packaged agent-comms ratchet, not copied AST measures.
  Pin `3b03785f45df2ef5dc62ba6aed99294192ecbb01`. C0/PR180 and the subsequent
  ratchet closure PR347 are merged. The current package exposes dispatch subjects,
  dispatch arms, boolean terms, foreign probes, codecs and class excess above500.
  Its declarations own measurement. A new measure requires no OpenHCS detector.
- BOUND-1/2, MEMB-4: R1 consumes NRA's actual RedundantTypeCheckDetector,
  UnmodeledRecordShapeDetector, schema inventory and missing-descent certificates.
  Mapping reads are selected by NRA's PresentationProjectionKind and
  SemanticAuthorityKind, not a second key-set/schema heuristic. Constructor decode
  descent remains owned by NRA. New schema fields need only the original schema;
  the cross-module fixture verifies that no OpenHCS schema list needs updating.
- TIME-8/9: no persisted application format changes, compatibility readers or
  codec subclasses. Git owns revision/gitlink membership; generated Python
  snapshots/caches are internal disposable state, removed after each comparison.
  Counts are a derived report, not a competing semantic authority.
- IMPL-3: there is no command-name/action registry. CI path selection is an
  external workflow boundary. The retained read-site distinction for redundant
  checks follows the original NRA detector's source-first evidence contract.
- AGENT-7: use one always-reporting parity status; a relevant failure cannot pass
  by becoming skipped. Do not wait for optional hosted completion or infer live
  acceptance from these source checks.

## Actual source evidence

The existing shared OpenHCS Python3.12 interpreter ran17 provider-free checks in
12.92s, zero skips: cross-module schema ownership, real constructor descent,
unmodeled reads, original redundant-attribute findings, per-file growth,
syntax/deadline failure, scope cleanup, and the actual parity shell for four
required production roots plus irrelevant docs and failed/skipped status cases.
Ruff and git diff --check pass. Initial fixture run was4 failed/13passed because
Git archive rejects nonexistent optional root arguments; the snapshot owner now
derives present roots from Git. No assertion was weakened.

NRA source: existing `/home/ts/wt/nra-bounded-full-audit-20260929`, production
identical to main `0844525ecaba93e090a064a4ae4914466b2dae60`,85 registered detectors.
This gate selects only the two R1 detectors and original schema/descent graph,
with changed-file reporting and recorded dependency context. It does NOT claim
all-detector/global FULL audit completion. The older shared NRA checkout lacks
R1 and is not used. Deadline/parse/absent-dependency failure remains nonzero.

The packaged ratchet was imported from its existing source tree with the already
available Python3.14 interpreter, enumerating11 registered measures. Python3.12
imports fail in unrelated eager package initialization (InputDocument annotation
namespace); no consumer bypass was added. Hosted ratchet explicitly uses3.14.
No local tool installation, environment creation or download was performed.

The first actual own-PR R1 CLI run completed analysis but FAILED reporting at
90.00s/256704KiB/exit1: R1Comparison did not inherit NRA's SemanticRecord.
The original empty stdout and traceback/resource receipt remain in evidence.
Correction uses the original report ancestor and declaration-owned computed JSON
field; no consumer codec or raw DTO schema was added. Two real subprocess CLI
tests now prove valid JSON and nonzero candidate-growth exit. The additional
missing-gitlink test proves an uninitialized child cannot silently read parent
source. The corrected20-case source suite passed17.41s/399024KiB, zero skips.
The static scanner is terminal and its flock released; scratch snapshots removed.

Packaged real Git comparisons at `9df03dada` pass for all three roots (including
scripts/check_refactor_r1.py), zero positive metric deltas. Full JSON and resources
are in evidence. Recorded worktree submodules were initialized, without any
gitlink or installed-source change; pycodify reused the existing local uneval
object repository. This is source preparation, not a new runtime/tool installation.

Guard before checks: /home30.8GiB, available RAM16.0GiB, historical swap warning
only. Synthetic Git/snapshot scratch is below6MiB, owned at
`/home/ts/.cache/agent-scratch/openhcs-r0-light[-b]-20260930`; no scientific input.

## Activation and remaining acceptance

Read-only GitHub API confirms admin/maintain/push rights. Main protection has no
required status checks; effective rulesets are empty. Required-check activation
is NOT claimed. Workflow publication is not check activation or hosted execution.

Owner explicitly forbids adding a required-check/branch-protection rule that
creates a hosted waiting gate. No protection mutation was performed. A fresh
read confirms required_status_checks remains null and enforce_admins false.
Automation publication and source validation do not imply required/live activation.

Actual packaged Git comparisons are DONE; raw reports are preserved as gzip
artifacts with resource captures. The two real final CLI subprocess cases pass
6.08s (18 other cases deliberately unselected in that path-only check).

The corrected own-PR R1 run at `ec66ef72f`, base `dbf1c7a8b`, is terminal FAILED,
not accepted: NRA raised ScanDeadlineExceeded during parse_python_module at the
existing160s absolute budget. Total161.74s includes cleanup, peak409600KiB,
exit1, no result JSON. Its original stdout/traceback/resource receipts are retained
separately from the first90s reporting failure. The exact flock/scan identities
are absent and the lock was verified available afterward. Snapshots were removed
by their owner. Parent owns the next installed205/264 native slot; no second heavy
scan is launched ahead of it.

Coverage was TWO selected detectors with the original schema/descent graph and
all declared source/gitlink context. It was NOT an85-detector/global FULL audit.
Small CLI success does not establish this full-context gate's bounded acceptance.
Source read identifies an important boundary: NRA analysis.py:2067 deliberately
removes focused projection demands when include_semantic_descent_graph is true.
The R0 consumer currently asks for that full graph to select typed mapping-read
certificates. Remaining R1 work must use/extend the existing scoped projection
owner, not parse finding strings, copy schema heuristics, omit dependency context,
increase the observation timeout, or report a deadline as zero debt. This concrete
bounded-entrypoint blocker remains owned by Lovelace; NRA PR12 is the separate
existing FULL-lifetime repair, not a claimed fix here.

## Authenticated reuse follow-up (source only)

SourceRevision still creates two immutable committed snapshots. The consumer now
passes the SAME original NRA parse/analysis cache directories to both scans,
instead of segregating them by commit. NRA cache_checkout.py owns relative-root
admission/rebinding and source/content identities own validity; no new cache,
source roster, rebase of finding paths, or heuristic was added. The original API
owns parse-cache enablement. Native cache status/projection counts and split
preparation/analysis time are emitted as observations, not inferred performance.
Coverage and the160s bound are unchanged; no production context is omitted.

The latest21-case lightweight suite passes19.59s/399436KiB/exit0, zero skips.
It includes a changed schema causing the same consumer to transition from an
owned mapping-read bypass to unmodeled_record_shape under shared authenticated
cache use. Existing constructor descent, stale/missing source, parse/deadline,
per-file growth, actual CLI and workflow-shell assertions remain intact.
Ruff and diff checks pass. Cache reuse has NOT yet passed the actual own-PR
full-context entrypoint; that bounded comparison is the remaining acceptance
after parent's installed205/264 slot. Both failed originals remain preserved.

The packaged scripts ratchet also passes at `dbe8c7749` against integrated main
`fb5fea4f1`, zero positive deltas; its compressed raw report/resource capture is
published. No205 production changes are attributed to R0 or reverted by its base.
All owned test/scanner identities are terminal. About13MiB of generated Git/NRA
fixture scratch was removed after receipts were saved; the fixtures are
reproducible from committed tests. Original failed receipts are not deleted.

Existing Official30 numerical comparator is reused unchanged; its PR trigger
already existed, so this change adds relevance and fail-closed status wiring
rather than claiming to invent PR parity. No new native/JVM/GUI/installed parity
run has occurred. Full R0 acceptance and archive L0/S1-S8 remain open; no global
correctness or live readiness claim.
