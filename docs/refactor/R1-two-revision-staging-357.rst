R1: authenticated fixed-address revision staging
===============================================

Independent source sidecar for OpenHCS issue357, originally based on remote main
``c81963475e6221961be5209c47c36f5f4c222521``. PR349 is now merged at main7640fd95;
parent proceeds with PR351 installed/native acceptance. This patch changes only the R1 source
consumer, guardrail tests and this reference. NRA's engine and original pin,
viewer, scientific pipelines, application CLI and installed packages are unchanged.

Retained failure
----------------

The original comparison is head ``901e9a49a6e18f0b9c86574210568d1a3efbae67``
against base ``c81963475e6221961be5209c47c36f5f4c222521``, with all production
roots (``openhcs``, ``scripts``, ``benchmark``), eight recursively recorded Git
dependencies, two original R1 detectors and the original full schema/descent
graph. NRA production is main ``0844525ecaba93e090a064a4ae4914466b2dae60``,
identical to the production source in the read-only review checkout at
``673c062fc656e9c74f1eddcab30f036c9befbc1f``.

The unchanged baseline completed3068 projections with112.790s preparation and
6.291s analysis. The second scan was killed at122.45s after observed combined
process-group RSS reached551.88MiB. Original limits are160s native,165s wall and
512MiB combined RSS. No head counts, passing comparison or global-clean claim
follow from that failure.

The authoritative failure remains at
``/home/ts/wt/openhcs-issue-batch-20260929/R1-TWO-REVISION-RESOURCE-DEFECT-20261001.rst``
with the original command, log and JSON receipt in that parent's ledger. None
is overwritten or reclassified by this patch.

Ownership and cutover
---------------------

``SourceRevision`` remains the Git/tree/gitlink membership owner. Its archive
reader now streams output rather than retaining a whole archive (including
non-Python artifacts) alongside analysis memory. It preserves identical Python
bytes and stat identity, and returns the exact materialised source membership.
Recursive child revisions retain the source owner's concrete class through
``dataclasses.replace``. No companion repository or schema roster exists.

``StagedSourceRevision`` inherits the reader and admission contract. Its only
added responsibility is pruning previously staged Python files absent from the
new recursive Git membership. Both scans use the same private ``source`` address.
Deletion and removed gitlinks cannot leave stale source discoverable at head.
The directory contains disposable committed-source copies, never user source.
The replacement is unconditional; there is no flag, alternate cache, legacy
reader or fallback path.

NRA's original ``analyze_compact_roots_with_cache`` owns every parse, collected
family, analysis identity and schema/descent resolution. The existing parse and
analysis cache directories remain shared. Fixed paths enable the original
collected-family identities to match unchanged source. Changed bytes, additions,
deletions and dependency changes still reach its original authentication and
fresh global resolution. No prior policy counts are substituted for head analysis.

Only immutable ``R1Count`` results cross the transition. Once ``scan_counts``
returns, the original NRA ``release_module_analysis_memory`` owner releases
scan-bound caches and collects graph cycles before the next revision is staged.
There is no consumer-maintained cleanup roster and no engine modification.

Catalog witnesses: IDEN-6 (different absolute addresses distinguish identical
source unnecessarily), MEMB-1 (Git membership is derived, not recopied),
BOUND-2 (the original analysis/certificate/cleanup owners remain authoritative),
IMPL-4 (the staging subtype extends the original reader through inheritance),
TIME-1/9 (one active path, no adapter or stale-count substitute).

New-case closure: another recursively recorded Git dependency is read through
the same polymorphic source owner without any consumer roster edit. A new schema
or field changes only its original declaration. All detector selection, source
policy, report scope and semantic graph obligations remain unchanged.

Focused verification and limits
-------------------------------

The final source run passes35 tests in45.51s wall at144.18MiB sampled
combined child RSS, under the60s/512MiB source limits. The initial test command
failed fixture setup because its scratch parent did not exist; the failure is
retained in the sidecar's durable ``validation/focused-first.*`` receipts.

The fixtures exercise both real Git revisions and original NRA analysis, not
mock findings or a replacement schema model. They cover original constructor
descent, new raw-record/type-check debt, actual R1 CLI JSON/exit, per-file growth,
parse/deadline/missing-dependency rejection, literal deletion/move identities,
changed/added/removed/ambiguous schema context against a fresh original analysis,
and fixed-address projection reuse (zero reparses for a comment-only transition).
Recursive dependency changes/removal match fresh original analysis. A weakref
check verifies the baseline graph is gone before the second analysis starts.
The actual CLI returns nonzero for both new raw-record and type-check debt.

A separate read-only source-staging check on the exact original base/head passes
in4.95s at207.47MiB combined RSS. Each revision contains1535 Python files and
the same eight Git-recorded dependencies. All1530 unchanged files preserve their
stat identity; only the five changed files are rewritten. Membership is checked
independently against recursive ``git ls-tree`` output. This checks real source
staging, not NRA analysis, cached counts or production comparison acceptance.

The packaged lightweight census on the changed script reports zero growth in
type-identity checks, raw string-key reads, dispatch subjects/arms, long boolean
chains/terms, codecs, foreign probes and named-attribute access. The full scripts
overlay has no raw-shape finding for this consumer. The new archive subprocess
is an external streaming boundary with checked exit and guaranteed reap, not
a provider/runtime launch. Both scripts complete with no parse warning.

Commands, full successful/failed source logs, resource JSON, staging recipe and
lightweight census/overlay reports are retained in
``receipts/r1-357-source-20261001.tar.gz``. The initial setup failure is retained
alongside successful runs, not overwritten.

Interpreter/dependencies are read-only:
``/home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python``.
Source selection is explicit through this worktree and
``/home/ts/wt/nra-bounded-full-audit-20260929``. Application conftests and plugin
autoload are disabled. No provider, download, install, native, science, UI or
MCP run is performed.

The full production901e9a49/c81963475 two-scan comparison is NOT yet verified.
The parent owns ``validation.lock`` and the active installed349/paired351 lane.
No heavy gate is dispatched ahead of that workflow. The required acceptance is
still the original full context under160/165s and512MiB, with genuine new debt
rejected. Small fixture success does not prove those production resource bounds,
all-detector/global FULL acceptance, or installed/live readiness.

If the production comparison remains over bound, the next owner is the existing
NRA PR12 integration owner, at ``analysis.analyze_compact_roots_with_cache`` /
``BoundedCompactProjectionManifest`` and original collected-family/graph lifetime
interfaces. This sidecar does not create a competing core repair or block OpenHCS.
