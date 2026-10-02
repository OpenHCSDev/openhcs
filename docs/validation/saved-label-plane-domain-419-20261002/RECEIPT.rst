Saved label plane-domain source repair (#419)
===========================================

Owner: Dewey. Base: c32447f1c86a1878a313d1643a398e30ac20f75e.
Existing persistent worktree reused; previous branches and untracked evidence
are preserved. No new environment, installations or runtime/scientific jobs.

Original failures remain in the parent-owned neurite-development-skill383
evidence root. Geometry job 7ff51e34-b98f-4d56-953d-2ea32dba612a and distance
job 0f9f7236-ae18-440b-bedf-1dfa2946c427 are not replayed or reclassified.

Production owner: SourceImageObjectLabelBuildRequest.plane_semantics. This
existing builder must retain the input's explicit nominal plane-axis and exact
source-plane cardinality, not infer spatial dimensionality from array rank.
Existing ObjectLabelPlaneDomainStrategy and registered shape kernels continue
to own projection and geometry. No new registry or copied geometry.

Patterns reviewed from the current NRA/refactor-audit package: IDEN-1,
BOUND-2 and IMPL-13. A new PhysicalCalibrationRequired admission capability
composes through cooperative super() with the original builder; it exercises
actual acceptance/rejection and per-plane building, not only MRO assertions.

PR394 retains its runtime/CellProfiler files. Minimal canonical raw-call ABI
request is published at PR394 issuecomment-5944804885. Morph DISTANCE is a
separate unresolved shared invocation boundary, not fixed by this builder.
Installed/native original saved-label acceptance remains parent-owned.

Bounded source evidence
-----------------------

Original unchanged-main reproducer: 9 failed / 1 passed, 5.371s,
329084KiB aggregate RSS. original-red.log/xml remain unchanged. The first
corrected runs exposed two invalid test assumptions: comparing bound identity
methods rather than their returned identities, and expecting two sparse-ID rows
from the original AreaShape ROW_SEQUENCE/dense-extent ABI. Those runs remain
in geometry-focused and geometry-focused-corrected logs/XML. The final test
calls the original identity owner and checks the entire 135-entry AreaShape
vector, including every NaN slot, alongside exact input IDs/pixels/provenance.
This is not a claim that public final measurement rows have sparse-label IDs.

Current synthetic original-entrypoint and existing runtime-value controls:
192 passed, 7.882s / 392288KiB aggregate RSS. geometry-and-runtime-values.log/xml
retain all output. Existing registered MeasureObjectSizeShape resolves through
CallableContract and the original FULL_STACK executor, now consuming two
declared 2-D planes with XY1.3556 and correct native pixel areas 6 and 12.
Both original runtime axis declarations, singleton source, genuine volume
within each declared plane, explicit payload override, undeclared volume,
missing/conflicting cardinality, geometry conflict, payload-wide ID rejection,
explicit axis conflict and cooperative calibrated-leaf admission are covered.

Each shard uses systemd MemoryMax512M / MemorySwapMax0 / CPUQuota100%,
taskset CPU0, outer timeout60s and the existing aggregate-RSS monitor. Python
is the read-only generated-inputs-installed-parent interpreter; source root
is this worktree. Existing source_shard.py borrows only the two installed ABI
extensions and asserts source import ownership. No application processes,
compiled scientific jobs, installs or package changes are performed.

Pinned R0/R1 qualification is not yet claimed. The former pinned R0 worktree
was removed in the separate cleanup; retained UV checkout detector bytes are
different from the original pin and must not be substituted. R1 must retain
all recorded Git dependency context, not run on missing submodules as if it
were complete. Additional source controls/guards will be appended separately.
