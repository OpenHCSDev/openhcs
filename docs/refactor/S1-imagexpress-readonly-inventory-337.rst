S1 issue337: read-only acquisition path ownership
=================================================

Implementation owner: Arendt. Integration/installed acceptance owner: parent.
Persistent worktree: /home/ts/wt/openhcs-imagexpress-readonly-inventory-337-20261001.
Branch: fix/imagexpress-readonly-inventory-337-20261001. Created at fetched main
8c512d404f8707a6a1be311406c0af2a089360f7, normally integrated merged333 main
f24a828da16691b83284622a01e1765b1d147e66 before shared handler changes.
Completed334 source and evidence are untouched. No installed/live/scientific work.

Read before decisions: complete dispatch S1-IMAGEEXPRESS-READONLY-INVENTORY-
20261001.rst, binding GOAL-SCOPE, canonical 00-RULES/01-INDEX, full NRA SKILL and
batching, authoritative refactor-audit.skill SKILL, patterns README, full
BOUND/IMPL/MEMB/identity examples and surface-receipt. Antipattern review is actual
source review, not a global NRA proof.

Before-source witnesses and ownership decision
----------------------------------------------

BOUND-2: PlateInspectionFilenameParser.parse at plate_inspection_service.py:549
strips Path.name before parsing. PlateImageInventory._record at
plate_image_inventory.py:268 separately asks only the filename parser. Both bypass
ImageXpressHandler's existing TimePoint/ZStep acquisition interpretation at
imagexpress.py:128-290. Initialized virtual paths already carry the correct axes.

IMPL-12/13: _flatten_timepoints, _flatten_zsteps and _flatten_indexed_folders repeat
traversal, folder recognition and coordinate replacement at different depths.
Move, do not copy, that format interpretation into small independent cooperative
TimePoint/ZStep hooks. Shared basename decode, path-coordinate composition and
mapping collection belong on the actual microscope image-path ancestor. Leaves
declare only format behavior. Initializer and read-only consumers use that owner.

MEMB-1/2/4 and IDEN-5: existing MicroscopeHandler/AutoRegisterMeta own discovery.
No parser roster, microscope switch, mirrored DTO or parallel address store.
Reuse FilenameParseResult, its nominal components and SourcePixelRef. Keep raw
physical paths distinct even when basenames repeat. Metadata JSON remains the
existing external mapping; raw inventory is derived read-only state.

Before census at integrated main: original debt_census.py, existing Python3.14,
all microscopes sources parsed; exact totals and per-file evidence archived with
validation. Source decision also traces PlateImageInventory.from_orchestrator,
PlateFileInventory.from_handler and inspection/query call sites. This source
census is a screening observation, not global detector/proof coverage.

Shared-file sequencing: checked open PRs.333 owned imagexpress.py and filename
construction. Posted precise owner coordination on333 before touching it; parent
then explicitly verified333 merged at f24a828. Normal merge completed before
handler edits; no Averroes branch/worktree edits, no change to producer spelling.

Acceptance and resource ownership
---------------------------------

Fresh owned raw fixture, never previously initialized: four physical planes,
same A01/site1 basenames across channels1/2 and Z1/2, time1, correct calibration.
Production inspect and inventory/query must retain all coordinates, source paths,
bounded samples/parse/failure/component limits, and unchanged source/metadata bytes.
Then separately initialize through the real source handler and compare native
inventory identities. Preserve other registered-handler controls and diagnostics.

New-case experiment: a newly declared path-aware acquisition subtype selected
through existing registration must work in the unchanged generic inspector and
inventory. Exercise independent coordinate capabilities in both cooperative MRO
orders, common ancestor identity once. No consumer or registration edits.

Resource helper warned: available RAM21.2GiB, /home19.6GiB, swap13.7GiB.
Only focused one-CPU/512MiB/60s source shards, existing interpreter/dependencies;
no agent/provider/package/Fiji/data downloads or runtime processes. Owned scratch:
/home/ts/.cache/agent-scratch/openhcs-imagexpress-readonly-inventory-337-20261001,
purpose bounded source census, compiler/test/guard logs and fresh unit fixtures.
Archive receipts, then clean this exact disposable root and owned build binaries.
Persistent worktrees remain. No scientific/held-out/reference files are accessed.

Working checkpoint: ten production-path tests pass, 4.12s/230664 KiB RSS, one CPU.
Fresh raw four-plane inspection, real file query, explicit native initialization
and reinspection agree on axes and exact physical source paths. Original bytes
remain unchanged; read-only inspection never creates workspace metadata. Flat,
TimePoint-only, ZStep-only and nested paths retain filename/folder precedence.
Bounded skipped/unparsed/duplicate-axis failure receipts remain observable.

Actual new-case evidence: one SiteAcquisitionHandler declaration composes the new
independent SiteFolders capability with ImageXpressHandler, both base orders.
Existing AutoRegisterMeta selects it through the real factory. Unchanged inspector
and file query retain site7/time3/Z1/2; the cooperative SiteFolders and PathTerminus
each execute once per interpretation, and the shared ancestor occurs once in MRO.
No consumer, registry, parser catalog or dispatch branch was added for the subtype.
Test-only declarations are removed from the existing registry on test teardown.

Deleted: all three _flatten_* procedures; basename-only inspector decode;
inventory's filename-only delegate; separately supplied parser/metadata pairs in
the image/file inventory API. Existing result-artifact filename interpretation is
unchanged. MicroscopeHandler's filename delegates moved to its actual path ancestor
and were deleted from the oversized class; that class shrinks, not grows.
Shared path decode/composition, folder traversal and mapping collection are on
MicroscopeImagePathParser; format grammar and nominal coordinate choice are small
cooperative TimePoint/ZStep hooks. No second address store, DTO mirror or registry.

Preserved persisted contracts: external ImageXpress filenames, folders and HTD
metadata unchanged; existing OpenHCS workspace JSON schema unchanged. Initialized
mapping derives the same canonical identity from the same path owner. Ambiguous
physical paths now fail explicitly rather than silently overwriting a source ref.
No migration, installed package or runtime change.

Original failing reproducer and every attempted test log/XML are retained.
First added 512MiB address-space cap failed in pytest collection (193220 KiB RSS):
mapped-library virtual memory is not resident memory. Subsequent identical-input
measured run remains below 512MiB resident memory; original failure is not erased.
Two subsequent test-fixture mistakes (enum order and DTO field names) are corrected;
their original failures remain archived. No existing assertion was weakened.

Existing regression closure: 42 service/new-path cases PASS, 11.77s/302392 KiB;
28 inventory/registered-handler/ImageXpress compatibility cases PASS,
7.57s/266464 KiB; 27 producer/parser-diamond/new-path/static-browser-inventory
cases PASS, 6.00s/282932 KiB. No GUI/viewer launched. Both parser diamond orders
are unchanged. Both new path capability orders now also initialize through the
real handler and preserve the same physical references in the native inventory.

Actual regression found and repaired: result-only OpenHCS inspection's parser
property may raise MetadataNotFoundError, already captured by the existing
_parser diagnostic boundary. The initial optional-self view retried that property
and bypassed its recorded absence. That view was deleted; the caller retains
the existing observation and supplies the real path owner only when available.
Original 41-pass/one-failure service shard is retained. No legacy reader/fallback
or duplicate diagnostic store was introduced; existing warning receipts survive.

Current pinned source and unchanged guards
-----------------------------------------

Current tested source: 42ebd233c2bcbd0bb9baa52febda284df0885188. Normally
integrated356 at9bb5e9aaa, then merged parent-shipped334/main
20ca4f82526974f16017021e313e4e6cf265b547 without conflict. The five owned production
files and tests have zero diff across the latter merge; base356 and base20ca also
have zero diff in those production files. No scientific/installed slot was used.

Production deletion first: 224 lines deleted,152 added, net72 deleted in five
production files versus main20ca. Original microscope census6920 ->6882 code
lines; ImageXpress alone489 ->391. No added string-key reads, literal gets, type
checks/switches, string dispatch, foreign absence probes or broad exceptions.
Three nominal classes added: actual path ancestor and two independent acquisition
capabilities. Five new None identity checks are explicit owned optional/parser
and unmatched-path facts, not foreign probes or hidden absence. No metric waiver.
All microscope files parsed; exact before/diff/after census is archived.

Final tests at42ebd233: 42 service/path tests PASS,6.38s/302296 KiB; 45 existing
inventory/handler/producer/static-browser controls PASS,11.35s/310860 KiB.
87 distinct cases, CPU0/timeout60, under512MiB RSS, existing Python/dependencies.
Actual inspect-plate generated CLI --help exits0,5.10s/249008 KiB, no MCP launch.
Correctness Ruff E9/F63/F7/F82 and git diff --check PASS. Existing UI assertions
were only migrated to the single handler API; no GUI/viewer was started.

Unchanged original R0 at3b03785: f24 ->3c7240016 PASS17.69s/87552 KiB; final
356910557 ->9bb5e9aaa PASS17.64s/87560 KiB, zero exceptions/increased measures.
After normal20ca merge the exact before/after selected production bytes are
unchanged; original measured comparison is retained, not relabelled as another run.
Scripts/benchmark have no owned Python diff, so no extra empty-scope pass claimed.

Unchanged full-context R1 at NRA0844525 and original scripts/check_refactor_r1.py:
base356910557 ->9bb5e9aaa, original roots openhcs/scripts/benchmark plus ALL
recorded dependency Python context. One CPU,512MiB address-space ceiling,
original55s deadline and bounded Git pack mapping8m/128m. INCOMPLETE,exit1,
ScanDeadlineExceeded during parse_python_module55.000s/55.000s, wall56.19s,
264000 KiB RSS. Source materialization completed but parsing did not; no
before/after/descent certificate, scoped substitute or global proof. Later20ca
context was not rescanned; this omission is explicit. The tool cleaned its owned
snapshot directory. Incomplete unrelated NRA tooling did not block implementation.

Authoritative archive SHA256 reverified:
100fbe8ef89664b866777e87b2c8640a3432e8a10e9188dff81c97942d551bf6.
Actual antipattern review is confirmed by the source witnesses/removed mechanisms
above and behavioral extension evidence, not by an incomplete analyzer pass.

Archive: receipts/S1-imagexpress-readonly-inventory-337-20261001.tar.gz, complete
logs/XML/census including original failures, subsequent repairs and both normal
merge logs. Fresh extraction/content comparison must succeed before cleanup.
Named disposable scratch and source-only build binaries, plus owned pytest caches
in both S1 worktrees, are moved to recoverable trash after archival. Persistent
source/worktrees and all recorded evidence remain. No installed/package/skill or
managed blind instruction change. Upcoming H003g candidate/runtime is untouched.

This completes the source fix checkpoint for337, NOT all S1/ZIP. Named remaining
S1 includes plate rendering, config/knowledge/function/authoring, object-state,
viewer/runtime, UI/code-document/state-surface. Separately owned339 generated
connection input projection has an issue/reproducer but no implementation yet;
it will have its own visible draft, not an expansion of334 or338.
Parent owns final installed public generate-inspect-initialize-reinspect journey
before merge. Neither source checks nor incomplete NRA evidence establish that.
