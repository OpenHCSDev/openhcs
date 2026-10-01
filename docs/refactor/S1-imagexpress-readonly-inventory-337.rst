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

Pending: implementation, focused source validation and unchanged original guards.
Parent owns final installed public generate-inspect-initialize-reinspect journey
before merge. Neither source checks nor incomplete NRA evidence establish that.
