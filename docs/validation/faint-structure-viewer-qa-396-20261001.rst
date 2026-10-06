Faint-structure viewer QA: packaged skill PR396
==============================================

Owner and scope
---------------

Singer owns this documentation/package follow-up, on branch
``docs/faint-structure-viewer-qa-20261001`` in existing persistent worktree
``/home/ts/wt/openhcs-knowledge-lazy-conversion-20261001``. Its base is main
``91dc52d4040890e1b88494acba7368196f6cd1e8``, the verified merged PR391.
PR377 remains an independent diagnostic; previous evidence/history is retained.
No new worktree, environment, download, build, installed-package change or live
Dalton383 skill/environment update was made. Parent owns future installation
and affected live acceptance; this guidance applies to future installation/run.

Open PR ownership checked: parent PR394 runtime plumbing, Dewey PR388
classification declarations, Schrodinger PR358 startup/connect and diagnostic
PR377 do not claim these packaged guidance files. Parent's authoritative RST
analysis strategy, blind promotion and learning procedures are unchanged.

Canonical owners and required relation
-------------------------------------

The operational viewer procedure has no corresponding authoritative RST source.
Its owner is maintained ``packaging/codex/openhcs/skills/use-openhcs/references/``
Markdown. ``viewer-qa.md`` owns the scanning/matched-set procedure;
``image-preprocessing.md`` owns nuisance interpretation and compatible method
composition; ``measurement-interpretation.md`` owns claim-specific inputs;
``segmentation-diagnostics.md`` owns stage/body-boundary diagnosis. Existing
SKILL.md, analysis strategy and companion links route to these files, not a
second procedure. This RST is an evidence receipt, not another instruction set.

The guide now connects relevant-channel comparison, distributed full-field /
context / native raw-only scanning with progressively LOWER numeric upper
display bounds, faint-path and nuisance interpretation, compatible declared
preprocessing/order, segmentation/tracing on processed pixels, claim-appropriate
measurements, and distributed same-coordinate raw/processed/result review.
More than one window is required. Intentionally saturated somas and visible
background are useful diagnostic evidence, not automatic rejection gates.
Clear supported misses, lost paths and induced background bridges reject the
candidate. Publication clipping criteria depend on the figure's stated intent.

Acquisition source/provenance remains reproducible reference, not a prohibition
on working-array processing. Validated analytical high clipping/remapping,
denoising and correction are legitimate segmentation operations. Geometry,
count, area and length may use processed-derived labels/masks/traces.
Original-fluorescence photometry needs its appropriate named original/calibrated
intensity source. Read-only ruler/profile sampling is distinct from analytical
preprocessing; acquisition-file overwriting is not authorised.

The nuisance guide supplies alternatives, not a mandatory stack: additive
background estimation/top-hat, denoising plus background subtraction, or
denoising plus flat-field and background correction where justified. Actual
order/aliases, correction fields/residuals, faint positives and background-bridge
controls must be reviewed. Focus loss, acquisition saturation and genuine
biology are not automatically correction targets. No numeric assay recipe or
held-out/clipboard image analysis is introduced. The body diagnosis adds the
reusable principle that DAPI candidate count alone does not establish body
count; admitting/splitting another cell needs independent body-channel support,
without assuming a universal one-nucleus-to-one-cell relation.

Projection and architecture review
----------------------------------

Original ``mcp_knowledge_base_manifest.json`` paths still declare these exact
Markdown sources. Only two summaries and viewer search tags change there.
Original ``AgentSkillBundle`` derives resources from the plugin declaration;
``project_knowledge_assets`` owns packaging, ``KnowledgeBaseService`` owns
retrieval, and ``sync_skills`` owns destination/receipt behaviour. No generic
consumer, catalogue implementation, registry or Python production code changes.

NRA/refactor-audit review checked MEMB-1/2 (no parallel resource/capability
roster) and IMPL-12/13 (no copied projection/sync procedure). Existing owners
remain authoritative. No ornamental inheritance or second snapshot mechanism
is added; the shared observation/writer and Qt binding leaf remain untouched.
This docs-only change has no production R0 delta or claimed global NRA/R1 audit.
Skill-creator guided canonical resource maintenance and original validation;
Diataxis how-to guidance kept the practical sequence in its existing owners.

New-case evidence adds two task queries, diagnostic soma saturation and noise /
background / illumination scan, through the existing manifest declarations and
unchanged generic search/retrieval consumer. Tests verify retrieval/content,
not the new wording as scientific behaviour proof. Packaged retrieval additionally
checks full returned content against its canonical source. No assay executes.

Bounded evidence and original failures
-------------------------------------

Resource preflight warned: root7.7GiB/home12.5GiB free, swap13.0GiB used.
Only small serial checks ran. Each used one CPU, cgroup MemoryMax=512M /
MemorySwapMax=0 and a 60s shell bound. Pytest plugin autoload and root conftest
were disabled. Original dependency ABI binaries were loaded read-only by the
existing ``docs/validation/check-function-help-390.py`` helper; no native
application, MCP, UI, provider or scientific operation ran.

* Original source-package.log: collection failed on the older environment's
  ``WindowSnapshotFrameCondition.RENDER_COMPLETE`` absence; 5.77s/255508KiB.
* source-package-paired.log: same original error, because the PyQT-reactive
  worktree root rather than its ``src`` import directory was selected;
  5.16s/261660KiB. Both failed checks are retained byte-exact.
* source-package-sync.log: corrected read-only source selection at the exact
  recorded paired dependency ad4948775ab81180a354d4b793d17ee5ddff3972,
  ``/home/ts/wt/pyqt-reactive-render-complete-snapshot-20261001/src``.
  12 PASS,15 deselected,7.21s/274444KiB. Covers original packaging safety,
  declared resource discovery and wheel globs, new task retrieval, canonical
  packaged guide content/links, and complete projected skill sync into an
  isolated scratch harness. Sync verifies every resource hash/byte, exact file
  membership and an unchanged second sync/receipt, including all four guides.
  Disabled-plugin asyncio configuration warnings are retained, not suppressed.
* Original skill-creator quick_validate: PASS on canonical source, projected
  package skill and isolated synced skill. It checks skill metadata/structure,
  not biological correctness. Whole-PR ``git diff --check`` passes.

All five raw logs are archived byte-exact in
``docs/validation/faint-structure-viewer-qa-396-20261001.tar.gz``.
Tar comparison against every original log passed; SHA256:
``5e522283673fdb90c0ad5f6369ed9ad393aa3d24c3c049b040deb804e355e0f7``.
No loose raw log whitespace is rewritten to manufacture diff-check success.
After test completion and verified archival, owned disposable scratch
``/home/ts/.cache/agent-scratch/faint-structure-viewer-qa-20261001`` is released:
2.6MiB allocated /1,535,685 logical bytes. Source, durable history, original
failed logs, frozen installations and scientific outputs remain preserved.
Lorentz-owned cleanup is not touched.

Changed paths
-------------

* The four Markdown references named above; SKILL.md routing is unchanged.
* ``docs/source/development/mcp_knowledge_base_manifest.json`` (discovery only).
* ``tests/unit/agent/test_analysis_knowledge_transfer.py`` (retrieval/byte proof).
* This receipt and its raw-log archive.

Source/package/scratch-sync success is not fresh installed or scientific
acceptance. No hosted-CI wait or merge is performed by this owner.
