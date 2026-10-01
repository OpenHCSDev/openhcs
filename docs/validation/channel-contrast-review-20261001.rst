Channel-switch presentation QA
==============================

Parent integration owner, isolated persistent paired-raw worktree, branch
docs/channel-contrast-review-20261001, based on merged main0d07909b.
This is a packaged skill/discovery checkpoint. Dalton retains the live science
slot and its installed environment; installation of this checkpoint is pending.

Observed failure and correction
-------------------------------

Native MCP state/captures in the retained development output
OWNER-LIVE-CURRENT-NATIVE-PNG-RECEIPT.json and
OWNER-LIVE-CURRENT-PRESENTATION.rst establish Ch2/calcein raw-only with
contrast502..65535/gamma1. Results were hidden. Direct render-complete PNG
222834.720859Z suppresses faint processes; same-camera PNG222835.118675Z at
141..450 reveals the network. Parent personally opened both. The intervening
channel/camera-change actor is unknown. These windows illustrate this witness,
not settings prescribed for another acquisition. Remote transport is not
needed to explain the dark native rendering.

The existing viewer-qa.md now explains shared-layer contrast retention,
readback/reapplication after channel changes and native PNG comparison when
remote compression is suspected. It distinguishes presentation from loss in
saved processing stages. No channel-state store or automated viewer restoration
is added. Existing distributed, multi-window, raw/result/combined QA remains.

Original owners and validation
------------------------------

The packaged viewer guide remains canonical. Original knowledge-manifest tags
make two new queries discoverable. AgentSkillBundle, KnowledgeBaseService,
project_knowledge_assets and sync_skills remain unchanged. IMPL-12/13 and
MEMB-1/2 review retains those owners without a parallel procedure or catalogue.

Original check-function-help-390.py uses existing read-only ABI dependencies,
paired pyqt-reactive/zmqruntime source imports, plugin-free/no-root-conftest
pytest. Both serial shards used one CPU, MemoryMax512M/MemorySwapMax0 and 60s.
Package projection/content/links plus byte-exact full skill sync/idempotence:
2 PASS/20 deselected, 4.82s, 254456KiB. Initial underscore query selection selected
neither new query; a separate channel-or-remote shard exercises those two plus
the existing channel-identity query: 3 PASS/19 deselected, 6.61s, 280044KiB.
Both retain the two existing disabled-asyncio-plugin config warnings.
Original skill-creator quick_validate passes; whole diff-check passes.
There are no production Python changes. These checks establish retrieval and
packaging, not autonomous biological performance.
