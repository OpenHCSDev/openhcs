Same-source viewer inspection and geometry
=========================================

Integration owner: parent OpenHCS agent. Issue302; branch
fix/viewer-route-spatial-302-20260930, based on main0cbb6fc26.

Reproducer and original real MCP receipts are preserved in
docs/validation/ack_runtime_parent_20260930/viewer-followup.rst and the
persistent issue-batch ack-runtime-parent-20260930 directory. No blind assay
or held-out answer is needed to reproduce this infrastructure defect.

Two acceptance failures remain: pipeline clear-state discards mounted raw
payload inventories, and ordinary Gaussian output loses raw physical XY scale.
The original raw pixels remain mounted; this is not an image-loss claim.

Ownership trajectory
--------------------

The existing native route store owns mounted-layer lifetime. Retained native
layers need their original component groups, observed/declared axis domains
and semantic names for inspection. New executions must cancel deferred work
and remove unmounted intake state, not sever the mounted route's data join
(IDEN-5). No producer-origin string classifier or parallel registry is needed
(IMPL-1, MEMB-2). Existing replacement/removal lifecycle must remain effective.

Separately trace original SourceSpatialDomain through compilation and streaming;
repair the first provenance loss, not a viewer-specific scale override (BOUND-2).
Avicenna owns a read-only independent geometry trace; parent owns implementation.
PR217 owns runtime image metadata/projection edits; PR206 owns preparation. Check
and coordinate any crossing before editing those surfaces.

Only runtime route state is affected by the reset correction. No durable saved
configuration, undo history or artifact format migration is authorized here.

Verification and delivery
-------------------------

Protect existing unmounted-domain reset and deferred-work cancellation tests;
add mounted raw/result inspection retention and native deletion regressions.
Repeat the real MCP raw-stream, lazy compile, execute, output readback journey.
Open same-coordinate raw-only, result-only and combined captures and assert
identical source transforms when no resampling is declared. Source tests alone
do not establish live or biological readiness. Use existing installed Python,
owned source pins and isolated display91; preserve H002 and user display0.

Publish a draft promptly; merge the coherent tested checkpoint without waiting
for optional CI. Ordinary installed activation remains separately reviewable.
Full refactor ZIP scope and autonomous-analysis goal remain active.

Current status: source trace underway; no fix or live acceptance claimed yet.
