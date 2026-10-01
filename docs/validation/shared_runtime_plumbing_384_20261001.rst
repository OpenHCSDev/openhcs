Shared runtime plumbing qualification
====================================

Issue #384 covers repeated source resolution, metadata construction and artifact
rendering outside callable execution. This branch combines three production
dependencies under their existing lifecycle owners. It does not yet establish an
end-to-end speedup.

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

The fresh open-issue audit verifies 7 of 29 have formal closing PR references;
22 still have no actual future fixing PR. Mere cross-references and diagnosis-only
drafts are not counted. Missing manual closing links were added for
138/207, 213/217, 320/217, 355/358 and 395/397. Existing 384/394 and 386/388 links
have closing cross-reference events. GitHub's official manual mutation is a no-op
for these already linked pairs; no exact ConnectedEvent is claimed for them.
Audit evidence: current-open-issues-connected-closing-audit-20261001.json/.md,
remaining-remote-branch-pr-audit-20261001.json and
local-worktree-branch-inventory-20261001.json in the external evidence directory.

The earlier runtime-plumbing prototype 2253ec63b is rejected. Its paired timing
did not establish a gain and its original R0 gate failed. It is not part of this
branch or the accepted evidence. Failed controls and diagnostic observations are
retained in the external benchmark evidence directory rather than replaced with
the fastest observations.

Pipeline clocks exclude ZMQ server startup, mandatory registry/kernel prewarming
and shutdown. Timed runs use the ordinary public OUTCOMES path and default memory
observer, without profiling injection. Candidate and baseline must have frozen
clean source revisions and the same dependencies, affinity and environment.
