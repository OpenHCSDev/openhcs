Saved label plane-domain source repair (#419)
===========================================

Owner: Dewey. Base: c32447f1c86a1878a313d1643a398e30ac20f75e.
Existing persistent worktree reused; previous branches and untracked evidence
are preserved. No new environment, installations or runtime/scientific jobs.

Current owner correction: RuntimePlaneAxisValueProjection.from_source_declaration
constructs projection from the declared optional axis and original nominal
SourceImageProvenance. SourceImageObjectLabelBuildRequest consumes that proof.
The projection value already owns declaration-based constructors and canonical
preserve()/selection; no metadata hook, second registry or compatibility reader
is introduced. Both production files are outside PR394's listed shared seams.
The earlier rejected metadata-owner proposal below is historical, not required.

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

Adjacent original controls: 17 passed, 7.000s / 409400KiB aggregate RSS, covering
CellProfiler image-output metadata, source spatial domains and the unchanged
AreaShape hotpath (adjacent-controls.log/xml). Total source controls: 209 pass.

The explicit original-executor Morph DISTANCE reproducer remains FAILED:
returned shape(1,) versus required(1,9,9), 5.026s / 327844KiB aggregate RSS.
This is an earlier original invocation witness, not a claim to reproduce the
later live module-output contextualization's exact shape(1,1) message. Both
original traces remain retained; the reproducer has no xfail or suppression.

Original pinned R0 was recovered without a new worktree, extracted copy or
alternate detector: validation/run_pinned_r0_419.py uses importlib ABCs to read
original package modules on demand from retained agent-comms Git objects at
CI pin3b03785f45df2ef5dc62ba6aed99294192ecbb01. The detector blob SHA256 is
e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562.
Python3.14 and metaclass backing remain read-only. It REJECTS production
e6fc6ad83: ForeignAbsenceProbe on runtime_object_label_building.py increases
0 -> 1. Original output r0-original-pin.log is retained. No R0 PASS claimed.

That rejected checkpoint names a real boundary violation: the builder asks whether
another owner's optional metadata plane_axis is present. The metadata owner
must instead report its complete projection. metadata-owner-proposal.patch
is an UNAPPLIED request, not a competing runtime edit: add the small original
ImagePayloadMetadata.preserved_plane_projection() owner hook and replace the
new builder probe/constructor with that call. It changes no existing singleton
hook behavior, raw output contract, enum/member roster, or scientific kernel.
The unmodified R0 also rejected the unapplied metadata hook: original
ImagePayloadMetadata GodClassExcess rises540 -> 550. The initial attempt to
submit its tree rather than a commit is separately retained as a failed command.
The proposal is rejected, not substituted into the current implementation.
Its remaining raw ndarray invocation correction belongs to PR394 independently.

The current correction instead extends the EXISTING projection value's source
construction alongside from_projector. The optional declared axis is an explicit
constructor input, not a metadata presence fact re-decided by a consumer.
Cardinality/aliases derive from the original SourceImageProvenance, and original
preserve() validates them. Source builder delegates construction and keeps its
own domain/shape invariants. No new carrier, facade, mapping or roster is added.
The superseded probe/constructor in the builder is removed. Independent paired
source-admission capability composes with the actual projection value through
cooperative __post_init__/super; inherited source construction and selection
execute its hook, reject three sources, while the original projection accepts
the same three-source declaration. Generic consumers need no new leaf branch.

Projection-owner controls before adding the new paired capability cases:
209 PASS, 8.771s / 416796KiB aggregate RSS (projection-owner-controls.log/xml).
Final source cases and original pinned R0 will be appended at the current head.

R1 full-context qualification is not claimed. This reused source worktree's
eight recorded dependencies are uninitialized; the original SourceRevision
require_repository guard rejects parent-repository resolution. A reduced
context scan or retained counts would not qualify the original R1 contract.
No full heavyweight gate is started within the source60s boundary.

Original plan hashes (read-only, not copied data stores):
geometry-plan-4.py dd00bdcef3fdc101a4aaf533ed2897086ead605918849f55070ee2d22b20e4d0;
distance-plan-2.py 3fefcf9113143728b98db2ba1a23e40b60625a60ee717958f0e20c44ad8f3c31.
Frozen public388 driver still has original SHA256
d3f259fae72ed5f70117646befa6b68a8301e168d785a7a56159cce1726bfd23.

Remaining acceptance: finish current-production unchanged R0, receiving PR394
owner settles raw invocation seam, then parent-installed original saved-label
geometry/EDT acceptance. Full-context R1 remains a separate unqualified scope.
No merge-readiness, biological readiness or original issue closure is claimed.
