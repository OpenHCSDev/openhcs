CellProfiler aligned full-stack boundary (#342)
==============================================

Owner: H003g runtime repair worker, under parent integration.
Audited base: OpenHCS main 0c0563e6538af313345391f2dc314270a86933a0.
H003g remains a frozen FAILED development repeat. No scientific retry or
native/MCP/viewer startup is authorized by this repair.

Diagnosis
---------

``CellProfilerModuleExecutor._image_request`` composes source/artifact image
values through ``compose_aligned_image_payload``. Multiple runtime-aligned
inputs produce an ``AlignedImageStack`` with one composed image bundle per
runtime slice. ``_invocation_request`` then applies the callable-owned
``runtime_image_execution_mode``. A FULL_STACK declaration supersedes the
composition's ALIGNED_MULTI_IMAGE_STACK mode without materializing its payload.
``CellProfilerFunctionContractExecutor.execute_pure_3d`` passes this alignment
carrier straight to the raw callable, whose numeric array contract is violated.

The retained candidate SHA256 is
7b69ce1f4256e2a64b32ecb1fefd6d22adef7ba3a1d98f5e2a3fc0125eab96b3;
the retained native log identifier is 1790835483807054701. The first failing
call is rescale_intensity, at RescaleIntensityContext.from_settings,
``source_data.astype(np.float32, copy=False)``: float(AlignedImageStack).

The synthetic two-runtime-plane/two-input composition reproduces this exact
stack with EMPTY kwargs: the primary image is the immediate root, not an
auxiliary binding. It does not read trial images or scientific outputs. Aligned
image kwargs have the same unmaterialized boundary and are covered separately.
The executor's
unchanged contract suite passed 32 cases while this added case failed.
The raw full-stack pass-through exists in 9110b10479 (June 2026); PR326 changes
neither this executor nor aligned_image_payload. This is an existing uncovered
boundary, not demonstrated to be a PR326 regression. Historical #204 is the
separate selector/input-scope surface and does not supply a fix here.

Ownership and migration
-----------------------

BOUND-2 and IMPL-12/13: the existing pixel stacking, mask composition and typed
provenance authorities are reused, not copied into the CellProfiler executor.
``ImagePayloadStackComposition`` is the actual owning ABC/template algorithm.
The existing same-slice ``ImagePayloadBundleContext`` inherits it through the
explicit dense-stack context, retaining its channel/spatial-mask hooks.
``AlignedImageStack`` inherits the same algorithm with runtime-slice inputs and
contributor provenance hooks. ``ImageOutputBundle`` remains a distinct named
source-binding axis; it is not treated as anonymous runtime alignment.

The existing AutoRegisterMeta/MRO-owned RuntimeSliceProjectionStrategy family
supplies the full-stack projection hook. The aligned image leaf calls the
payload owner; every other nominal family retains its own value. The executor
uses this authority for the primary image and kwargs before the raw call.
Object labels, measurement rows, graphs and RuntimeSliceAlignedValues are not
flattened into guessed arrays. The existing PURE_3D rejection of slice-aligned
non-image kwargs remains active. No callable-name branch, second registry,
numeric wrapper, alternate executor or installation change is introduced.

Source checkpoints
------------------

33 source cases passed, 2.35 seconds pytest / 3.08 seconds wall,
305672 KiB RSS. One CPU and a 512 MiB cgroup with no swap, 60-second timeout.
The isolated installed interpreter supplies existing dependencies; the source
runner resolves this worktree's Python code and only the unchanged installed
``_tabular_native.abi3.so`` artifact. No download/build/install is performed.

The first complete-package NRA attempt rejected a misdeclared context root.
The corrected whole-package scan admitted the installed candidate's external
directory, but that candidate's submodules are uninitialized; this is not
complete dependency context. The CLI's own 20-second deadline expired while
parsing (outer shard bound 60 seconds), with 511664 KiB RSS.
No complete global semantic/proof certificate
is claimed. Manual ownership evidence and source behavior tests are distinct.
The initial slotted-dataclass zero-argument super failure is retained and fixed
with explicit cooperative super(AlignedImageStack, self), not suppressed.

Expanded checkpoint: 110 cases PASS, 3.38 seconds pytest / 4.19 seconds wall,
322736 KiB RSS, under the same one CPU / 512 MiB / no swap / 60-second bound.
The 14 new cases cover the real rescale callable, all four ProcessingContract
families with singleton and two-slice image/auxiliary inputs, exact contributor
identities and slice projections, voxel calibration, masked source-binding
planes composed into a runtime stack, named output bundles, ragged-input
rejection before dispatch, and independent pixel/mask capabilities composed in
both cooperative MRO orders. The other 96 are unchanged executor and nominal
projection/alignment/device/registry controls. The named bundle strategy now
inherits the aligned-image strategy's full-stack hook; its own source-binding
projection/count behavior stays separate. Shared input validation uses
cooperative super; metadata composition stays in the ABC with a small
per-input provenance hook, not a direct jump around an ancestor algorithm.

The masked 4D control found that stacking shared 2D masks produces a 3D mask
outside the outer runtime axis's domain. The existing mask owner now consults
the composed ImageMaskDomain and uses its declared broadcast authority only
when required. Pixel values and exact masks are checked; no relaxed domain
check or ndarray coercion is used. Intermediate failed attempts remain in
diagnostics alongside the working logs and JUnit receipts.

A broader metadata/artifact-consumer shard had 44 PASS / 1 FAIL. The failure,
test_callable_abi_keeps_main_flow_artifacts_in_trailing_slots, declares only
two outputs although identify_primary_objects now has seven diagnostic image
slots in addition to the canonical slots. The exact same test fails on a
complete unchanged production source snapshot of main 0c0563e65, not merely
an executor substitution. No production ABI assertion or fixture was weakened.
This pre-existing fixture mismatch is owned by the runtime repair worker under
parent integration. Its fixture is now aligned by deriving diagnostic artifact
specs from PrimaryObjectDiagnosticPlanes.artifact_specs, the same authority
used by the production module declaration. No new role/name inventory or
production relaxation is introduced. The original failure receipts stay
retained, including the unrelated failed shard invocation with nonexistent
test paths; corrected consumer checks are reported separately.

Affected nominal owners: aligned runtime image stacks and their named-output
bundle subtype require materialization; already-dense image metadata/masked
payloads and arrays keep their own domains. Object labels, aligned non-image
values, measurement tables/columnar rows, relationships, sparse labels,
projectable identities and spatial graphs retain their registered strategies.
PURE_3D's prohibition on non-image slice-aligned kwargs is preserved. FULL_STACK
is shared by all processing contracts; ordinary slice modes are unchanged.
This is source evidence, not a claim that every backend/input combination was
executed or that GPU/device coverage is complete.

Disposable baseline source snapshot: owner H003g runtime repair worker,
/home/ts/.cache/agent-scratch/h003g-runtime-repair-baseline-20261001, 31 MiB,
purpose unchanged-main fixture control. It contains no scientific data and is
recoverable from Git; logs are retained here before removing that owned scratch.

Remaining gate: original R1 environment disposition, parent integration
and scheduled fresh installed entrypoint acceptance with synthetic inputs.
This source checkpoint is not live readiness or biological success. H003g
stays FAILED and is not a validation dataset for this repair.

Guard disposition at source checkpoint 63ad7c652: original CI-pinned R0
debt_ratchet.py (agent-comms 3b03785f45df2ef5dc62ba6aed99294192ecbb01,
SHA256 e323c94d49c2b72d9524a5169f123e64b4a6e46a41035ca9fb4497e49b6ca562)
and its direct owner dependencies are byte-identical in the existing cached
package. It ran with the CI's Python 3.14 using existing local dependencies:
production openhcs root PASS, 18.75 seconds wall / 89428 KiB RSS, one CPU,
512 MiB / no swap / 60 seconds. Earlier interpreter/dependency import failures
remain retained. Changed-source counts have no positive structural deltas.

The original scripts.check_refactor_r1 is NOT passing: the existing current
NRA environment fails to import RedundantTypeCheckDetector from the detector
package before scanning. The worktree's recorded dependency gitlinks are also
uninitialized, so full-context source materialization is not yet qualified.
No detector substitution, narrowed context, script modification, download or
dependency installation has been used to manufacture a passing result. Parent
integration must disposition/qualify the original R1 environment separately.

Merged-main source gate (2026-10-01)
-----------------------------------

Main 7b0ec3f5ab5a35a586d77c480fb7d5d6b1c85ba0 was merged normally, without
rebase, force push, runtime install or frozen trial modification. Merge commit
b770266428c5faac96069011c636fe93a1712acc is the original R0 head; the only
subsequent source changes add source tests (no production changes).

Original R0 compared exactly against main 7b0ec3f5: openhcs, scripts and
benchmark roots all PASS, respectively 17.65 / 2.52 / 3.37 seconds wall and
88244 / 59028 / 57892 KiB RSS. No detector or threshold was modified. All
shards retained one CPU, 512 MiB / no swap and a 60-second bound.

111 family controls PASS after this merge (3.33 seconds pytest / 4.10 seconds
wall, 322492 KiB RSS), including a direct full-stack identity test for object
labels, measurement tables/columnar rows, spatial graphs, aligned non-image
tokens and already-dense image/array carriers. 45 consumer controls PASS
(4.01 seconds pytest / 5.27 seconds wall, 372736 KiB RSS), including the
declaration-derived diagnostic ABI fixture correction. These 156 source cases
supersede the initial 33-case checkpoint, but are not fresh installed numeric
or native acceptance.

The two MRO cases contain real independent TEST capabilities: one changes
pixels, the other adds validity masks. Both use cooperative super through the
actual AlignedImageStack composition owner, and both orderings check exact
pixels AND masks. This proves that extension seam, not a new production MI
family or a complete NRA equivalence certificate.

Raw receipts, unsuccessful attempts and source/artifact SHA256 manifests are
retained in docs/refactor/receipts/cp-aligned-full-stack-342-20261001.tar.gz;
diagnostics/README.rst indexes their interpretation and replay commands.
The worker's 31 MiB disposable unchanged-main source snapshot was removed
after its processes completed and failure receipts were retained; it can be
recreated from the recorded Git commit. No H003g scratch, source, environment,
input, harness, logs or sealed data was changed.

Next acceptance belongs to the parent after #338: reviewed source must be
installed into a separately isolated candidate, then the actual installed
user entrypoint must execute matched synthetic aligned primary and auxiliary
images, retain exact typed outputs/masks/provenance and satisfy the raw
callable's dense ABI. Neither source tests nor old frozen H003g are substitutes
for that gate. Original R1 remains explicitly unqualified as described above.
