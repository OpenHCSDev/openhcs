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
stack. It does not read the trial images or scientific outputs. The executor's
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

Initial working gate
--------------------

33 source cases passed, 2.35 seconds pytest / 3.08 seconds wall,
305672 KiB RSS. One CPU and a 512 MiB cgroup with no swap, 60-second timeout.
The isolated installed interpreter supplies existing dependencies; the source
runner resolves this worktree's Python code and only the unchanged installed
``_tabular_native.abi3.so`` artifact. No download/build/install is performed.

The first complete-package NRA attempt rejected a misdeclared context root.
The corrected whole-package plus recorded external dependency scan timed out
at 60 seconds with 511664 KiB RSS. No complete global semantic/proof certificate
is claimed. Manual ownership evidence and source behavior tests are distinct.
The initial slotted-dataclass zero-argument super failure is retained and fixed
with explicit cooperative super(AlignedImageStack, self), not suppressed.

Remaining gate: broaden family/metadata/mask/projection controls and regression
consumers, then parent integration and scheduled fresh installed acceptance.
This working source checkpoint is not live readiness or biological success.
