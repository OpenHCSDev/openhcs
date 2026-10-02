GrayToColor #432: source diagnosis, not an installed repair
=========================================================

Owner: Schrodinger. Base: df15ddfe0bcbd80cadaf2f5fc56b83517910f334.
Existing isolated worktree: openhcs-knowledge-declaration-source-376-20261001.
Branch: fix/graytocolor-role-axis-20261002. Normal fast-forward main integration;
no reset/clean, new environment or dependency mutation. The untracked owned
required-runtime-qt-publication-20261002 ledger is preserved and excluded.

Original evidence
-----------------

Issue: https://github.com/OpenHCSDev/openhcs/issues/432.
Installed predecessor fa04956a7eb3212e3456cf9927fc35ab6cdfd361 / PolyStore0.3.1.
Original native PID3214331/create_time1790918404.81/port5993. Terminal execution
37f69b64-2331-4bcb-a4f1-99f78da3d316 (v1) and
c81af5db-f805-434a-a067-930d5201975c (v2) both fail at
RetainRawCalceinBodyReference, completed0/total4. No failed call was replayed.

Original persistent MCP evidence is under
/home/ts/wt/openhcs-issue-batch-20260929/neurite-development-skill383-20261001/
output/assisted-3-fa049/mcp.stdout, lines5365..5421 and6724..6780.
Complete source drafts at the same prefix:

* c8-composition-control-v1.py, SHA256
  4dc60002f89b9a7851a66deebf6c504963aeeb83e28455ff58e56367f8f9d2da
* c8-composition-control-v2-explicit-source.py, SHA256
  ee319fa08303c6bba8280b4ba254863a576e15343f5fc85745a56a7931455ae0

Original native log named by the exact saved native-handle.json:
/home/ts/.cache/agent-scratch/neurite-development-skill383-20261001/
assisted-3-fa049/data/openhcs/logs/
openhcs_zmq_server_port_5993_1790918405617427245.log.
Only its two exact failure trace excerpts (238..278,714..754) are captured here
in original-native-excerpts.log. The scientific author retains the original;
no scratch/process/output was modified. v3's scalar-file/declared-stack-axis
compile rejection is separate authoring evidence, not a product regression.

Proven relation and source result
---------------------------------

test_gray_to_color_binding_axis_432.py reuses the original public FunctionStep
compiler, exact source-declaration input-edge construction, original nominal
RuntimeAdapterRequest fixture, CellProfilerModuleExecutor._image_request and
_invocation_request, and CellProfilerFunctionContractExecutor. Synthetic 4x5
arrays only; no TIFF/image-array read, provider or live process call.

Both implicit and explicit FITC selection compile to exactly one declared FITC
input. The original request retains its real C2 physical source identity and
RUNTIME_SLICE carrier. compose_aligned_image_payload's single-input fast path
returns that payload unchanged. The declaration's image-request hook is the
ancestor no-op. PURE_3D/NATURAL then reaches gray_to_color's SOURCE_BINDING-only
guard with RUNTIME_SLICE, reproducing the exact original error. This is a
missing declaration/consumer-domain adaptation, NOT evidence that the loader
assigned incorrect physical channel identity, nor authority to relabel axes.

The positive owner-algebra experiment explicitly projects a declared runtime
slice through RuntimeSliceProjection, THEN introduces the distinct named role
axis through ImagePayloadBundleContext. The unchanged original executor and
STACK runner accept that SOURCE_BINDING domain. No arbitrary squeeze, metadata
overwrite to impersonate a binding axis, relaxed guard or consumer switch.

Two independent named processing roles composed through the original bundle
owner and registered STACK executor preserve their ordered floating-point
values (raw 0..19000; capped 0..1), spacing/domain and SAME original physical
C2 path/channel. Changing both role declarations requires no consumer edit.
These are source composition controls, NOT the entire four-step saved-artifact
journey, public TIFF unit calibration or installed acceptance.

Two additional boundaries prevent a false full-repair claim:

* STACK emits YXC/color metadata even for one role. It is not an identity
  renamer of a scalar gray plane. Feeding that one-color-channel output back
  into the same original grayscale STACK binding creates a 4D input, and the
  current registered runner rejects it (axes don't match array). The synthetic
  control proves that additional boundary, not that Dalton reached it live.
* ImageArtifactTypeStrategy.runtime_input_value normalizes uint16 before the
  kernel's rescale_intensity argument: the actual original binding experiment
  maps integer values to float32/65535 and leaves the source unmodified. Merely
  passing rescale_intensity=False is not proof of preserved raw integer units.
  No claim is made about the unseen TIFF values/dtype or scientific calibration.

Ownership and proposed integration boundary
-------------------------------------------

Root retains PR394 executor/input context, source projection/metadata and
shared materialization. PR394 also lists color.py. Explicit narrow declaration/
backend release or Root integration requested before any production edit:
https://github.com/OpenHCSDev/openhcs/pull/394#issuecomment-5946253275.
No release received at this checkpoint; production files are untouched.

Required original-owner seam: CellProfilerModule.project_invocation_image_request
(ABI ancestor) with minimal GrayToColor declaration hook, backed by existing
runtime-slice projection and named-bundle composition owners. Establish the
binding domain, do not reinterpret a runtime axis as a named binding. Preserve
the SOURCE_BINDING guard. Any generalized singleton composition template or
raw-unit ingress policy belongs to Root's existing shared owner, not a second
color-local executor/binder. The complete requested four-step route must also
resolve the scalar-gray versus STACK-color relation before claiming acceptance.

NRA/refactor-audit review
-------------------------

Personally reread installed nra-refactoring and refactor-audit SKILL.md;
authoritative ZIP's entire SKILL.md, catalogue, boundaries, implementation,
identity and surface-receipt references; project docs/refactor/00-RULES.md.
Applied BOUND-2 (bypassing the existing model) and BOUND-8 (flattening an owned
fact) to binding-domain adaptation; IDEN-1 (one field answering two questions)
to independent runtime/binding axes and IDEN-5 to forbidding a second identity
store; IMPL-1/3 to excluding string/concrete-type consumer dispatch, IMPL-12 to
avoiding a copied projection procedure, IMPL-13 to avoiding a less-rigorous
second composition mechanism. No production algorithm moved, facade,
duplicated registry, consumer
type/string switch or ornamental MI was added. No removed/replaced production
code exists at this diagnosis checkpoint. No new family/MRO behavior claimed;
any repair must test cooperative hooks on the actual owner after release.

Bounded evidence and limits
---------------------------

Existing read-only Python3.12.3:
/home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/bin/python.
Existing source/ABI loader: docs/validation/knowledge-selected-source-tests.py.
Every shard: systemd scope MemoryMax512M/MemorySwapMax0/CPUQuota100%, tasksetCPU0,
timeout60s, all numerical thread pools1, no conftest/plugin autoload/cache writes.
Advisory resource check: RAM14.9GiB/home12.3GiB; advisory disk warning retained,
actual bounded source admission held. Exact retained invocation is in each log.

* Initial two-case source RED: 2fail/5.58pytest seconds, 6.42wall seconds,
  350640KiB RSS, exit1 (original tool transcript; not claimed green).
* source-diagnosis.log: same two RED + four distinct controls PASS, 6.01pytest
  seconds/6.94wall seconds/350904KiB RSS, exit1.
* integer-binding-units.log: one additional control PASS, six deselected,
  5.52pytest seconds/6.44wall seconds/348924KiB RSS, exit0.

Total distinct cases: two unresolved RED, five passing diagnosis/negative
controls. Existing pytest unknown-asyncio-config warnings retained. No full
R0/R1 retry/global NRA qualification: zero production change and unrelated
historical global scope remain distinct. No installed/native/GUI/biological
readiness claim. Parent owns future installed original entrypoint acceptance.
Owned potential scratch address graytocolor-role-axis-20261002 was never
materialized by these tests; observed absent after terminal shards, no cleanup
performed. All durable source/logs retained; no new environment/artifact fleet.
The final test strengthens unreachable post-RED acceptance from a shape reshape
to exact nominal RuntimeSliceProjection and YXC shape; that post-repair check is
not executed/qualified at this diagnosis checkpoint. Raw pytest logs retain
four trailing-whitespace warning lines; whole diff-check is NOT clean. Source
test/receipt-only diff-check passes; original evidence is not reformatted.
