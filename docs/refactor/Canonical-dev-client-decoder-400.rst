Canonical dev-client output-contract ingress: issue 400
======================================================

Source owner: Dewey. Installed integration/acceptance owner: parent Codex.
Base: main 49a95d8fb3da8ecb3dc4c1323332bd48b345f42e.
Scope: existing MCP dev-client ingress and its presentation controls only.

Original failure and disposition
-------------------------------

The original installed public388 attempt1 started native2153942 successfully,
then failed because ``startup.handle`` received a dictionary. No authoring,
fixture registration, compile or execution was reached. Do not replay startup.
Parent retains that exact live handle and owns subsequent observations.
The original failed attempt is not accepted or overwritten.

The unchanged external response is committed as
``tests/fixtures/mcp/start-owned-runtime-400.json``; SHA256
fe227ffa97abd12b8e394ca78b955616ab4ce522f771940f64d320bdeb33a6a6.
It matches the parent-owned original response byte-for-byte at
``paired397-388-installed-20261001/public388-attempt1/005-openhcs_start_owned_runtime-response.json``
under the issue-batch evidence root. Absolute paths are external golden data,
not a copied source/environment snapshot. Offline replay proves decoding,
not current process liveness or readiness.

Decision and owner closure
--------------------------

The existing owning ``McpDevToolResult`` now derives contracts from the
original capability declaration's ``output_contract_types`` and invokes
original ``python_introspect.dataclass_from_mapping``. Optional compact
presentation no longer grants permission to decode a declared result.
Unknown external tool names retain their original external result; known
contract failures retain their full external receipt and original errors.
All declared union alternatives are tried with unchanged per-alternative
rejections. Already typed instances and rejection receipts remain idempotent.
The shared owner's ``decoded_payload_as`` requires the requested nominal
member. Unknown raw receipts, rejected records and another declared union
member cannot masquerade as typed UI state/operation/workflow results.
This is one contract-directed boundary check, not a concrete-family switch.

Delete the three renderer/root/binding decode hooks in place, including the
raw no-op. The shared ingress owns the algorithm, not renderer leaves.
Existing polling helpers consume the now-decoded bridge-operation and state
document envelopes; only the state document's declared dynamic JSON body
remains a mapping. Delete their replaced outer mapping readers and second
bridge-operation decoder. No per-tool dictionary conversion, renderer
workaround, registry/schema roster, compatibility facade or engine change.

Current NRA/refactor-audit review: BOUND-2 (declared DTO bypass), IMPL-4
(half-migrated family), and MEMB-2 (presentation membership substituted for
contract admission). The new-case test adds only its original capability and
output declaration, with no generic consumer edits or renderer. Its result
combines an independent description capability with the original envelope
ancestor and executes cooperative ``super()`` to produce
``independent:owned`` after real nested ingress decoding. This is meaningful
MI behavior, not an inheritance assertion or ornamental production class.

Source evidence and limits
--------------------------

Original seven-case red: 7 failed, 5.34s / 251.78MiB, retained at
``validation/canonical-decoder-400-original-red.{json,log}``.
First correction: 7 passed, 4.98s / 251.75MiB.
Expanded controls initially exposed 5 failures / 87 passes (12.88s /
258.16MiB): two decoder-location spies and three obsolete outer-mapping
polling assumptions. That failure is retained, not waived.
Corrected complete dedicated decoder/presentation controls: 92 passed,
7.83s / 258.09MiB. Includes actual saved nested runtime handle, renderless
cooperative new case, both declared union branches and unknown union shape,
strict unknown outer/nested fields, invalid nested values, original errors,
unknown tools, empty/rejected payloads, pipeline/config/action families,
compact CLI journeys, runtime-debug, transport and generated-input controls.
Two existing unknown pytest async-config warnings remain recorded.

Shared-controller expansion initially exposed 7 failures / 186 passes,
27.39s / 321.15MiB. All seven were incomplete mock outer envelopes,
constructed directly as raw ``McpDevToolResult`` values without the required
``UiStateSurfaceDocument`` schema/summary/payload-schema declarations.
The real wire and existing dedicated CLI tests already supply those fields.
Complete mock envelopes now derive from the original DTO's serialization;
their intentionally partial dynamic JSON bodies and every original scope,
terminality, recovery, call-count and summary assertion remain unchanged.
No production compatibility reader or permissive decoding was added.
Two intermediate fixture-constructor mistakes (keyword-only identity and
required inherited widget identity) are retained in separate failed logs.

Final combined dedicated/shared controls: **288 passed**, 26.04s /
313.53MiB, 105 unrelated/native cases deselected. This includes all 95
dedicated cases and all 193 shared source dev-client cases; the actual fresh
server test is excluded because source-worker native/MCP launches are
prohibited. No affected source control is waived. New nominal-member tests
cover unknown raw/rejected UI access and both actual declared union members.
Final command/log: ``validation/canonical-decoder-400-complete-controls-final``.

Every source test uses one CPU, unchanged 60s / 512MiB combined process-group
limits, readonly existing dependency interpreter, own source explicitly and
a subprocess guard. No worker native/MCP/UI process, lock, installation,
download, model/provider call, parent environment/fixture edit or mutation
replay. Installed public author/compile/execute, exact
labels/rows/persistence and process closure remain parent-owned and pending.
No biological, snapshot or global NRA FULL qualification is implied.

Original pinned R0: **PASS**, 15.49s / 85.28MiB, main49a95 to source/test
head efa51897d27be16653723d837b3abe3f217a525a, 5170 entries, no positive
delta; ForeignAbsenceProbe on the shared ingress decreases by one. Actual
Python3.14 original pinned tool and readonly metaclass backing paths were
asserted, no copied detector/engine change. R0 command/log:
``validation/canonical-decoder-400-pinned-r0``. This is the source debt
guard, not global NRA FULL acceptance or installed/runtime qualification.

Ruff F checks pass for both production files and all dedicated modified
decoder tests; diff whitespace checks pass. The shared server-test file has
two unchanged pre-existing F401 viewer imports, independently reproduced
from base49a95. They are outside the decoder changes and remain explicit;
no lint cleanup of another viewer owner's imports is bundled here.

Immutable source archive (20 command/receipt/log files including every
original/intermediate failure and final controls/R0, no redundant source
snapshot/environment):
``docs/refactor/receipts/canonical-dev-client-decoder-400-source-20261001.tar.gz``;
SHA256 06d9c73a82ae7e1c58eb1213da3398a3e1a349ec939bc69bf1e1992145f4c351,
156KiB allocated. Tar comparison against the retained originals passed
without extraction. No new build/install/cache directory was needed.

Driver checkpoint
-----------------

PR388 preparation remains at 0ae714fae83e63199434c72d4603daa9dacb7e24;
driver SHA256 d3f259fae72ed5f70117646befa6b68a8301e168d785a7a56159cce1726bfd23
is unchanged on disk. Its original actual attempt1 stays failed. This
independent decoder branch does not include classification388 production or
the frozen driver. Duplicate source issue401 was closed in favor of issue400.
