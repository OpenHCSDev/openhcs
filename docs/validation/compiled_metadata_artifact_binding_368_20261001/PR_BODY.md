## Working source fix for #368

Metadata injection was already correct in invocation kwargs; the unstored input
edge lacked its compiled metadata origin and requested image-source resolution
again. The existing input-edge owner now supplies a polymorphic unstored-payload
hook. Its metadata leaf consumes that same invocation-owned value through the
shared runtime loader. No duplicated metadata values/store, pixel_size switch,
required-input skip, arbitrary kwargs exemption or default calibration.

The original compile-only regression is extended in place through
FunctionCoreExecutor.execute: original source red (`resolved 0`), same test green.
Eleven controls pass, including hidden calibration **1.3556**, registered new
metadata provider, alias ABI, missing required value, unknown origin and stored
producer precedence through runtime. Original red/green and intermediate
failures are retained under docs/validation/compiled_metadata_artifact_binding_368_20261001.

Source shards are bounded to one CPU,512MiB,60s; existing installed native
extensions are borrowed read-only while affected Python owners load from this
worktree. No installed environment mutation or native/science endpoint launch.

Source qualified and frozen at production/test commit410164878:

- Full planner116passed; full patterns/runtime131passed.
- Wider edge/projection suite113passed/1failed. The SAME legacy-only declaration
  failure reproduces on unchanged base98d2 (4passed/1failed); exact required-binding
  contract/test conflict retained for parent triage, no compatibility workaround.
- New registered provider leaf composes two independent capabilities with real
  cooperative super/MRO. Positive value reaches the real callable; invalid value
  is rejected before success recording or invocation, without shared consumer edits.
- Original packaged R0: exact three production paths,5170metrics,zero positive
  deltas. Initial GodClassExcess+5 receipt retained; metadata injection/availability
  now belong to the inherited owner, old child algorithm/precheck deleted.

All shards enforce oneCPU/512MiB/60s; maximum measured RSS464252KiB.
Complete original-red/green, intermediate failures, base comparison, original
R0 and frozen source hashes are committed in the validation directory.
Draft is ready for parent source review and installed synthetic acceptance,
not an installed/live readiness claim. No install or cold preparation by author.
R1 issue357 remains BLOCKED, not a passing complete audit or waiver. Parent owns
installed MCP/native synthetic acceptance. The biological freeze stays terminal;
this PR does not replay it or establish biological acceptance.

Owner decision: IMPL-4, IMPL-13, BOUND-2; reject IDEN-5 duplicated authorities.
No invocation_artifacts.py/Dewey edit. Persisted/external formats: unchanged;
compiled edges are internal transient state. Source integration owner: parent.
