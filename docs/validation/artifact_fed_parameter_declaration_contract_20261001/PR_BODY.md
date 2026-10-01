Fixes #375. Source/triage owner: Lorentz; integration owner: parent.

Tests/docs-only repair of a stale baseline assertion, separate from #368 / #371.
The existing exact-declaration validator is correct and unchanged: `special_inputs`
names ABI slots, not semantic artifacts. Commit `4f4332368` intentionally validates
finalized input contracts during compilation; the earlier ABI-only compile-success
test was not updated.

The patch preserves both original ABI metadata assertions and strengthens
required-binding rejection at contract and public compiler boundaries, including
an authored-value bypass attempt. Existing positive exact/matching declarations
and conflict assertions remain. Declared optional defaults still work.

A new typed invocation provider finalizes exact input semantics through the real
public compiler. Its validation and receipt capabilities use cooperative `super()`:
`start -> declare -> validate -> ready`; an empty declaration rejects before ready.
An independently named artifact binds the same ABI with no shared consumer edits.
No compatibility reader, parallel roster/store, validator skip or production change.

Validation: original current-main file4pass/1fail preserved; repaired file9pass;
full callable-contract/function-pattern/normalization shard97pass. OneCPU,
512MiB,60s enforced per shard; maximum measured RSS429376KiB. Complete command,
resource, red/green and hash receipts are under
`docs/validation/artifact_fed_parameter_declaration_contract_20261001`.
Production tree is byte-identical to base `fe7ad23cc`; R0 has zero changed
production targets. R1 #357 remains blocked, not a full audit claim or waiver.

No install, native/science endpoint or model/external-provider call. Parent owns
installed acceptance. PR371's source freeze is unchanged; the biological trial
remains terminal/unmodified.
