# Correct stale ABI-only artifact compilation regression

Source/triage owner: Lorentz. Integration owner: parent. This is separate from
#368 / PR #371 and does not modify their source or scientific freezes.

At current main `fe7ad23cc6ffc43eebac0e315d411142e4057364`,
`tests/unit/test_artifact_input_parameter_normalization.py::test_legacy_only_artifact_parameter_declaration_compiles`
fails with `Callable 'consume' artifact-fed parameter 'labels' has no exact artifact declaration binding`.
The unchanged file gives 4 passing tests / 1 failure; the same baseline conflict
was retained in #371's qualification.

The current authoring and architecture docs explicitly say `special_inputs`
declares Python ABI names, not semantic artifacts, producers or storage identity.
`CallableContract.validate_artifact_input_parameter_bindings` owns required
binding validation. Commit `4f43323681685f951299814268a92e51183d64b5` intentionally
moved that validation into compilation after invocation-contract provider
resolution. The compile-success test added earlier in `5e8812ee8` was not updated.
This is a stale regression expectation, not evidence that the production
compiler should accept an unsatisfied required parameter.

Repair scope: tests and authoring clarification only. Preserve both original ABI
metadata assertions; require rejection of missing exact declarations, including
an attempted authored-value bypass. Keep declared optional-default behavior.
Exercise successful finalized exact declarations through the existing typed
`InvocationContractProvider` extension point, including an independent semantic
name and genuine cooperative validation/receipt hooks. No production consumer,
compatibility reader, parallel registry/store, skip or weakened validator.

Acceptance: full normalization suite plus callable-contract/function-pattern
controls pass in bounded source shards; original failure retained; no `openhcs/`
changes. Native/science slot and installed validation remain parent-owned.
