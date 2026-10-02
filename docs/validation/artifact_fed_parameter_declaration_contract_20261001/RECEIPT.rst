Issue375: ABI-only declaration contract regression
==================================================

Source/triage owner: Lorentz. Integration owner: parent.
Independent worktree/branch:
/home/ts/wt/openhcs-artifact-fed-parameter-declaration-contract-20261001
fix/artifact-fed-parameter-declaration-contract-20261001.
Base/main fe7ad23cc6ffc43eebac0e315d411142e4057364.
Issue https://github.com/OpenHCSDev/openhcs/issues/375.
No PR371 source/evidence rewrite, installation or native/science-slot use.

Diagnosis and current contract
------------------------------

The failing legacy-only compile-success assertion is stale. special_inputs
marks Python ABI slots, not a semantic ArtifactSpecRef, artifact type, producer
or runtime-store identity. This separation is explicit in the current
callable_artifact_authoring.rst and artifact_contract_system.rst documents.
The public decorator spelling and metadata snapshot remain supported unchanged.
An ABI-only parameter with a genuine Python default may use that default.
A required artifact-fed parameter must have an exact finalized declaration.

CallableContract.validate_artifact_input_parameter_bindings owns this validation.
InvocationContractProvider.__call__ can first supply a finalized typed contract.
_compile_invocation resolves that provider, then validates the finalized input
ABI, before dependent output obligations. Commit
4f43323681685f951299814268a92e51183d64b5 intentionally added that validation
on2026-09-30. The earlier test from5e8812ee8 still expected an unsatisfied required
ABI slot to compile successfully. No evidence warrants relaxing production.

Repair and ownership patterns
------------------------------

Four obsolete test lines removed; original ABI-name/empty-semantic-input
assertions retained against the original CallableContract snapshot. Required
missing bindings now reject at BOTH contract and public compilation boundaries,
including an attempted authored-kwargs bypass. This replaces an unsupported
success assumption with stronger fail-closed coverage, not a required-input
skip, assertion weakening or validator change. Existing exact-only, matching,
conflicting and compiler-finalized binding tests retain their assertions.
The authoring guide now states the required/default/provider distinction.

BOUND-2: use the original CallableContract and ArtifactSpec owners.
TIME-1/TIME-3: do not add an old loader, compatibility facade or special_inputs
origin inference. The production declaration reader, provider roster and public
decorator are unchanged. IMPL-4/IMPL-13: exercise the existing provider ancestor
and consumer rather than adding a parallel compilation path.

Independent new-case evidence: _CheckedInputProvider composes
_RecordFinalizedInputs, _ValidateFinalizedInputs and _DeclaredInputProvider,
the latter deriving from the original InvocationContractProvider ABC. Its
minimal hook returns the original InvocationContractPlan/CallableContract.
Cooperative super() executes start -> declare -> validate -> ready through
real compile_function_pattern. Both StoredLabels and independently declared
IndependentSeedRegions bind the same labels ABI without consumer edits.
Removing the exact declaration rejects through the validation capability;
only start -> declare occurs and the receipt capability cannot report ready.
Public callable metadata remains empty, proving provider-finalized semantics
were not mirrored back into another authority. These are compile-time provider
behavior proofs, not a runtime artifact-origin or installed native proof.
The optional case directly invokes the unchanged public callable to verify
its real declared None default, with no injected kwargs or invented edge.

Executed evidence and bounds
----------------------------

original-red.xml: untouched current-main file4passed/1failed;
5.66s,417556KiB RSS,exit1. Full original traceback retained byte-for-byte.
normalization-green.xml: repaired file9passed;5.06s,422332KiB RSS,exit0.
contract-pattern-shard.xml: full callable_contract, function_patterns and
normalization files97passed, including those9cases;6.04s,429376KiB RSS,exit0.
Black formatting of the one edited test file succeeds. Source/docs whitespace
check passes; raw pytest traceback XML whitespace is preserved as evidence.

Every test command in *-resources.txt uses systemd-run --user --scope,
MemoryMax512M,CPUQuota100percent,timeout60s,one numeric thread pool, and the
existing parent Python interpreter read-only. The already frozen PR371
source_shard.py entrypoint is REUSED READ-ONLY, with OPENHCS_SOURCE_TEST_ROOT
and PYTHONPATH set to THIS worker root. It verifies affected Python modules
load from this checkout and borrows only the existing native extension ABI.
Entry-point SHA256:
05f7dd98f7a449a0d86863b163807f700ba328cc9c5a1225c8fe66dd4a1634a2.
Read-only native SHA256 values:
tabular fc974871e5707199fbde83421b07d2c0c808310b0b46fc639b7b78b53f2e406f;
granularity 9f873070c3e136dd78109a55570852981e989c1d21e3452ce214bbaa753b7308.
No copied scientific loader, package install, environment mutation, native
worker/server/viewer, canonical lock, extra agent or model/provider call.

Exact production guard and frozen edited artifacts
--------------------------------------------------

git diff --exit-code fe7ad23cc6ffc43eebac0e315d411142e4057364 -- openhcs
returns0. Entire production tree is unchanged, not merely selected functions:
036015cede647ab84aad7eb6212aa9f5ffd087af.
R0 has no changed production targets in this tests/docs repair. No new R0
measurement or full NRA scan is claimed; PR371 original R0 evidence remains
unchanged. R1 remains BLOCKED #357, not a waiver or completed global audit.
No source ABI, persisted format, runtime state or package dependency changed.

Edited test SHA256:
9307b32bc0404e7ffad6b779cde9c1d846fd9411976833a2289b6100fd59e7b4.
Edited authoring guide SHA256:
204bc980bf4eb9b8d388e17ea9510c15baea62dbd42cbce19b71aa59119a0b53.
SHA256SUMS indexes all owned retained evidence except itself.

Resource check before the shard returns advisory warning/exit2:
RAM21.0GiB available,home8.2GiB free,swap10.7GiB used. The disk advisory is not
the task threshold. All actual shards stayed below512MiB/60s with one CPU.
Only owned .pytest_cache44KiB is disposable and removed after tests; no other
scratch was created. Source and red/green receipts remain persistent.
Parent alone retains the native/science slot and installed validation authority.
The original blinded biological freeze remains terminal and unmodified.
