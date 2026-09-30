# Issue315: planning admission and converted checkpoint publication

Head audited: main `702b2c2c9563da2636db251f8b734cff215596b8`, including
merged PR310. Source-only owner: Avicenna; integration/live acceptance: parent.
Frozen H003e REPRODUCERS.rst was read; no trial replay or artifact alteration.

## Boundary and witnesses before changes

- `pipeline/path_planner.py::_cached_results_path` admits absolute external roots
  without the plate containment required by
  `steps/function_outputs.py::RuntimeArtifactMetadataTarget.from_plan` (1125).
  The existing `PathPlannerPathAuthority` owns path geometry; publication must
  not discover a planner-admitted inconsistency after persistence.
- `steps/function_runtime.py::_unwrapped_main_flow_output_context` (3239)
  returns no new context for unnamed replacement images. Both unstacking paths
  then reuse producer contexts; converted pixels can inherit an object-label
  artifact kind. `CompiledFunctionGroup` already distinguishes a final unnamed
  replacement from `preserves_input_main_flow()` and owns that contract fact.
  `ProducedOutputSemantics.is_image_payload` correctly excludes objects;
  `AtomicMetadataWriter` correctly refuses missing produced addresses.

Baseline06 reproduces both remaining defects through public compilation and
real in-process execution: external results compile (expected rejection fails),
and the replacement's inherited object context prevents checkpoint persistence,
then metadata publication fails because its directory has not been created.
This is an earlier symptom than the frozen missing-address finalization; the
same producer-context gap is present. No claim of identical frozen traceback.
Relevant
catalog patterns: BOUND-2 (ignoring an existing typed contract authority),
IDEN-1 (input producer identity reused for a replacement output), IMPL-13
(planning and persistence enforce different geometry). Do not change valid
object filtering or weaken final reconciliation.

## Target and deletions

Use existing path and compiled contract owners. Reject unsupported results
geometry in planning, with a named diagnostic. Resolve a replacement's producer
context from the compiled group; retain exact input contexts only for actual
passthrough contracts. Delete the corresponding late-admission/context gap in
place. No concrete-function classifier, inferred filenames, permissive fallback,
new store, compatibility path, or PR206/217 file edit.

## Tests and new-case experiment

First qualify tiny synthetic root admission and object-to-image checkpoint
journeys on unchanged main. Then verify nested/relative roots, saved TIFF
addresses/provenance/calibration, unchanged object/table publication and true
passthrough producer identity. A new unnamed replacement currently needs its
callable plus consumer knowledge to avoid inherited object semantics (2 sites);
afterward its existing callable contract suffices (1 declaration). A new root
consumer currently needs to rediscover containment; afterward it consumes the
existing planner's admitted path without another admission rule.

## Guards and constraints

Original CI-pinned structural ratchet remains unmodified. Retain raw baseline
failures and actual metric inventory/deltas. R1 is distinct from source tests;
missing dependency objects are a failed prerequisite, not a pass. Single CPU,
512MiB projected RAM, 256MiB owned scratch. Resource preflight reports warning
(15.7GiB available; /home free12.2GiB; swap8.7GiB). Initial source imports use
263532KiB RSS. Reuse only the existing local stable-ABI tabular extension;
its C++ source hash matches this checkout exactly. No install/build/server/GUI.
Scratch: `/home/ts/.cache/agent-scratch/artifact-publication-315-20260930`.

Russell issue314 scope crossing notice:
https://github.com/OpenHCSDev/openhcs/issues/314#issuecomment-5920738225.
No edits to workspace/preparation, measurement identity or spreadsheet owners.
Final source proof is not installed/MCP acceptance; parent owns that boundary.
