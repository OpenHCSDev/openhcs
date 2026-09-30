Issue314: paired-field measurement identity
=========================================

Head audited: OpenHCSDev/openhcs main702b2c2c9563da2636db251f8b734cff215596b8.
Fresh isolated branch fix/paired-field-csv-314-20260930 in
/home/ts/wt/openhcs-paired-field-csv-314-20260930. Parent integration owns final
source/MCP acceptance; Russell owns this source reproduction and repair.
H003e remains an immutable REJECT: no reads of its scientific inputs/outputs,
no rerun, tuning, CSV repair or freeze mutation for this task.

Instruction review before production implementation
--------------------------------------------------

Read complete nra-refactoring SKILL.md (SHA256
9f2f8b28bc82256eefa3e9d63248c50722dc3ffe7d77adba5793296df196b47e), complete latest
refactor-audit.skill ZIP entrypoint, pattern README, full identity/boundaries/
membership/implementation references and surface-receipt template. Archive SHA
100fbe8ef89664b866777e87b2c8640a3432e8a10e9188dff81c97942d551bf6.
The following IDs are actual catalog IDs, not guessed NRA detector findings:

* IDEN-1: source_matching.py:475..488 uses presence of a declared component
  both as a biological plane address and as image-set plane membership.
* IDEN-6: image_set_numbering.py:45..55 keys the source identity produced by
  that policy. Fully addressed DNA/Actin bindings make every source component
  a plane member; SourceImageSetIdentity.from_metadata (:550..566) then falls
  back to two different filenames. This is the earliest broken identity rung.
* BOUND-2 prevention: NamedSourceBinding.component_values() at
  source_bindings.py:1015..1040 already owns assignment-versus-selector value
  precedence. Use it instead of creating another coordinate/value reader.
* IMPL-1/2, MEMB-1/2/5 prevention: no axis-name/module-name strings, consumer
  switch, parallel registry, policy mirror or duplicated row schema. Existing
  AllComponents, ComponentSet, binding/policy/provenance/row owners suffice.

Current-head census and proof scope
----------------------------------

Archive debt_census.py scanned all179 tracked core Python files at this head:
91295 code lines; no parse-failure warning. Core totals: string_dispatch7,
type_switch29, string_key_subscript274. These are syntax screens, not diagnoses
or a whole-repository architecture verdict. source_matching.py:824 code lines,
zero string dispatch/type switches/string-key subscripts, one four-term chain,
four foreign absence probes. Source witnesses, not these counts, establish314.
core-census.json/log and core-overlay.json/log retain unfiltered observations;
unrelated overlay leads are not assigned to this issue.

Full NRA scan attempted with complete openhcs context, requested policy/numbering
files, --json --raw-findings --json-payload full, parse/analysis workers1,
--no-cache and an enforced512MiB/one-CPU/60s scope. It terminated exit124 with
maximum RSS524536KiB and an explicit deadline_incomplete JSON result:
complete=false, deadline_exceeded=true, stage=parse_python_module,
budget_seconds20.0, elapsed_seconds22.054. Original stderr/resource receipt retained.
Do not call this complete, zero omissions, R1 evidence, DSL preflight, native
proof, or formal equivalence. The confirmed stopping condition is the internal
parse deadline, not a demonstrated OOM. Observed process peak slightly exceeds
512MiB despite the scoped cap; a repeat is not admitted under this RAM budget.
Required resources for a complete context scan remain unknown; no global limit
was raised. There are no R1
mapping_read/unmodeled_record_shape/redundant_type_check findings to certify.
This repair is an explicitly authored semantic patch, not an NRA-generated plan.

Follow-up one-module compact loop reports79 detectors,0 omissions, complete=true
and zero findings for source_matching.py alone (nra-owner-loop.json). Do not
extend that completeness to the failed full-package context. Source commit
6f636c2afe6d98cc has +16 core code lines and zero debt-screen delta in every
other measured category; owner-census-delta.json retains exact observations.

Original failing reproducer
---------------------------

New tiny synthetic fixture in test_cellprofiler_spreadsheet_export.py uses
two fields, two cells per field, full well/site/channel/z/timepoint addresses,
typed SourceImageProvenancePlanes, ordinary RuntimeExecutionAxisScope and
RuntimeArtifactBatch. It calls the real export_to_spreadsheet function. Literal
small feature rows stand for known synthetic measurements; this is not a
segmentation or installed/native-process test and reads no image files.

Policy from fully addressed paired bindings loses four shared fixed axes as
well as the varying channel. Both primary/secondary features have the same
axis_id, local slice/object IDs; separate DNA/Actin paths cause duplicate rows.
Original built-source test fails with8 partial rows instead of4 complete rows
(reproducer-original-built.log), maxRSS311488KiB,3.96s. Initial collection failed
because the fresh checkout lacked _tabular_native; retained reproducer-original.log.
Built existing unchanged setup.py extension declarations locally (no installation,
JVM/server/viewer or dependency changes), maxRSS144720KiB,4.02s; source-build.log.
Owner-policy import was40MiB and resolved this worktree, policy-import.log.

Required relation and owners
----------------------------

CellProfiler ImageNumber identifies a source IMAGE SET, not the currently
selected channel, measurement module, local slice position or provenance path
when semantic coordinates identify the set. A full plane address does not
declare every address axis to be a stack member. Across a paired primary-plane
declaration set, equal singleton component_values are fixed field coordinates;
different/unresolved coordinates remain plane selection dimensions under the
existing binding rule. Explicit source_stack_components and group_component
remain authoritative, even when their current coordinate happens to be equal.
One-plane binding contexts retain their existing selection semantics (there is
no cross-binding equality witness); no compatibility facade/reader is added.

SourceImageSetIdentityPolicy.from_source_bindings owns the repair. It compiles
plate-wide via from_pipeline_config at compiler.py:207..209 and travels as the
same typed value through ProcessingContext and RuntimeArtifactBatch. Provenance
continues to retain original plane paths and coordinates. RuntimeExecutionAxisScope
keeps independent execution axes. CellProfilerImageSetNumbering consumes the
policy unchanged. MeasureObjectSizeShapeModule retains declared object identity
and feature semantics; spreadsheet_export.py:296..300/:398..413 continues its
ordinary typed row projection/union. No stored-format change or frozen migration.

Ownership crossings and destination
-----------------------------------

Open PRs309,217,207,206,160,125,110 checked with exact changed-file lists. PR206
touches source_bindings.py; PR217 (Avicenna) touches runtime_image_values.py and
runtime_plane_projection.py. Those files stay read-only in this repair.
Existing binding/provenance owners are consumed, not edited or duplicated.
Notify Avicenna directly if any of those shared owner implementations become
necessary; do not compete with their worktree. No new coordinator or worker.

Replace only from_source_bindings' unqualified component-collection expression
with a derivation that excludes shared fixed cross-binding coordinates from
binding-selected membership. Keep explicit stack/group membership. No new
carrier/store/registry. Destination new-case experiment: add another plane
binding or different semantic field coordinates through existing declarations;
the consumer/exporter changes0 times. Tests cover independent site/z/time/well
and execution identities, explicit stacked equal-coordinate axes, column/label
semantics and existing applicable source-level CellProfiler contracts.

Done when the original behavioral failure passes, controls preserve separate
fields and declared stacks, applicable provider-free source tests pass, changed
owner census adds no dispatch/raw-record/schema mirrors, and one coherent draft
PR is visible with original failures and exact proof limits. Live/native/JVM,
installed-entrypoint, external-oracle and biological acceptance remain parent
owned and unclaimed. Local focused tests are not full acceptance.

Resources and disposal
----------------------

Preflight: warning-only20GiB policy; home12.5GiB free, availableRAM15.6GiB,
historical swap8.7GiB. Worker512MiB and CPUQuota100percent/threads1 enforced;
owned scratch ceiling256MiB at /home/ts/.cache/agent-scratch/issue314-russell.
Source, failures and handoff stay in this persistent worktree. Archive/preserve
failure logs and remove only owned disposable caches/builds after workers exit.

Durable .issue314/ (41MiB) holds the extracted current instruction archive and
original702b2c2c9 source snapshot for the inherited-failure control. It is local,
not a published source change. Disposable scratch measured652KiB; local build
objects400KiB. No task process remains running at this checkpoint. Existing
locally built extensions are not installed globally. Full test/dependency proof
limits and inherited fixture ownership are recorded in checkpoint.rst.

Current merged-head receipt: e3d991e9cf02c496daa7c9df32c73bfde4a7ad00 integrates
main2b7969f700c33eb7f73f891d975afd1efc0628bb without changing shared owners.
merged-main-census.json compares those exact revisions: +16 code lines, zero
other syntax-screen deltas. Production/test checks at this head pass131 of139
selected tests; eight inherited strict-subject fixture failures are retained and
assigned to parent integration for disposition, not masked. Owned scratch/build
disposal is complete and recoverably archived; checkpoint.rst records paths/SHA.
