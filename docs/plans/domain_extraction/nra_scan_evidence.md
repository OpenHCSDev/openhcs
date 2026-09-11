# NRA scan evidence

2026-09-11. Production source only; `--include-tests` was never used.
The working NRA tree is at HEAD `5f96c76358fe7c3be53af8d325bc513d693168e4`
with pre-existing uncommitted changes. Findings apply to that exact working
state, not a published release. All commands ran from the NRA repository.

## Full application context

Follow-up: NRA's scope normalisation, bounded collection lifetime and
overlapping-root parsing corrections now permit complete package-root scans
within the agreed budget. Final cold/warm measurements, roster completeness,
finding equivalence and regression results are maintained in NRA's
[performance reference](../../../../nominal-refactor-advisor/docs/plans/full_package_scan_performance.md).
The failures below describe the initial assessment, before those corrections.

```sh
.venv/bin/nominal-refactor-advisor \
  /home/ts/code/projects/openhcs/openhcs \
  --context-root /home/ts/code/projects/openhcs/openhcs \
  --json --json-payload agent \
  --parse-workers 8 --analysis-workers 8 --scan-budget-seconds 60
```

The initial default-budget run (20 seconds), a 150-second run, and a subsequent
60-second run all exited 124 with `deadline_incomplete` at
`parse_python_module`. The JSON explicitly reports `complete: false` and
`finding_count: null`. No whole-application finding or clearance claim can be
made from these runs. Repeated attempts did not establish a usable warm full
context cache during this assessment.

The user's subsequent budget direction permits up to 165 seconds for broader
scans and 60 seconds for focused scans. We did not keep increasing the deadline
after these incomplete attempts.

Generated raw reports and stderr are in
`/var/tmp/openhcs-domain-audit-kAEAjH/nra-package*.json` and corresponding
`.stderr` files. This is temporary evidence storage; the results and commands
are preserved here independently of those files.

## Component authority context

```sh
.venv/bin/nominal-refactor-advisor \
  /home/ts/code/projects/openhcs/openhcs/components \
  /home/ts/code/projects/openhcs/openhcs/constants/constants.py \
  /home/ts/code/projects/openhcs/openhcs/core/component_set.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/components \
  --context-root /home/ts/code/projects/openhcs/openhcs/constants/constants.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/component_set.py \
  --no-auto-context-root --json --json-payload agent \
  --parse-workers 4 --analysis-workers 4 --scan-budget-seconds 60
```

Result: exit 0, 3.859 seconds reported analysis total, 79 detectors analyzed,
none omitted, zero findings, zero plans. `scan_status.mode` is
`exact_compact_global`, **within these explicitly selected context roots**.
This does not mean repository-global completeness; omitted application
consumers and submodule implementations were not admitted source context.

An earlier invocation admitted only the components directory while reporting
two additional files. It failed with `CacheCheckoutPathError: ... outside
every admitted root`. The corrected invocation explicitly admits each root;
no cache or source code was changed to bypass the check.

Raw result: `nra-component-context.json` in the temporary evidence directory.

## Display and source consumer context

```sh
.venv/bin/nominal-refactor-advisor \
  /home/ts/code/projects/openhcs/openhcs/core/config.py \
  /home/ts/code/projects/openhcs/openhcs/core/source_projection.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/config.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/source_projection.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/components \
  --context-root /home/ts/code/projects/openhcs/openhcs/constants/constants.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/component_set.py \
  --no-auto-context-root --json --json-payload agent \
  --parse-workers 4 --analysis-workers 4 --scan-budget-seconds 60
```

Result: exit 0, 4.228 seconds reported analysis total, 79 detectors analyzed,
none omitted, zero findings, zero plans. Again, completeness is relative to
these admitted roots. The five-component display field/serialization coupling
and fixed source-address constructors are visible in source but were not
surfaced by this scan. The result does not establish that the consumers adapt
to a different component family.

Raw result: `nra-consumer-boundary.json` in the temporary evidence directory.

## Compiler consumer context

```sh
.venv/bin/nominal-refactor-advisor \
  /home/ts/code/projects/openhcs/openhcs/core/pipeline \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/pipeline \
  --context-root /home/ts/code/projects/openhcs/openhcs/components \
  --context-root /home/ts/code/projects/openhcs/openhcs/constants/constants.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/component_set.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/config.py \
  --context-root /home/ts/code/projects/openhcs/openhcs/core/source_projection.py \
  --no-auto-context-root --json --json-payload agent \
  --parse-workers 8 --analysis-workers 8 --scan-budget-seconds 60
```

Result: exit 0, 7.466 seconds reported analysis total, 79 detectors analyzed,
none omitted, one semantic boundary and no plans. The admitted roots remain a
bounded context, not the whole application or external packages.

The `external_enum_case_recovery` finding identifies `MaterializationBackend`
as an owner consumed through member-specific behavior in
`PipelineCompiler._configure_input_conversion_if_needed` and
`MaterializationFlagPlanner._resolve_materialization_backend`.
Source inspection confirms member checks at `compiler.py:361,387,600` and
`materialization_flag_planner.py:173-177`, with the enum declared at
`core/config.py:74`. This is useful compiler-path factoring evidence, separate
from the specific component-membership extraction. The resolved NRA authority
claim establishes a source relation, not proof that a new algorithm is correct.

Raw result: `nra-compiler-boundary.json` in the temporary evidence directory.

## Interpretation for the refactoring plan

NRA's source-aware operations and staged simulation can still provide leverage
after the practitioner selects the intended boundary. Detector discovery and
codemod applicability are separate claims. A zero-finding detector result is
not a declaration-propagation test, and parse-valid simulated edits do not by
themselves establish behavioral equivalence.

The goal must therefore retain source-backed inventories and alternate-schema
acceptance tests alongside NRA planning. The subsequent performance batch
resolved the broad-scan timing gate. Detection of distributed component
membership remains a separate capability gap, not a reason to ignore source
evidence or hand-apply an unreviewed large refactor.

A source-level limit is visible in the successful compiler detector:
`nominal_refactor_advisor/detectors/_systemic.py:1267-1337` selects indexed
classes with `direct_enum_member_names` and matches closed-axis branch sites.
The helper at `detectors/_base.py:2816-2841` similarly enumerates top-level
`ClassDef` enum declarations. OpenHCS creates `AllComponents` with the
functional `Enum(...)` API from configuration. That is a different declaration
shape from `MaterializationBackend`, which is a direct enum class. This
explains a limitation of that specific recovery path; it is not a proof about
all other detectors.

Future NRA work should recover declaration-derived families and repeated
field/map projections through their source authorities. A special detector
that merely recognizes the spelling `AllComponents`, or a hand-maintained
microscopy member list, would reproduce the very coupling being removed.
