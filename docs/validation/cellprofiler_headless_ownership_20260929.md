# #138 nominal bootstrap ownership receipt

Integration owner: `openhcs-architecture-memory`. Implementation owner:
`openhcs-headless-bootstrap-worker`. PR: https://github.com/OpenHCSDev/openhcs/pull/207.
Scope: `scripts/bootstrap_cellprofiler_headless.py`, its focused guard and
regressions. This is a real-source/AST audit, not a complete NRA scan.

## Witnesses and actual checks

The coordinator identified real debt in the first published checkpoint
`cfda8f330eae72d6651da19b35e2b41999d804bd`. The implementation owner read the
current archived refactor-audit catalog and checked that source directly:

| Pattern | Published source witnesses | Replacement |
| --- | --- | --- |
| IMPL-7 / IMPL-1 | Five `args.command` comparisons in `main`, lines 458, 461, 473, 476, 499; `create` was the implicit remaining arm | Deleted; selected command instance owns `execute()` |
| MEMB-1 | Literal five-name parser choices at line 436 | Deleted; parser membership and constructor lookup project concrete command declarations |
| MEMB-2 | Central package membership sets at lines 205–206 | Deleted; package policy belongs to each install stage |
| IMPL-1 | Central package-to-stage comparisons at lines 210, 214, 221 | Deleted; ordered stage declarations select/consume remaining pins |
| BOUND-1 / BOUND-2 | Raw JSON decoding in preflight/verify at lines 121, 404 | Deleted; subprocess schemas decode once through their typed owners |

Actual guard commands, with `PYTHONPATH` pointing to this worktree:

```sh
/home/ts/code/projects/openhcs/.venv/bin/python \
  -m scripts.audit_cellprofiler_headless_ownership --revision cfda8f330
# finding_count: 13; exit 1 (expected: witnessed debt)
/home/ts/code/projects/openhcs/.venv/bin/python \
  -m scripts.audit_cellprofiler_headless_ownership
# finding_count: 0; exit 0
```

The guard inspects the real source for command-discriminator comparisons,
literal parser choice rosters, central stage package sets/comparisons, and JSON
decoding outside the schema boundary. A regression proves each guard fires on
the replaced pattern forms. Zero means these focused structural witnesses are
absent, not that the full codebase is globally clean.

## Authorities and migration closure

`Command` is the ABC contract. Its concrete dataclass declarations own behavior,
parameters and derived CLI names. Stdlib subclass discovery projects that one
family into argparse subparsers; the selected constructor is attached directly
by its declaration. `main` only parses, constructs and executes. There is no
handler map, string ladder, manual command roster, alternate dispatcher, or
third-party registration package that would break Python 3.9 isolation.

Genuine shared capabilities use cooperative MRO:

- `OracleCapability` composes Python/JDK options and preflight for preflight,
  plan, create and verify.
- `VenvCapability` owns the target and exact command trajectory shared by plan
  and create, replacing duplicated construction-command assembly.
- `EvidenceCapability` owns new-receipt safeguards for create and verify.
- `DriftDiagnosticCapability` belongs to verify and native-probe only. Create
  has neither the field nor parser option; there is no central rejection roster.

`InstallStage` owns pip command construction. `BuildPrerequisitesStage` and
`NativeExtensionsStage` declare their external-distribution selection policies;
`SourceBuildStage` owns non-isolated source build flags. The final
`HeadlessDependenciesStage` consumes unclaimed pins. Their declared order owns
NumPy-before-javabridge sequencing. The planner only traverses ordered owners
and removes consumed pins; it does not rediscover package semantics. Constraints
still own versions, and installed CP metadata still owns active dependencies.

`PythonIdentity` replaces the embedded `python -c` positional record and
consumer-side unpack. Its real command runs this same standalone source in the
native interpreter. `NativeProbeReceipt` owns framed stdout decoding and complete
lifecycle admission. Their existing dataclass fields drive strict decoding via
`TypedJsonRecord`; nested `DependencyDiagnostic` records remain typed. Missing,
unknown, wrong-type and int-as-bool inputs fail at that boundary. Consumers use
attributes, never re-read subprocess record keys. No legacy `_probe` reader or
positional identity format remains; producer and consumer changed together.

Create's refusal to mutate existing/symlink environments or receipt evidence,
full-JDK/header checks, disk/RAM gates, explicit no-wx/no-resolver install,
non-isolated pinned-NumPy build, failed-build receipt and strict final validation
remain in the owning mechanisms.

## New-case extension evidence

The tests execute, rather than merely describe, extension experiments:

- `test_new_command_is_discovered_parsed_and_executed_from_one_declaration`
  adds one command subclass. Parser membership, constructor lookup and behavior
  work without editing `main` or a roster. Before, a new operation required at
  least a choices edit plus a dispatcher arm; after, one declaration.
- `test_new_stage_is_selected_from_its_declaration_without_a_classifier_edit`
  adds one stage with order/selection policy. It owns the new pin exactly once
  and appears before native extensions without editing the planner. Before,
  stage membership and assembly were centralized; after, one declaration.
- `test_new_record_field_uses_the_existing_schema_decoder_without_reader_edit`
  adds one receipt field. The existing codec decodes it and native lifecycle
  admission still works without a hand-mapped reader change.

49 focused provider-free tests passed (0.30 s; two unrelated async-plugin config
warnings). Tests also exercise wrong nested/leaf types and false boolean
coercion, diagnostic-option absence on create/plan/preflight, creation/failure
evidence, and resource/data-preservation safeguards. Python 3.9 AST parsing and
actual Python 3.9 `python-identity`/strict `native-probe` entrypoints passed.

## Remaining acceptance

Earlier source-hashed receipts prove real Java/Pipeline/shutdown in the existing
oracle, with setuptools 69.5.1 drift. They do not certify the nominal-command
revision. Its next full native lifecycle check waits for the coordinator's explicit
slot handoff; Confucius owns the current heavy validation slot and the installed
package/skill is frozen. Fresh creation is owner-authorized within the 4 GiB owned-output
budget; it does not require another approval request. #138 stays
open; no merge/install/current-version live-readiness claim is made.

## MI identity correction from independent review

Review: https://github.com/OpenHCSDev/openhcs/pull/207#issuecomment-5897134579.
Reviewed head: `038b5a3ece46ec6898e988be382db4aa0f026258`. Current main
`283b21275553c54261cf9aeedb7374c113d07f2b` was fetched and merged normally as
`3d387981b86d0bd011b220ed185fe292bbb129c6` before this correction.

The earlier focused AST guard was not sufficient to prove declaration identity:
it reports zero for the reviewed head even though the real diamond extension
fails. This is a MEMB-1 membership projection defect, with IDEN-6's wrong-identity
concern: inheritance paths were treated as members rather than class declarations.
Both `Command.parser()` and `install_stages()` consumed that same projection.

The actual script reproduced two occurrences of a concrete command inherited
through two abstract roles. Parser creation raised `conflicting subparser:
combined`. The equivalent stage was constructed twice, with pin counts `[1, 0]`.
Both new diamond regression tests failed before the traversal correction
(2 failed, 51 deselected, 0.25 s).

`concrete_descendants()` now owns a traversal-local visited-class set and an
explicit depth-first stack. Reversing subclass insertion when pushing retains
the previous first-encounter declaration order. Every class, including abstract
parents, is visited once; only concrete declarations are yielded. The set is
discarded after traversal, not a registration store or a hand-maintained family
roster. No MI restriction, caller-side deduplication, command/stage dispatcher,
or parallel traversal remains. The old recursive path enumeration is deleted
in place. Command behavior/options and stage selection/order/build policy remain
on their existing owners.

Executed new-case evidence:

- `test_diamond_command_is_registered_once_in_declaration_order` composes two
  abstract command roles in one concrete dataclass declaration, then exercises
  the real parser, constructor lookup and `main` behavior. An additional sibling
  confirms first-encounter order and repeated discovery is stable. Abstract
  roles do not become commands.
- `test_diamond_stage_is_constructed_once_in_declaration_order` composes two
  abstract stage parents and verifies exactly one constructed stage with its
  owned pin. An equal-priority sibling exercises deterministic stable sorting;
  every real constraint pin plus both extension pins is consumed exactly once.
- Both extensions require only their declarations, with no parser, planner or
  roster edit. Stage policy is not moved into a central classifier.

The first full-suite rerun exposed a test-fixture omission: the new executable
command was not decorated as a dataclass, unlike the production command leaves.
The fixture was corrected, not supported by a production fallback. The final
focused suite passed **53 tests in 0.36 s**, with the same two unrelated disabled
async-plugin configuration warnings. The prescribed project Python imported both
bootstrap and audit modules from this isolated worktree; no OpenHCS import was
needed. `PYTHONPATH` included this tree and all eight recorded external source
directories, and `--confcutdir=tests/unit` avoided global runtime fixtures.

The current focused source/AST guard still reports zero; its historical
`cfda8f330` run reports 13 actual replaced witnesses (expected exit 1). The
diamond behavioral checks cover the identity defect that this structural guard
does not detect. Both changed Python files parse with Python 3.9 AST rules.
Actual Python 3.9.25 ran `python-identity`, MI parser/main dispatch and MI stage
construction successfully with `-I -B`, without OpenHCS, CellProfiler or
javabridge imports. These checks do not start Java or certify native acceptance.
No environment creation, package installation, native build, MCP, GUI, JVM,
installed source or managed skill change occurred.
