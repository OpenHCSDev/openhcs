# B6c: CI triggers

Follows job 3 of the B6b handoff (`refactor/B6b-ci-green`, `B6b-ci-and-smoke.md`).
Owner decision 2026-10-12: merges do not wait on the CI matrix; the full matrix
must be green on the release commit before a PyPI upload.

## What is wrong

- `integration-tests.yml` (about 40 jobs) ran on every pull-request push and
  every push to main. Six open PRs queued six matrices and GitHub stopped
  assigning runners for hours.
- Its jobs carried `if: github.event_name == 'push' || ... 'pull_request' || ...
  'workflow_dispatch'`, which is false on `schedule`, so a nightly run would
  have skipped 13 of them.
- `ReleaseWorkflowGate.successful_run` asked only for `--event push` runs, so a
  dispatched or nightly green run on the release commit did not count.
- `nra-r1` ran with `--budget-seconds 160` under a 10-minute job. Measured: 141 s
  for the base scan alone on a hosted runner; the comparison scans base and head.
- `scripts/validate_docs.py` pins every audit authority by the sha256 of the
  whole file. Any edit to a file cited by many pages makes each of them stale.
  At `77bf7e803` the validator reports 866 `authority changed after review`
  findings, so the Documentation workflow is red on main.

## Target

| Workflow | Events |
| --- | --- |
| `pr-checks.yml` (new: `unit-subset`, `smoke`) | `pull_request` to main, `workflow_dispatch` |
| `refactor-guardrails.yml` | `pull_request` to main, `workflow_dispatch` |
| `integration-tests.yml` | `workflow_dispatch`, tags `v*`, nightly 03:23 UTC |
| `docs.yml` | `workflow_dispatch`, tags `v*`, nightly 02:53 UTC |
| `publish.yml` | tags `v*`, `workflow_dispatch` (unchanged) |
| `website-pages.yml` | unchanged (path-filtered) |
| `published-release-canary.yml`, `coverage-pages.yml` | unchanged |

Every workflow has a concurrency group keyed on event and ref.
`publish.yml` queues instead of cancelling, so an upload is never interrupted.

Release gate: the existing query for a green run on the exact SHA, with the
event filter removed. `scripts/release.py` runs the same proof before it
creates the tag, and `publish.yml`'s `verify-release-commit` job repeats it
before any build or upload job starts. A job dependency (`workflow_call` from
`publish.yml`) was not used: it would rerun 40 jobs inside the release run even
when the commit already has a green nightly or dispatched run, and a single
flaky job would force the whole release workflow to restart.

nra-r1: `--budget-seconds 600`, `timeout-minutes: 20`. Two scans at 141 s each
is about 280 s; 600 s is twice that and equals the local gate's value. The
job timeout leaves 10 minutes around the scan, so the scan's own deadline
reports before the job is killed. What is compared is unchanged.

Documentation audits: an authority may now carry `symbols` (dotted names in a
Python file). Its `sha256` then covers only the source text of those
definitions, decorators included, so edits elsewhere in the file and line
shifts keep the pin valid. A renamed or deleted symbol is reported as changed.
`python scripts/validate_docs.py --authority-digest PATH [SYMBOL ...]` prints
the value to pin.

## Not done here

- No existing audit entry was converted. Choosing the symbols a page depends on
  is the review itself; the handoff measured that scoping to the names a page
  mentions would still leave 86 of 98 pages stale after B6, so the entries need
  a reviewer pass, not a mechanical rewrite. Until then whole-file pins behave
  as before.
- Non-Python authorities (workflow YAML, JSON, other pages) are still pinned by
  whole file. A key-path scope for YAML is the next step of the same kind.
- This PR itself makes about 15 more pins stale (workflows,
  `release_readiness.py`, `validate_docs.py`) and edits
  `docs/source/development/mcp_release.rst`. They are left stale for the
  reviewer pass rather than re-pinned without review.
- `parity-scope` in `integration-tests.yml` still has a `pull_request` branch
  that no event reaches now; `tests/unit/test_ci_package_boundaries.py` and
  `.github/tests/test_refactor_guardrails.py` read it. Remove with those tests.
- `code-quality` (`black --check` on files changed since its last green run)
  will fail the first full matrix run; unowned (B6b handoff).
- The GUI step of the `smoke` job fails on main until the B6b job-4 fixes merge
  (catalog wait, action status name).

## Tests

- `tests/unit/test_validate_docs_symbol_pins.py` (new): a symbol pin survives
  edits outside the symbols and goes stale on edits inside them; whole-file
  pins are unchanged; malformed `symbols` is rejected.
- Existing: `tests/unit/test_validate_documentation_audit.py`,
  `test_ci_action_pinning.py`, `test_ci_package_boundaries.py`,
  `test_mcp_release_workflow.py`, `test_release_readiness.py`,
  `.github/tests/test_refactor_guardrails.py`.

## Done when

- All workflow files parse; the tests above pass; `guardrails_local.sh` ends
  `guardrails rc=0`.
- On real runners (not verified here): a pull request starts only PR Checks and
  Refactor Guardrails; a dispatched Integration Tests run starts every job.
