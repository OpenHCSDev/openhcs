# B6b: CI triggers, local smoke, and B6's remaining fixes

## B6b handoff

All work is on branch `refactor/B6b-ci-green` (merged with main `77bf7e803`; last commit is this WIP). Job 1 merged as #1212. Scratch: `scratch/b6-merged` (local only) is B6's head with formatting-only edits undone by `.claude/dechurn.py` in the agent worktree.

**Job 2, smoke script: done, not yet in a PR.**
- `/home/ts/code/projects/openhcs/.claude/verify/smoke_local.sh <worktree>` is installed. It runs `tests/smoke_tests.txt` (in this branch; a built-in list on older branches) with 2 workers, then `scripts/smoke_installed_gui.py` from source, offscreen.
- Observed: main `a751b0eba` `smoke rc=1` (5 failed, GUI catalog timeout, 651 s); this branch `smoke rc=0` (7 passed, GUI passed, 187 s).
- After #1212 alone the GUI part still fails; it needs this branch's catalog wait (`03ca14cc9`) and `accepted_ui_action_status` (the smoke result held the status class, not JSON). Until this merges use `SMOKE_SKIP_GUI=1`.
- Verify: `bash /home/ts/code/projects/openhcs/.claude/verify/smoke_local.sh <worktree>`.

**Job 3, CI triggers: not started (design only).**
- Plan: new `pr-checks.yml` (pull_request): guards plus changed test files plus `tests/core`, and `tests/smoke_tests.txt`. `integration-tests.yml` and `docs.yml` go to `workflow_dispatch`, nightly `schedule`, tags `v*`; delete the per-job `if: github.event_name == ...` lines (they are false on `schedule`).
- Release gate: `scripts/release_readiness.py` `ReleaseWorkflowGate.successful_run` filters `--event push`; drop that filter so a dispatch or nightly run on the exact commit counts.
- nra-r1: still `--budget-seconds 160`, job `timeout-minutes: 10`. Local gate uses 600. Not changed yet.
- Doc audits: `scripts/validate_docs.py` pins each authority by sha256 of the whole file, so any edit to a hub file (`compiler.py` is cited by 24 pages) invalidates every citing page. Measured, B6's pins against main: 98 stale pages by bytes, 98 by AST-normalized digest, 86 if scoped to symbols the page names. Formatting is not the cause; scoping needs a reviewer-declared `symbols` list per authority.
- Unowned: the `code-quality` job runs `black --check` on every file changed since its last green run; it will fail the full matrix.
- B6's workflow commits belong here: `542f7ffeb`, `ce529e459`, `5544c445f`, `e82ae3398`, `6bccc4d6d` (website part).

**Job 4, B6's remaining fixes: WIP, not a PR.**
- Done: all B6 functional commits carried, plus two new fixes (stop during compile ends `cancelled`; smoke status name). `266 passed` on the touched unit files; smoke rc=0.
- Dropped: black commits (`cf0b8eb8c`, `f2ae23c97`, `2ed28bb32`, `ae618be9d`, `7f5710ae9`, `3e089a3f2`), ratchet mixin moves (`239953c4c`, `ab03ba7ba`, `24bfafede`; the registry keeps B6's module functions), all `docs/source`, `docs/audits`, `README.md` and `validate_docs.py` changes (re-review and re-pin commits), workflows (job 3), the pyqt-reactive pin (PyQT-reactive#21 still open), `f8062d2cd`.
- Next: run `guardrails_local.sh` (the ratchet may object to classes grown without the mixins), parity under flock (execution code changed), check 3.11 syntax of touched files, replace B6's receipt text, open the PR, close #1195 with a comment.
- Verify: `bash /home/ts/code/projects/openhcs/.claude/verify/guardrails_local.sh <worktree>` and the smoke command above.
