# B6: main's CI green

**Head audited:** `openhcs` `main` at `84e7a2904` (#1193). **Rules:** [00-RULES.md](00-RULES.md). **Input:** the last completed runs on main: Integration Tests 38116770859 (`b468e7359`, W), Website 38110269836, Documentation 38116770933.

## What is wrong

**Three workflows are red on main, and Documentation has not passed on main in the last 1,000 runs. Most jobs fail for a handful of shared causes that only CI exposes (wheel install, `--import-mode=importlib`, Windows, path filters), so local runs never see them.**

Causes measured on the W run, before B5 merged (to be re-measured on this PR's CI):

- **Website:** the job installs a hand-written roster of five first-party packages instead of OpenHCS, then imports `openhcs.authoring.session.operations`, whose graph needs `numba` (and the rest of OpenHCS's dependencies). The `paths:` filter lists `openhcs/__init__.py` only, so refactors that broke the import never triggered it.
- **unit-tests:** collection stops at 17 errors. 14 test modules import a sibling test module by bare name (`from test_function_outputs import …`); CI runs `--import-mode=importlib` from the installed wheel, where the test directory is not on `sys.path`. The rest were fixed by B5.
- **Documentation:** `scripts/validate_docs.py docs/source` reports 950 findings: 828 "authority changed after review", 78 "authority file does not exist", 34 "source changed after its editorial audit" over 140 pages in `docs/audits/*.json`, and 10 missing `openhcs/skills/use-openhcs/references/*.md` paths in the MCP knowledge-base manifest.
- **Integration (other jobs):** listed per job under Remaining, with owner, as measured on this PR.

## Target

- Each workflow installs what it imports through the one candidate installer (`scripts/install_ci_candidate.py`), never a roster.
- Test helpers are imported through the `tests` package.
- Root causes fixed in production, packaging or workflows; no skip, xfail, `continue-on-error` or loosened check.

## Guards

- `tests/unit/test_ci_import_guards.py`: no test module imports a test-tree module by bare name.
- `tests/unit/test_ci_package_boundaries.py`: the website installs the OpenHCS candidate through `install_ci_candidate`.
- `tests/unit/test_build_website.py`: the website workflow triggers on `openhcs/**`.

## Done when

Website, Documentation and Integration Tests are green on this PR's head, or each remaining red job names its exact cause and owning surface below.

## Remaining

(filled from this PR's CI)
