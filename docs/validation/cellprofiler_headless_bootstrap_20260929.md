# Headless CellProfiler bootstrap checkpoint

Issue: #138. Draft implementation: https://github.com/OpenHCSDev/openhcs/pull/207.
Worker: `openhcs-headless-bootstrap-worker`. Source worktree:
`/home/ts/wt/openhcs-headless-bootstrap-20260929`.

## Verified scope

The standalone script's existing-oracle entrypoint executed the real
`start_java()` → `Pipeline()` → `stop_java()` lifecycle under the batch's
nonblocking validation lock. The recorded native import paths are inside
`/home/ts/code/projects/openhcs/.venv-cellprofiler39`. That environment was not
installed into or upgraded. Headless preferences and the standard CP Java owner
were used, with no GUI or benchmark dataset opened.

The [first checkpoint receipt](cellprofiler_headless_existing_environment_20260929.json)
contains exact source/constraints SHA-256s and observed package/JVM identities.
It records CP/core 4.2.8.1, Python 3.9.25, NumPy 1.24.4, SciPy 1.9.0, JDK
11.0.32.1 (Arch vendor), and setuptools 69.5.1. Only setuptools differs from the
constraints; no non-GUI dependency errors. This is
`verified_with_version_drift`, not pinned-target acceptance.

The follow-up source checkpoint makes native lifecycle admission an owned
`NativeProbeReceipt` method, rejects incomplete/malformed native proofs, and
disables native bytecode writes with `-B`. Focused provider-free tests additionally
cover exact creation command order, recorded build failure, refusal to mutate
existing environments/evidence, and insufficient disk/RAM. These mocked install
tests do not prove a fresh build.

The later nominal-command/stage correction is documented in the
[focused ownership receipt](cellprofiler_headless_ownership_20260929.md).
Its actual AST checks found 13 witnesses at published `cfda8f330` and zero in the
replacement, and 49 provider-free regressions passed in 0.30 s. The current
Python 3.9 entrypoint successfully executed declaration-owned `python-identity`
and the strict `native-probe` early-rejection path. Because setuptools differs,
that strict probe correctly returned failure before Java startup.

The full Java lifecycle receipts above belong to the earlier source hashes,
not the nominal-command replacement. Further JVM verification is deferred while
Euler owns H003/shared validation priority. No new JVM/GUI/heavy test was started
after the resource checkpoint. There is no current-version live readiness claim.

The live host reported 12.5–12.9 GiB available RAM at the validation guards.
Resource checks warned about already-used swap; headroom checks passed. The
worker did not start a GUI, create a new environment, download a JDK/interpreter,
access blind data, modify an installed package, or alter production files.

## Reproduce validation

Use `/home/ts/code/projects/openhcs/.venv/bin/python` as the orchestrator. Set
`PYTHONPATH` to the worktree and required recorded `external/*/src` directories;
verify `openhcs`, `benchmark`, `objectstate`, `polystore`, `metaclass_registry`,
and `zmqruntime` imports point there first. The worker verified those paths.

```sh
mkdir -p .pytest_cache
/home/ts/bin/agent-resource-check --assert-headroom
flock -n /home/ts/wt/openhcs-issue-batch-20260929/validation.lock \
  env OPENHCS_CPU_ONLY=true PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 \
  /home/ts/code/projects/openhcs/.venv/bin/python -m pytest \
  --confcutdir=tests/unit tests/unit/test_cellprofiler_headless_bootstrap.py \
  -q --basetemp="$PWD/.pytest_cache/headless-bootstrap-tests"

flock -n /home/ts/wt/openhcs-issue-batch-20260929/validation.lock \
  /home/ts/code/projects/openhcs/.venv/bin/python \
  scripts/bootstrap_cellprofiler_headless.py verify \
  --python /home/ts/code/projects/openhcs/.venv-cellprofiler39/bin/python \
  --java-home /usr/lib/jvm/java-11-openjdk --allow-version-drift \
  --receipt "$PWD/new-existing-oracle-receipt.json"
```

The focused pytest invocation deliberately omits global OpenHCS runtime fixtures
and plugin autoload because these standalone packaging-boundary tests need no
runtime, display, or provider. The repo's two async configuration warnings under
that invocation are unrelated to the tested script. No global NRA scan was run;
ownership/source inspection and Python 3.9 AST validation were focused on the
changed tooling.

## Artifact availability, not installability proof

A read-only check of [PyPI release metadata](https://pypi.org/simple/) for all 58
constraints found non-yanked matching Python 3.9/Linux wheel artifacts for the
wheel stages and source archives for the two declared native builds
(`mysqlclient`, `python-javabridge`). It matched wheel tags against the existing
native interpreter and checked `Requires-Python`. No distribution bytes were
downloaded or installed. This check does not establish that native compilation
or a fresh dependency closure succeeds.

## Outstanding acceptance

Owner approval has now been granted for the bounded fresh environment, after
Euler releases shared validation: no more than 4 GiB owned disposable output,
only the two declared native builds, and no JDK/interpreter download. Earlier
coordinator messages did not grant it; the newer owner instruction does. See the
[authorized run plan](cellprofiler_headless_fresh_acceptance_20260929.md). Leave
#138 open until an approved `create` run emits a strict `verified` receipt with
setuptools 80.9.0. Temurin-specific fresh validation is also not covered by the
Arch-JDK observation. No merge, installation, biological, parity, or performance
readiness claim follows from this checkpoint.
