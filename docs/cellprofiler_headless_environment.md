# Bootstrap the native headless CellProfiler benchmark environment

Use this how-to guide before reproducing [Official30](../benchmark/manifests/README.md)
or the [matched-batch experiments](../benchmark/results/matched_batch_pilot_v2_20260923/README.md).
It creates the native oracle only, not the OpenHCS environment or a CellProfiler GUI.

## Check prerequisites without installing anything

Provide an existing **Linux x86_64 CPython 3.9.25** interpreter and a full **JDK 11**.
Temurin JDK 11 is the issue #138 reference; the preflight accepts JDK 11 vendors
and records the selected executable and actual JVM vendor/version. A JRE alone
is insufficient. Obtain Python/JDK through your approved host provisioning path;
this script never downloads them. Native builds also need a C compiler, Python
headers, and MySQL/MariaDB development files providing `mysql_config`.

From the repository root, substitute your interpreter and JDK paths:

```sh
export JAVA_HOME=/path/to/jdk-11
python scripts/bootstrap_cellprofiler_headless.py preflight \
  --python /path/to/python3.9
python scripts/bootstrap_cellprofiler_headless.py plan \
  --python /path/to/python3.9 \
  --venv "$PWD/.venv-cellprofiler39"
```

Both commands are read-only. `plan` prints the exact commands without running
pip, creating a virtual environment, or starting CellProfiler's JVM.

## Create and validate a fresh oracle

Reserve disk and RAM first. The script requires at least 4 GiB free disk and
8 GiB available RAM before creation; allow additional space for pip's existing
cache and build scratch. In a shared agent batch, obtain coordinator approval
for the environment/download budget, run the resource guard, and acquire the
batch's nonblocking validation lock around the entire create/verify command.
Do not run it against a shared or installed environment.

```sh
python scripts/bootstrap_cellprofiler_headless.py create \
  --python /path/to/python3.9 \
  --venv "$PWD/.venv-cellprofiler39" \
  --receipt "$PWD/cellprofiler-headless-environment.json"
```

The environment and receipt paths must be new, with existing parent directories.
An existing environment is refused, never upgraded or repaired in place. A failed
build is retained with a failure receipt rather than erased or silently retried.

For an owned disposable acceptance environment, add `--cache-dir /owned/run/pip-cache`
to `plan` and `create`; keep build scratch (`TMPDIR`) in the same owned run.
Pip uses isolated configuration, disables global/site config files and user
installation, and selects the public PyPI index. Inherited target/prefix/user
settings cannot redirect writes into a shared installation.

The pinned [constraints](../scripts/cellprofiler-headless-constraints.txt) own the
installation versions. Pip installs the explicit closure with `--no-deps`, so
CellProfiler cannot pull wxPython. NumPy 1.24.4, setuptools 80.9.0, and build tools
are installed first. `python-javabridge` and `mysqlclient` are then built from
source with `--no-build-isolation`. The remaining packages must have wheels;
there is no surprise GTK/wx or scientific-library source-build path.

The acceptance probe runs in the native interpreter, with OpenHCS's `PYTHONPATH`
removed. It validates pins and active dependency requirements from installed
distribution metadata. Only CellProfiler's missing wxPython requirement is
permitted. It sets CP/AWT headless preferences and executes the real
`start_java()` → `Pipeline()` → `stop_java()` lifecycle in a bounded subprocess.
Successful strict validation records `status: "verified"`.

## Inspect an existing oracle without changing it

```sh
python scripts/bootstrap_cellprofiler_headless.py verify \
  --python "$PWD/.venv-cellprofiler39/bin/python" \
  --receipt "$PWD/cellprofiler-headless-verification.json"
```

Strict verification fails before JVM startup if the environment differs from the
constraints. For a historical oracle, add `--allow-version-drift` to inspect its
real Java lifecycle while recording every differing package. This diagnostic
mode cannot be used with `create` and records `verified_with_version_drift`,
**not** acceptance of the pinned target. Missing/incompatible non-GUI
dependencies still fail. `pip check` will report missing wxPython in this
deliberately headless installation; do not solve that by installing wx.

The JSON receipt contains interpreter/JDK identities, constraints and bootstrap
SHA-256s, construction commands when created here, observed package versions,
dependency diagnostics, imported source paths, actual JVM vendor/version, and
startup/Pipeline/shutdown outcomes. Keep it beside new benchmark evidence. A
verify-only receipt has `construction: null` and does not prove how the inspected
environment was built. This environment check does not establish dataset parity
or benchmark timing validity.

## Use the validated oracle

Keep `JAVA_HOME` exported for benchmark subprocesses. For Official30, set:

```sh
export CELLPROFILER_EXECUTABLE="$PWD/.venv-cellprofiler39/bin/cellprofiler"
```

For the existing matched-batch driver, pass
`--native-python "$PWD/.venv-cellprofiler39/bin/python"` to
`python -m benchmark.matched_cellprofiler_batch` in the separate OpenHCS
environment. Use the experiment's documented manifest, well selection and output
arguments. Do not run the OpenHCS package under Python 3.9.
