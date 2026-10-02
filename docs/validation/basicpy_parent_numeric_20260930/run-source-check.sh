#!/bin/sh
set -eu
export PYTHONPATH=/home/ts/wt/openhcs-basicpy-parent-integration-20260930:/home/ts/wt/basicpy-parent-numeric-20260930/src:/home/ts/wt/openhcs-viewer-live-20260930/external/zmqruntime/src
export PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1 OPENHCS_CPU_ONLY=true
export JAX_PLATFORMS=cpu OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
export NUMBA_NUM_THREADS=1 XLA_FLAGS=--xla_cpu_multi_thread_eigen=false QT_QPA_PLATFORM=offscreen
export POLYSTORE_IMAGEJ_CACHE_ROOT=/home/ts/.cache/polystore/imagej
export POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false
export XDG_CACHE_HOME=/home/ts/.cache/agent-scratch/basicpy-parent-numeric-20260930
export TMPDIR="$XDG_CACHE_HOME"
cd /home/ts/wt/openhcs-basicpy-parent-integration-20260930
exec timeout 60s /usr/bin/time -v /home/ts/code/projects/openhcs/.venv/bin/python -B -c '
import os
from pathlib import Path
os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
import openhcs, arraybridge, basicpy, zmqruntime
for module, directory in (
    (openhcs, "/home/ts/wt/openhcs-basicpy-parent-integration-20260930/openhcs"),
    (arraybridge, "/home/ts/wt/openhcs-basicpy-parent-integration-20260930/external/arraybridge/src/arraybridge"),
    (basicpy, "/home/ts/wt/basicpy-parent-numeric-20260930/src/basicpy"),
    (zmqruntime, "/home/ts/wt/openhcs-viewer-live-20260930/external/zmqruntime/src/zmqruntime"),
):
    assert Path(module.__file__).resolve().is_relative_to(Path(directory))
    print("SOURCE", module.__file__, flush=True)
import pytest
raise SystemExit(pytest.main([
    "--noconftest", "-p", "no:cacheprovider", "-o", "addopts=",
    "tests/unit/test_fitted_illumination_fields.py",
    "tests/integration/test_basicpy_real_fit.py",
    "/home/ts/wt/arraybridge-basicpy-parent-integration-20260930/tests/test_callable_dtype_default.py",
    "-q",
    "--junitxml=/home/ts/wt/openhcs-issue-batch-20260929/basicpy-parent-numeric-20260930/paired-source-native-built.xml",
]))
'
