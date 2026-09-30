#!/bin/sh
set -eu
task_root=/home/ts/wt/openhcs-bootstrap-integration-20260930
dependency_root=/home/ts/wt/openhcs-context-bounding-20260929/external
receipt_root="$task_root/docs/validation/runtime_bootstrap_20260930/parent-main-integration"
export PYTHONPATH="$task_root:$dependency_root/ObjectState/src:$dependency_root/PolyStore/src:$dependency_root/arraybridge/src:$dependency_root/metaclass-registry/src:$dependency_root/pycodify/src:$dependency_root/pyqt-reactive/src:$dependency_root/python-introspect/src:$dependency_root/zmqruntime/src"
export PYTHONDONTWRITEBYTECODE=1 PYTEST_DISABLE_PLUGIN_AUTOLOAD=1
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1
export OPENHCS_CPU_ONLY=true QT_QPA_PLATFORM=offscreen
export XDG_CACHE_HOME="$receipt_root/test-scratch/cache"
export XDG_DATA_HOME="$receipt_root/test-scratch/data"
cd "$task_root"
exec /usr/bin/time -f 'elapsed=%e max_rss_kib=%M exit=%x' timeout 30s \
  /home/ts/code/projects/openhcs/.venv/bin/python -B -c '
import importlib.util
from pathlib import Path
import pytest
from polystore.imagej_distribution import FijiArchiveDistribution, ImageJArchiveDownloadPolicy
FijiArchiveDistribution.configure_process_environment(default_download_policy=ImageJArchiveDownloadPolicy(allow_download=False))
expected = {
    "openhcs": Path("/home/ts/wt/openhcs-bootstrap-integration-20260930/openhcs"),
    "objectstate": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/ObjectState/src/objectstate"),
    "polystore": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/PolyStore/src/polystore"),
    "arraybridge": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/arraybridge/src/arraybridge"),
    "metaclass_registry": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/metaclass-registry/src/metaclass_registry"),
    "pycodify": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/pycodify/src/pycodify"),
    "pyqt_reactive": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/pyqt-reactive/src/pyqt_reactive"),
    "python_introspect": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/python-introspect/src/python_introspect"),
    "zmqruntime": Path("/home/ts/wt/openhcs-context-bounding-20260929/external/zmqruntime/src/zmqruntime"),
}
for name, root in expected.items():
    actual = Path(importlib.util.find_spec(name).origin).resolve()
    assert actual.is_relative_to(root), (name, actual, root)
    print(f"source {name}: {actual}", flush=True)
raise SystemExit(pytest.main([
    "--noconftest", "-o", "addopts=", "-q",
    "--basetemp=docs/validation/runtime_bootstrap_20260930/parent-main-integration/test-scratch/pytest-native-built",
    "--junitxml=docs/validation/runtime_bootstrap_20260930/parent-main-integration/source-tests-native-built.xml",
    "tests/unit/agent/test_owned_runtime_bootstrap.py",
    "tests/unit/test_zmq_execution_server_process.py",
    "tests/unit/agent/test_agent_services.py::test_execution_connection_spec_owns_zmq_endpoint_projection",
    "/home/ts/wt/openhcs-context-bounding-20260929/external/zmqruntime/tests/test_owned_startup.py",
    "/home/ts/wt/openhcs-context-bounding-20260929/external/zmqruntime/tests/test_owned_close.py",
    "/home/ts/wt/openhcs-context-bounding-20260929/external/zmqruntime/tests/test_endpoint_ownership.py",
    "/home/ts/wt/openhcs-context-bounding-20260929/external/zmqruntime/tests/test_startup.py",
    "/home/ts/wt/openhcs-context-bounding-20260929/external/zmqruntime/tests/test_viewer_state.py",
]))
'
