#!/bin/sh
set -eu
cd /home/ts/wt/openhcs-ack-runtime-parent-20260930
mkdir -p /home/ts/.cache/agent-scratch/ar30
exec sh docs/validation/ack_runtime_parent_20260930/run-candidate.sh -c '
import os
from pathlib import Path
os.sched_setaffinity(0, set(sorted(os.sched_getaffinity(0))[:3]))
import openhcs, zmqruntime, polystore, metaclass_registry
for module, directory in (
    (openhcs, "/home/ts/wt/openhcs-ack-runtime-parent-20260930/openhcs"),
    (zmqruntime, "/home/ts/wt/openhcs-ack-runtime-parent-20260930/external/zmqruntime/src/zmqruntime"),
    (polystore, "/home/ts/wt/openhcs-ack-runtime-parent-20260930/external/PolyStore/src/polystore"),
    (metaclass_registry, "/home/ts/wt/openhcs-ack-runtime-parent-20260930/external/metaclass-registry/src/metaclass_registry"),
):
    assert Path(module.__file__).resolve().is_relative_to(Path(directory)), (module.__file__, directory)
    print("SOURCE", module.__file__, flush=True)
import pytest
raise SystemExit(pytest.main([
    "--noconftest", "-p", "no:cacheprovider", "-o", "addopts=", "-q",
    "tests/unit/test_ack_return_route_journey.py",
    "tests/unit/agent/test_owned_runtime_bootstrap.py",
    "tests/unit/agent/test_owned_bootstrap_readback.py",
    "tests/unit/test_napari_transport_ownership.py",
    "tests/unit/test_fiji_viewer_server.py",
    "--basetemp=/home/ts/.cache/agent-scratch/ar30/p",
    "--junitxml=/home/ts/wt/openhcs-issue-batch-20260929/ack-runtime-parent-20260930/paired-source-final.xml",
]))
'
