"""Source-only startup feedback selection; dependencies remain read-only."""

import sys

sys.path[:0] = [
    "/home/ts/wt/openhcs-gui-cold-connect-355-20261001",
    "/home/ts/wt/zmqruntime-cold-start-355-20261001/src",
]

import openhcs.core

openhcs.core.__path__.append(
    "/home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/lib/python3.12/site-packages/openhcs/core"
)

import pytest
import zmqruntime.client

print("Python:", sys.executable, sys.version, flush=True)
print("OpenHCS:", openhcs.__file__, flush=True)
print("ZMQRuntime:", zmqruntime.client.__file__, flush=True)
raise SystemExit(pytest.main([
    "--noconftest", "-o", "addopts=", "-p", "no:cacheprovider",
    "--basetemp=/home/ts/.cache/agent-scratch/startup-feedback-358-20261001/pytest",
    *sys.argv[1:],
]))
