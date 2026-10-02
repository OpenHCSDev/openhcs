"""Bounded source checks using the existing read-only ABI environment."""

import importlib.util
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[2]
sys.path[:0] = [
    str(root),
    "/home/ts/wt/metaclass-registry-selected-discovery-376-20261001/src",
]
installed = Path(
    "/home/ts/wt/openhcs-generated-inputs-installed-parent-20261001/.venv/lib/python3.12/site-packages/openhcs"
)
for name, relative in (
    ("openhcs.core._tabular_native", "core/_tabular_native.abi3.so"),
    ("openhcs.processing.backends.cellprofiler._granularity_native",
     "processing/backends/cellprofiler/_granularity_native.abi3.so"),
):
    spec = importlib.util.spec_from_file_location(name, installed / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)

import pytest
import metaclass_registry

print("Interpreter:", sys.executable, sys.version, flush=True)
print("Discovery owner:", metaclass_registry.__file__, flush=True)
raise SystemExit(pytest.main([
    "--noconftest", "-o", "addopts=", "-p", "no:cacheprovider",
    "--basetemp=/home/ts/.cache/agent-scratch/knowledge-selected-source-376-20261001/pytest",
    *sys.argv[1:],
]))
