"""Source-test entrypoint borrowing only the existing read-only extension ABI."""
import hashlib
import importlib.util
from pathlib import Path
import sys

ROOT = Path('/home/ts/wt/openhcs-compiled-metadata-artifact-binding-20261001')
INSTALLED = Path('/home/ts/wt/openhcs-paired-raw-installed-parent-20261001/.venv/lib/python3.12/site-packages/openhcs')

for module_name, relative in (
    ('openhcs.core._tabular_native', 'core/_tabular_native.abi3.so'),
    ('openhcs.processing.backends.cellprofiler._granularity_native',
     'processing/backends/cellprofiler/_granularity_native.abi3.so'),
):
    binary = INSTALLED / relative
    spec = importlib.util.spec_from_file_location(module_name, binary)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    print('Read-only native ABI:', binary, hashlib.sha256(binary.read_bytes()).hexdigest())

import openhcs.core.function_patterns as patterns
import openhcs.core.pipeline.path_planner as planner
import openhcs.core.steps.function_runtime as runtime

for module in (patterns, planner, runtime):
    path = Path(module.__file__).resolve()
    assert path.is_relative_to(ROOT), path
    print('Source owner:', path)

import pytest

raise SystemExit(pytest.main(sys.argv[1:]))
