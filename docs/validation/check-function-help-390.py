"""Provider/plugin-free source check using read-only existing ABI dependencies."""

import importlib.util
import sys
from pathlib import Path

import openhcs

installed_package = Path(sys.argv[1])
for module_name, relative in (
    ("openhcs.core._tabular_native", "core/_tabular_native.abi3.so"),
    (
        "openhcs.processing.backends.cellprofiler._granularity_native",
        "processing/backends/cellprofiler/_granularity_native.abi3.so",
    ),
):
    spec = importlib.util.spec_from_file_location(module_name, installed_package / relative)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)

import pytest

raise SystemExit(pytest.main(sys.argv[2:]))
