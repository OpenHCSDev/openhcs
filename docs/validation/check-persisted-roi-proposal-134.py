"""Select the explicit source proposal before provider/plugin-free collection.

The existing validation runner owns ABI preparation and pytest invocation. This
callback changes only the selected source file, not product classes or test
assertions. The projection is not an installed package or production change.
"""

import importlib.util
from pathlib import Path
import runpy
import sys

import pytest


original_main = pytest.main


def check_proposed_source(args):
    source = (
        Path(__file__).resolve().parents[2]
        / ".qa134-proposal-20261001/source/openhcs/core/steps/function_outputs.py"
    )
    module_name = "openhcs.core.steps.function_outputs"
    if module_name in sys.modules:
        raise RuntimeError("Metadata owner was imported before source selection")
    spec = importlib.util.spec_from_file_location(module_name, source)
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    print(f"SOURCE PROPOSAL ONLY: {module.__file__}")
    pytest.main = original_main
    return original_main(args)


pytest.main = check_proposed_source
try:
    runpy.run_path(
        str(Path(__file__).with_name("check-function-help-390.py")), run_name="__main__"
    )
finally:
    pytest.main = original_main
