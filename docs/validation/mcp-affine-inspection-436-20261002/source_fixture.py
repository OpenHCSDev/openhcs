"""Borrow only declared native binaries; all Python owners stay on own source."""

from importlib.metadata import distribution
from importlib.machinery import EXTENSION_SUFFIXES
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import runpy
import sys

source_root = Path(sys.argv[1]).resolve().parents[3]
sys.path.insert(0, str(source_root))

installed = distribution("openhcs")
for entry in installed.files:
    if entry.parts[0] != "openhcs":
        continue
    for suffix in EXTENSION_SUFFIXES:
        if str(entry).endswith(suffix):
            module_name = str(entry)[:-len(suffix)].replace("/", ".")
            spec = spec_from_file_location(module_name, installed.locate_file(entry))
            module = module_from_spec(spec)
            sys.modules[module_name] = module
            spec.loader.exec_module(module)
            break

import openhcs
assert Path(openhcs.__file__).resolve().is_relative_to(source_root)
runpy.run_path(sys.argv[1])["serve_stdio_inspection_fixture"]()
