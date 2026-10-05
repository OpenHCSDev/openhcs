"""Source test admission and optional exact original renderer negative control."""

import importlib
from pathlib import Path
import subprocess
import sys

# Running this script names validation/ as sys.path[0]; source_root in the
# recorded PYTHONPATH admits the isolated checkout, never an installed target.
import openhcs
import metaclass_registry
import python_introspect
import pyqt_reactive
import pytest

print("ORIGINS", openhcs.__file__, metaclass_registry.__file__,
      python_introspect.__file__, pyqt_reactive.__file__, flush=True)
assert Path(openhcs.__file__).resolve().parent.parent == Path.cwd()
arguments = sys.argv[2:]
if arguments[:1] == ["--original-renderers"]:
    arguments.pop(0)
    for name in ("plate", "viewer"):
        module = importlib.import_module("openhcs.mcp.dev_client_renderers." + name)
        path = "openhcs/mcp/dev_client_renderers/" + name + ".py"
        original = subprocess.check_output(("git", "show", "5b2e43b36b7e2d129e191e86e763e914e7142e9a:" + path))
        print("ORIGINAL NEGATIVE CONTROL", path, flush=True)
        exec(compile(original, path + "@5b2e43", "exec"), module.__dict__)
raise SystemExit(pytest.main(["--noconftest", "-o", "addopts=", *arguments]))
