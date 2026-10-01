"""Baseline behavioral comparison; restore only the original projection module in memory."""

import importlib.util
import os
from pathlib import Path
import runpy
import subprocess
import sys

root = Path(os.environ["OPENHCS_SOURCE_TEST_ROOT"])
revision = sys.argv.pop(1)
module_name = "openhcs.core.projected_image_output"
filename = root / "openhcs/core/projected_image_output.py"
source = subprocess.run(
    ["git", "-C", str(root), "show", f"{revision}:openhcs/core/projected_image_output.py"],
    check=True, capture_output=True,
).stdout
spec = importlib.util.spec_from_file_location(module_name, filename)
module = importlib.util.module_from_spec(spec)
sys.modules[module_name] = module
exec(compile(source, str(filename), "exec"), module.__dict__)
print("Original projection source loaded in memory:", revision, flush=True)
runpy.run_path(
    str(root / "docs/validation/compiled_metadata_artifact_binding_368_20261001/source_shard.py"),
    run_name="__main__",
)
