"""Select original/proposed PR394 source owners, not a second implementation.

QA134_SOURCE_ROOT points to a small, explicitly retained source projection.
The existing runner owns ABI preparation and pytest. No product method or
assertion is replaced; normal imports select these files before collection.
"""

import importlib.abc
import importlib.util
import os
from pathlib import Path
import runpy
import sys


source_root = Path(os.environ["QA134_SOURCE_ROOT"]).resolve(strict=True)
sources = {
    ".".join(path.relative_to(source_root).with_suffix("").parts): path
    for path in source_root.rglob("*.py")
}


class SelectedOwnerSources(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        source = sources.get(fullname)
        if source is None:
            return None
        print(f"SOURCE PROJECTION ONLY: {fullname} -> {source}")
        return importlib.util.spec_from_file_location(fullname, source)


if any(name in sys.modules for name in sources):
    raise RuntimeError("A selected owner was imported before source selection")
selection = SelectedOwnerSources()
sys.meta_path.insert(0, selection)
try:
    runpy.run_path(
        str(Path(__file__).with_name("check-function-help-390.py")), run_name="__main__"
    )
finally:
    sys.meta_path.remove(selection)
