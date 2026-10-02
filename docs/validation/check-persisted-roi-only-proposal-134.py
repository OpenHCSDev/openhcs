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
import subprocess
import sys

source_root = Path(os.environ["QA134_SOURCE_ROOT"]).resolve(strict=True)
sources = {
    ".".join(path.relative_to(source_root).with_suffix("").parts): path
    for path in source_root.rglob("*.py")
}
repository = Path(__file__).resolve().parents[2]
revision = os.environ.get("QA134_GIT_REF")
git_sources = {}
if revision:
    changed = subprocess.check_output(
        ["git", "diff", "--name-only", "HEAD", revision, "--", "openhcs"],
        cwd=repository,
        text=True,
    ).splitlines()
    git_sources = {
        ".".join(Path(path).with_suffix("").parts).removesuffix(".__init__"): path
        for path in changed
        if path.endswith(".py")
    }


class GitOwnerSource(importlib.abc.Loader):
    """Import exact pinned source blobs without copying an entire checkout."""

    def create_module(self, spec):
        return None

    def exec_module(self, module):
        path = git_sources[module.__name__]
        source = subprocess.check_output(
            ["git", "show", f"{revision}:{path}"],
            cwd=repository,
        )
        print(f"PINNED SOURCE ONLY: {module.__name__} -> {revision}:{path}")
        exec(compile(source, f"{revision}:{path}", "exec"), module.__dict__)


class SelectedOwnerSources(importlib.abc.MetaPathFinder):
    def find_spec(self, fullname, path=None, target=None):
        source = sources.get(fullname)
        if source is not None:
            print(f"SOURCE PROJECTION ONLY: {fullname} -> {source}")
            return importlib.util.spec_from_file_location(fullname, source)
        source_path = git_sources.get(fullname)
        if source_path is not None:
            spec = importlib.util.spec_from_loader(
                fullname,
                GitOwnerSource(),
                is_package=source_path.endswith("/__init__.py"),
            )
            if spec.submodule_search_locations is not None:
                spec.submodule_search_locations = [
                    str(repository / Path(source_path).parent)
                ]
            return spec
        return None


if any(name in sys.modules for name in {*sources, *git_sources}):
    raise RuntimeError("A selected owner was imported before source selection")
selection = SelectedOwnerSources()
sys.meta_path.insert(0, selection)
try:
    runpy.run_path(
        str(Path(__file__).with_name("check-function-help-390.py")), run_name="__main__"
    )
finally:
    sys.meta_path.remove(selection)
