"""Run the original R0 directly from retained Git objects, without a checkout.

No detector is copied or altered. Git declares available modules at the CI pin;
Python's original importer contracts load their immutable source on demand.
"""

from __future__ import annotations

import importlib.abc
import importlib.util
from pathlib import Path
import subprocess
import sys


REPO = Path("/home/ts/.agent-comms")
REVISION = "3b03785f45df2ef5dc62ba6aed99294192ecbb01"
BACKING = Path("/home/ts/wt/basicpy-live-candidate-20260930/.venv/lib/python3.12/site-packages")


class GitSourceLoader(importlib.abc.SourceLoader):
    """Read one original module from its exact Git blob, never a replacement."""

    def __init__(self, relative: str):
        self.relative = relative

    def get_filename(self, fullname):
        return f"{REPO}@{REVISION}/{self.relative}"

    def get_data(self, path):
        return subprocess.check_output(("git", "-C", str(REPO), "show", f"{REVISION}:{self.relative}"))


class GitRevisionFinder(importlib.abc.MetaPathFinder):
    """Resolve original package membership solely from the pinned Git tree."""

    def __init__(self):
        self.paths = frozenset(subprocess.check_output((
            "git", "-C", str(REPO), "ls-tree", "-r", "--name-only", REVISION,
            "--", "src/agent_comms",
        ), text=True).splitlines())

    def find_spec(self, fullname, path=None, target=None):
        if fullname.partition(".")[0] != "agent_comms":
            return None
        relative = "src/" + fullname.replace(".", "/")
        for candidate, package in ((relative + "/__init__.py", True), (relative + ".py", False)):
            if candidate in self.paths:
                return importlib.util.spec_from_loader(fullname, GitSourceLoader(candidate), is_package=package)
        raise ModuleNotFoundError(f"Module absent from original pinned Git tree: {fullname}")


sys.path.insert(0, str(BACKING))
sys.meta_path.insert(0, GitRevisionFinder())
from agent_comms.debt_ratchet import main

print(f"Original R0 source: {REPO}@{REVISION}; dependency backing: {BACKING}", flush=True)
raise SystemExit(main())
