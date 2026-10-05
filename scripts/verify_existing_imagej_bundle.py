"""Read-only native bundle admission proof; does not initialize ImageJ or Java.

Set POLYSTORE_IMAGEJ_CACHE_ROOT to an already materialized cache parent and
POLYSTORE_IMAGEJ_ALLOW_DOWNLOAD=false before starting this fresh process.
"""

import json
import os
from pathlib import Path

import jpype
import polystore.imagej_distribution as distribution_module
from polystore.imagej_runtime import FIJI_IMAGEJ_RUNTIME


def main() -> None:
    distribution = FIJI_IMAGEJ_RUNTIME.distribution
    root = distribution.cache_root
    assert root is not None and root.is_dir(), "An existing bundle cache is required"
    assert not distribution.download_policy.allow_download, "Downloads must be forbidden"
    assert not jpype.isJVMStarted()
    before = tuple(sorted(str(path.relative_to(root)) for path in root.rglob("*")))
    launch = distribution.materialize()
    after = tuple(sorted(str(path.relative_to(root)) for path in root.rglob("*")))
    assert after == before, "Materialization changed the cache inventory"
    assert launch.imagej_directory.is_relative_to(root)
    assert not jpype.isJVMStarted()
    print(json.dumps({
        "source": str(Path(distribution_module.__file__).resolve()),
        "xdg_cache_home": os.environ["XDG_CACHE_HOME"],
        "shared_cache_root": str(root),
        "imagej_directory": str(launch.imagej_directory),
        "java_home": str(launch.java_home),
        "download_allowed": distribution.download_policy.allow_download,
        "new_cache_entries": 0,
        "jvm_started": False,
    }))


if __name__ == "__main__":
    main()
