"""Verify original public artifacts without installation or a second publisher."""

import argparse
import hashlib
import json
import subprocess
import sys
import tarfile
from email.parser import BytesParser
from pathlib import Path
from zipfile import ZipFile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("source", type=Path)
parser.add_argument("--scratch", type=Path, required=True)
args = parser.parse_args()
evidence = Path(__file__).resolve().parent
sys.path.insert(0, str(evidence.parents[2]))
from scripts.wait_for_pypi_release import materialize_release_files, wait_for_release

source = args.source.resolve()
expected_commit = "393a7e03003cdc56df9013f932ed4f26e632d77a"
actual_commit = subprocess.check_output(
    ["git", "-C", str(source), "rev-parse", "HEAD"], text=True,
).strip()
assert actual_commit == expected_commit
assert subprocess.check_output(
    ["git", "-C", str(source), "rev-parse", "v0.2.2^{commit}"], text=True,
).strip() == expected_commit
probe = wait_for_release(
    "metaclass-registry", "0.2.2", timeout_seconds=30.0,
    poll_interval_seconds=10.0,
)
assert probe.available, probe.detail
artifacts = evidence / "artifacts"
assert not artifacts.exists(), "retain existing artifacts; never replay materialization"
paths = materialize_release_files("metaclass-registry", "0.2.2", artifacts)
wheels = tuple(path for path in paths if path.name.endswith(".whl"))
sdists = tuple(path for path in paths if path.name.endswith(".tar.gz"))
assert len(wheels) == len(sdists) == 1
assert len(paths) == 2
wheel, sdist = wheels[0], sdists[0]
source_paths = tuple(path for path in subprocess.check_output(
    ["git", "-C", str(source), "ls-tree", "-r", "--name-only", expected_commit,
     "--", "src/metaclass_registry"], text=True,
).splitlines() if path.endswith(".py"))
with ZipFile(wheel) as distribution, tarfile.open(sdist) as source_distribution:
    wheel_sources = {
        name for name in distribution.namelist()
        if name.startswith("metaclass_registry/") and name.endswith(".py")
    }
    assert wheel_sources == {path.removeprefix("src/") for path in source_paths}
    assert not any(name.endswith(".pyc") for name in distribution.namelist())
    metadata_names = tuple(
        name for name in distribution.namelist() if name.endswith(".dist-info/METADATA")
    )
    assert len(metadata_names) == 1
    metadata = BytesParser().parsebytes(distribution.read(metadata_names[0]))
    assert metadata["Name"] == "metaclass-registry"
    assert metadata["Version"] == "0.2.2"
    for path in source_paths:
        blob = subprocess.check_output(
            ["git", "-C", str(source), "show", f"{expected_commit}:{path}"],
        )
        assert distribution.read(path.removeprefix("src/")) == blob, path
        member = source_distribution.extractfile(f"{sdist.name.removesuffix('.tar.gz')}/{path}")
        assert member is not None
        with member:
            assert member.read() == blob, path

# Import directly from the one retained PyPI wheel, not checkout/site-packages.
sys.path.insert(0, str(wheel))
import metaclass_registry
assert metaclass_registry.__file__.startswith(f"{wheel}/")
assert metaclass_registry.__version__ == "0.2.2"
import pytest
result = pytest.main([
    "--noconftest", "-o", "addopts=", "-p", "no:cacheprovider",
    f"--basetemp={args.scratch / 'pytest'}",
    str(source / "tests/test_selected_discovery.py"),
])
assert result == 0, f"published-wheel API controls failed: {result}"
print(json.dumps({
    "source_commit": expected_commit,
    "index": {"available": probe.available, "detail": probe.detail,
              "wheel_url": probe.wheel_url},
    "wheel_import": metaclass_registry.__file__,
    "exact_source_files_checked_in_wheel_and_sdist": len(source_paths),
    "api_controls": "original selected/full discovery and both failure controls passed",
    "artifacts": [{"path": str(path), "size": path.stat().st_size,
                   "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
                  for path in paths],
    "installation": "none; direct retained-wheel import in original read-only interpreter",
}, indent=2), flush=True)
