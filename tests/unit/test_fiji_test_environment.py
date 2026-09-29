"""Protect the real pytest bootstrap against per-fixture Fiji provisioning."""

import os
import subprocess
import sys
from pathlib import Path

import pytest
from polystore.imagej_distribution import (
    FijiArchiveDistribution,
    ImageJArchiveDownloadPolicy,
)

from tests.fiji_test_environment import configure_fiji_test_environment


def test_default_root_is_pinned_before_fixture_cache_isolation(monkeypatch, tmp_path):
    initial = tmp_path / "initial"
    monkeypatch.setenv("XDG_CACHE_HOME", str(initial))
    values = {}
    configure_fiji_test_environment(values)
    root = values[FijiArchiveDistribution.cache_root_environment_key]
    monkeypatch.setenv("XDG_CACHE_HOME", str(tmp_path / "fixture"))
    configure_fiji_test_environment(values)
    assert values[FijiArchiveDistribution.cache_root_environment_key] == root
    assert values[ImageJArchiveDownloadPolicy.allow_download_environment_key] == "false"


def test_explicit_root_and_provisioning_permission_are_authoritative(tmp_path):
    root = tmp_path / "shared"
    values = {
        FijiArchiveDistribution.cache_root_environment_key: str(root),
        ImageJArchiveDownloadPolicy.allow_download_environment_key: "true",
    }
    configure_fiji_test_environment(values)
    assert values[FijiArchiveDistribution.cache_root_environment_key] == str(root)
    assert ImageJArchiveDownloadPolicy.from_environment(values).allow_download


@pytest.mark.parametrize("root", ("", "relative"))
def test_invalid_explicit_root_does_not_fall_back(root):
    with pytest.raises(RuntimeError, match="absolute bundle-cache"):
        configure_fiji_test_environment({
            FijiArchiveDistribution.cache_root_environment_key: root
        })


def test_fresh_collection_configures_runtime_before_import_and_forbids_network(tmp_path):
    # Run the actual conftest, not a stand-in plugin. Each child then isolates
    # XDG and materializes from a tiny local bundle; no real Fiji or JVM needed.
    checkout = Path(__file__).resolve().parents[2]
    cache = tmp_path / "bundles"
    probe = tmp_path / "test_probe.py"
    probe.write_text('''
import runpy
from pathlib import Path
import os
import pytest
from dataclasses import replace

runpy.run_path(os.environ["FIJI_TEST_CONFTEST"])
from polystore.imagej_distribution import (
    FIJI_IMAGEJ_DISTRIBUTION, ImageJArchiveDownloadPolicy,
    ImageJRuntimeArchive, ImageJDistributionUnavailableError,
)
from polystore.imagej_runtime import FIJI_IMAGEJ_RUNTIME

def test_reuse(monkeypatch):
    assert FIJI_IMAGEJ_RUNTIME.distribution is FIJI_IMAGEJ_DISTRIBUTION
    assert not FIJI_IMAGEJ_DISTRIBUTION.download_policy.allow_download
    monkeypatch.setenv("XDG_CACHE_HOME", os.environ["FIJI_TEST_ISOLATED_CACHE"])
    distribution = FIJI_IMAGEJ_DISTRIBUTION
    root = distribution.cache_root
    root.mkdir(parents=True, exist_ok=True)
    # Capture the owner's target path without mirroring its version/digest naming.
    targets = []
    original = type(distribution)._discover_runtime
    def discover(self, target):
        targets.append(target)
        return original(self, target)
    monkeypatch.setattr(type(distribution), "_discover_runtime", discover)
    def no_download(*args, **kwargs):
        pytest.fail("Test bootstrap attempted a Fiji download")
    monkeypatch.setattr(ImageJRuntimeArchive, "download_verified_once", no_download)
    if not tuple(root.glob("fiji-*")):
        with pytest.raises(ImageJDistributionUnavailableError, match="forbidden"):
            distribution.materialize()
        application = targets[0] / "Fiji"
        (application / "jars").mkdir(parents=True)
        (application / "plugins").mkdir()
        java = application / "java/jdk/bin/java"
        java.parent.mkdir(parents=True)
        java.write_bytes(b"fixture - never execute")
    before = tuple(sorted(str(path) for path in root.rglob("*")))
    launch = distribution.materialize()
    assert launch.imagej_directory.is_relative_to(root)
    assert tuple(sorted(str(path) for path in root.rglob("*"))) == before
    assert not Path(os.environ["FIJI_TEST_ISOLATED_CACHE"]).exists()
    missing = replace(distribution, cache_root=root / "missing")
    with pytest.raises(ImageJDistributionUnavailableError, match="forbidden"):
        missing.materialize()
    assert not (root / "missing").exists()
''')
    for run in ("first", "second"):
        environment = dict(os.environ)
        environment.pop(ImageJArchiveDownloadPolicy.allow_download_environment_key, None)
        environment[FijiArchiveDistribution.cache_root_environment_key] = str(cache)
        environment["FIJI_TEST_CONFTEST"] = str(checkout / "tests/conftest.py")
        environment["FIJI_TEST_ISOLATED_CACHE"] = str(tmp_path / run)
        environment["OPENHCS_CPU_ONLY"] = "true"
        environment["PYTEST_DISABLE_PLUGIN_AUTOLOAD"] = "1"
        environment["PYTHONPATH"] = os.pathsep.join((
            str(checkout),
            str(checkout / "external/PolyStore/src"),
        ))
        result = subprocess.run(
            [sys.executable, "-m", "pytest", "-q", "-o", "addopts=", str(probe)],
            env=environment, cwd=tmp_path, text=True, capture_output=True, timeout=15,
        )
        assert result.returncode == 0, result.stdout + result.stderr
    assert len(tuple(cache.glob("fiji-*"))) == 1
