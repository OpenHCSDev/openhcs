"""Global pytest configuration for OpenHCS integration tests."""

import os
import tempfile
from pathlib import Path

from openhcs._source_dependencies import ensure_source_checkout_external_paths

ensure_source_checkout_external_paths()

import pytest
from zmqruntime.messages import AckReturnRoute, ProcessIdentity

from polystore.imagej_distribution import (
    FijiArchiveDistribution,
    ImageJArchiveDownloadPolicy,
)

# Configure before test collection imports any ImageJ runtime. Tests may change
# XDG_CACHE_HOME later; the immutable bundle must not follow those run caches.
FijiArchiveDistribution.configure_process_environment(
    default_download_policy=ImageJArchiveDownloadPolicy(allow_download=False)
)

def _missing_native_extensions() -> tuple[str, ...]:
    """Native modules declared by their sources (``<module>.cpp``) but not built.

    setup.py derives each extension's source path from its qualified module
    name, so the tracked sources are the declaration; the registry treats an
    unimportable native module as a broken installation.
    """
    import importlib.machinery
    import importlib.util

    import openhcs

    package_root = Path(openhcs.__file__).resolve().parent
    missing = []
    for source in sorted(package_root.rglob("_*_native.cpp")):
        relative = source.relative_to(package_root.parent).with_suffix("")
        module_name = ".".join(relative.parts)
        spec = importlib.util.find_spec(module_name)
        if spec is None or not isinstance(
            spec.loader, importlib.machinery.ExtensionFileLoader
        ):
            missing.append(module_name)
    return tuple(missing)


def pytest_sessionstart(session):
    missing = _missing_native_extensions()
    if missing:
        raise pytest.UsageError(
            "OpenHCS native extensions are not built: "
            + ", ".join(missing)
            + ". Build them in this checkout with "
            "`python setup.py build_ext --inplace`."
        )


# Conditionally import pytest-qt only when not in CPU-only mode
CPU_ONLY_MODE = os.getenv("OPENHCS_CPU_ONLY", "false").lower() == "true"
if not CPU_ONLY_MODE:
    pytest_plugins = ["pytestqt"]
else:
    pytest_plugins = []


@pytest.fixture
def viewer_ack_return_route():
    """Nominal producer route for message construction without a live listener."""
    return AckReturnRoute(
        url="tcp://127.0.0.1:8111",
        incarnation="00000000-0000-0000-0000-000000000001",
        owner=ProcessIdentity.current(),
    )


@pytest.fixture(autouse=True)
def cleanup_test_runtime_resources():
    """Release connection and process resources after every test."""

    from polystore import cleanup_backend_connections
    from zmqruntime import ViewerStateManager

    resolve_viewer_manager = ViewerStateManager.get_instance
    yield

    try:
        resolve_viewer_manager().stop_all_viewers()
    finally:
        cleanup_backend_connections(include_process_resources=True)


@pytest.fixture(autouse=True)
def visible_source_root(monkeypatch):
    """Private, visible root for benchmark visible-source aliases.

    The default root is one shared directory under /tmp, so stale aliases from
    other runs leak into tests. ``tmp_path`` is not usable: a ``--basetemp``
    under a hidden directory (``.claude/``) makes every alias hidden.
    """
    from benchmark.datasets.visible_source import VISIBLE_SOURCE_ROOT_ENV

    with tempfile.TemporaryDirectory(prefix="ohcs-visible-") as directory:
        root = Path(directory)
        monkeypatch.setenv(VISIBLE_SOURCE_ROOT_ENV, str(root))
        yield root
