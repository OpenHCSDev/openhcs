"""Global pytest configuration for OpenHCS integration tests."""

import os
import signal
import uuid
from collections.abc import Iterator

from openhcs._source_dependencies import ensure_source_checkout_external_paths

ensure_source_checkout_external_paths()

import psutil
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


SPAWN_MARKER_VARIABLE = "OPENHCS_TEST_SPAWN_MARKER"


def _marked_processes(marker: str) -> list[psutil.Process]:
    found = []
    for process in psutil.process_iter(["pid"]):
        if process.pid == os.getpid():
            continue
        try:
            if process.environ().get(SPAWN_MARKER_VARIABLE) == marker:
                found.append(process)
        except (psutil.AccessDenied, psutil.NoSuchProcess, psutil.ZombieProcess):
            continue
    return found


@pytest.fixture
def reap_spawned_processes(monkeypatch) -> Iterator[None]:
    """Kill every process this test spawned, detached ones included.

    Execution and viewer servers start their own sessions (setsid), so they
    outlive the test and its process tree. Each test marks its environment;
    every descendant inherits the marker, and teardown kills the process group
    of each marked process still alive, whether the test passed or failed.
    """
    marker = uuid.uuid4().hex
    monkeypatch.setenv(SPAWN_MARKER_VARIABLE, marker)
    yield
    own_group = os.getpgid(0)
    survivors = _marked_processes(marker)
    for process in survivors:
        try:
            group = os.getpgid(process.pid)
            if group != own_group:
                os.killpg(group, signal.SIGTERM)
            else:
                process.terminate()
        except (ProcessLookupError, psutil.NoSuchProcess):
            continue
    _gone, alive = psutil.wait_procs(survivors, timeout=10)
    for process in alive:
        try:
            group = os.getpgid(process.pid)
            if group != own_group:
                os.killpg(group, signal.SIGKILL)
            else:
                process.kill()
        except (ProcessLookupError, psutil.NoSuchProcess):
            continue
    psutil.wait_procs(alive, timeout=10)
