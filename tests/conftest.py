"""Global pytest configuration for OpenHCS integration tests."""

import os
import signal
import tempfile
import uuid
from collections.abc import Callable, Hashable, Iterator
from contextlib import ExitStack
from pathlib import Path

from openhcs._source_dependencies import ensure_source_checkout_external_paths
from openhcs.utils.environment import OpenHCSProcessEnvironment

ensure_source_checkout_external_paths()

from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG, use_private_socket_root

# Every socket and lock file of this pytest process, and of the servers and
# viewers it starts, lives under a root no other run sees. Each xdist worker
# imports this module, so each has its own.
use_private_socket_root()

import psutil
import pytest
from metaclass_registry.testing import restored_registry
from polystore.imagej_distribution import (
    FijiArchiveDistribution,
    ImageJArchiveDownloadPolicy,
)
from zmqruntime.messages import AckReturnRoute, ProcessIdentity

from tests import family_registries

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
CPU_ONLY_MODE = OpenHCSProcessEnvironment.cpu_only_mode()
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


@pytest.fixture
def unix_socket_dir():
    """A private directory for AF_UNIX/IPC sockets, beneath the socket root.

    ``sun_path`` holds about 104-108 bytes, so a socket under a deep
    ``tmp_path`` (long ``--basetemp`` or ``TMPDIR``) cannot bind.
    """
    with tempfile.TemporaryDirectory(
        prefix="s-", dir=OPENHCS_ZMQ_CONFIG.socket_root()
    ) as directory:
        yield Path(directory)


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


@pytest.hookimpl(wrapper=True)
def pytest_make_collect_report(collector):
    """Members a test module declares at import leave their families after the import."""
    report = yield
    if isinstance(collector, pytest.Module):
        family_registries.withdraw_module_members()
    return report


@pytest.fixture(scope="module", autouse=True)
def module_family_members(request) -> Iterator[None]:
    """Members a test module declares at import are members while its tests run."""
    family_registries.join_module_members(request.module)
    yield
    family_registries.leave_module_members()


@pytest.fixture(autouse=True)
def restored_family_registries(module_family_members) -> Iterator[None]:
    """Every family registry is, after a test, what it was before it."""
    before = family_registries.registry_snapshot()
    yield
    family_registries.restore_registries(before)


@pytest.fixture(autouse=True)
def restored_global_configs() -> Iterator[None]:
    """The saved and live global config of every config type is, after a test, what it was before it."""
    from objectstate import global_config

    def config_types() -> set[type]:
        return {
            *global_config._saved_global_config_contexts,
            *global_config._live_global_config_contexts,
        }

    before = {
        config_type: global_config.GlobalContextValues.capture(config_type)
        for config_type in config_types()
    }
    yield
    for config_type in config_types():
        before.get(
            config_type, global_config.GlobalContextValues(config_type, None, None)
        ).apply()


@pytest.fixture
def stand_in_members() -> Iterator[Callable[..., None]]:
    """Let a test define stand-in members of a registered family.

    ``stand_in_members(member, *keys)`` frees ``keys`` of the family that
    ``member`` belongs to, so the test can define its own class under them.
    When the test ends the registry is exactly what it was: the stand-ins are
    gone and the production classes hold their keys again.
    """

    with ExitStack() as restored:

        def allow(member: type, *released_keys: Hashable) -> None:
            restored.enter_context(restored_registry(member, released=released_keys))

        yield allow


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
    survivors = _marked_processes(marker)
    for process in survivors:
        _stop_marked_process(process, force=False)
    _gone, alive = psutil.wait_procs(survivors, timeout=10)
    for process in alive:
        _stop_marked_process(process, force=True)
    psutil.wait_procs(alive, timeout=10)


def _stop_marked_process(process: psutil.Process, *, force: bool) -> None:
    """Signal a detached POSIX session's whole group, else the process itself.

    Windows has no process groups; every descendant carries the marker, so
    stopping each marked process covers the tree there.
    """
    try:
        if os.name == "posix":
            group = os.getpgid(process.pid)
            if group != os.getpgid(0):
                os.killpg(group, signal.SIGKILL if force else signal.SIGTERM)
                return
        if force:
            process.kill()
        else:
            process.terminate()
    except (ProcessLookupError, psutil.NoSuchProcess):
        return
