"""Pytest configuration owned by the integration-test subtree."""

from __future__ import annotations

import os
import signal
import socket
import uuid
from collections.abc import Callable, Iterator, Sequence
from dataclasses import replace
from typing import Any

import psutil
import pytest
from zmqruntime import EndpointShutdownMode, ZMQClient
from zmqruntime.transport import DataControlPortPairAuthority

from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG

from tests.integration.helpers.fixture_utils import (
    BACKEND_CONFIGS,
    DATA_TYPE_CONFIGS,
    EXECUTION_MODE_CONFIGS,
    MICROSCOPE_CONFIGS,
    SEQUENTIAL_CONFIGS,
    ZMQ_EXECUTION_MODE_CONFIGS,
)

VISUALIZER_CONFIGS = {
    "none": {"enable_napari": False, "enable_fiji": False},
    "napari": {"enable_napari": True, "enable_fiji": False},
    "fiji": {"enable_napari": False, "enable_fiji": True},
    "napari+fiji": {"enable_napari": True, "enable_fiji": True},
}


def _integration_test_config() -> dict[
    str,
    tuple[str, Sequence[str], Callable[[str], Any]],
]:
    return {
        "backend_config": ("--it-backends", BACKEND_CONFIGS, lambda value: value),
        "microscope_config": (
            "--it-microscopes",
            tuple(MICROSCOPE_CONFIGS),
            MICROSCOPE_CONFIGS.__getitem__,
        ),
        "data_type_config": (
            "--it-dims",
            tuple(DATA_TYPE_CONFIGS),
            DATA_TYPE_CONFIGS.__getitem__,
        ),
        "execution_mode": (
            "--it-exec-mode",
            EXECUTION_MODE_CONFIGS,
            lambda value: value,
        ),
        "zmq_execution_mode": (
            "--it-zmq-mode",
            ZMQ_EXECUTION_MODE_CONFIGS,
            lambda value: value,
        ),
        "processing_axis": (
            "--it-processing-axis",
            ("well",),
            lambda value: value,
        ),
        "visualizer_config": (
            "--it-visualizers",
            tuple(VISUALIZER_CONFIGS),
            VISUALIZER_CONFIGS.__getitem__,
        ),
        "sequential_config": (
            "--it-sequential",
            tuple(SEQUENTIAL_CONFIGS),
            SEQUENTIAL_CONFIGS.__getitem__,
        ),
    }


def _selected_choices(
    config: pytest.Config,
    option_name: str,
    choices: Sequence[str],
) -> tuple[str, ...]:
    option_value = config.getoption(option_name)
    if option_value == "all":
        return tuple(choices)
    selected = frozenset(value.strip() for value in option_value.split(","))
    return tuple(choice for choice in choices if choice in selected)


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    """Parameterize only fixtures owned by integration tests."""

    for fixture_name, (option, choices, mapper) in _integration_test_config().items():
        if fixture_name not in metafunc.fixturenames:
            continue
        selected = _selected_choices(metafunc.config, option, choices)
        metafunc.parametrize(
            fixture_name,
            tuple(mapper(choice) for choice in selected),
            ids=selected,
            scope="module",
        )


@pytest.fixture
def enable_napari(
    request: pytest.FixtureRequest, visualizer_config: dict[str, bool]
) -> bool:
    return bool(
        request.config.getoption("--enable-napari")
        or visualizer_config["enable_napari"]
    )


@pytest.fixture
def enable_fiji(
    request: pytest.FixtureRequest, visualizer_config: dict[str, bool]
) -> bool:
    return bool(
        request.config.getoption("--enable-fiji") or visualizer_config["enable_fiji"]
    )


def _os_assigned_port() -> int:
    """Ask the OS for a currently unused port to start this run's search from."""
    while True:
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as probe:
            probe.bind(("127.0.0.1", 0))
            port = probe.getsockname()[1]
        if port + OPENHCS_ZMQ_CONFIG.control_port_offset <= 65535:
            return port


@pytest.fixture
def free_port_pair() -> Iterator[Callable[[], int]]:
    """Allocate this test's own data/control endpoint pairs.

    Every server, viewer and client a test starts takes its port from here, so
    concurrent runs never share an endpoint. Pairs come from the transport owner
    that will bind them; the search starts at an OS-assigned port instead of the
    configured default, which every concurrent run would otherwise pick first.
    Whatever still listens on an allocated pair at teardown, such as a viewer
    a spawned execution server kept alive, is shut down.
    """
    allocated: set[int] = set()
    data_ports: list[int] = []

    def allocate() -> int:
        pair = DataControlPortPairAuthority.acquire(
            replace(OPENHCS_ZMQ_CONFIG, default_port=_os_assigned_port()),
            transport_mode=OPENHCS_ZMQ_CONFIG.transport_mode,
            excluded=allocated,
        )
        allocated.update(pair.ports)
        data_ports.append(pair.data_port)
        return pair.data_port

    yield allocate

    for port in data_ports:
        endpoint = OPENHCS_ZMQ_CONFIG.client_endpoint(port)
        for mode in (EndpointShutdownMode.GRACEFUL, EndpointShutdownMode.FORCE):
            if not endpoint.occupied_ports(OPENHCS_ZMQ_CONFIG):
                break
            ZMQClient.shutdown_endpoint_on_port(
                port,
                mode,
                transport_mode=endpoint.transport_mode,
                host=endpoint.host,
                config=OPENHCS_ZMQ_CONFIG,
            )


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


@pytest.fixture(autouse=True)
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
