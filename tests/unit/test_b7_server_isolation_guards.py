"""Guards for B7: the checks that keep a client on a server it may use."""

from __future__ import annotations

import ast
import inspect
import json
import os
import subprocess
import sys
from pathlib import Path

import pytest
import zmq

import zmqruntime.client
import zmqruntime.transport_modes
from zmqruntime.client import ZMQClient
from zmqruntime.config import ZMQConfig

import openhcs
from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority
from openhcs.runtime.zmq_config import (
    OPENHCS_ZMQ_CONFIG,
    SOCKET_ROOT_ENV,
    SocketPathTooLongError,
    checkout_socket_root,
    require_bindable_address,
)
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient
from openhcs.runtime.zmq_execution_server import ZMQExecutionServer

REPOSITORY_ROOT = Path(openhcs.__file__).resolve().parents[1]
LAUNCH_CHECKS = {"_require_started_endpoint", "_require_usable_endpoint"}


def _functions_assigning_a_connection() -> dict[str, ast.FunctionDef]:
    tree = ast.parse(inspect.getsource(ZMQClient))
    assigning = {}
    for function in ast.walk(tree):
        if not isinstance(function, ast.FunctionDef):
            continue
        for node in ast.walk(function):
            if not isinstance(node, ast.Assign):
                continue
            targets = [ast.unparse(target) for target in node.targets]
            cleared = isinstance(node.value, ast.Constant) and node.value.value is None
            if "self._connection" in targets and not cleared:
                assigning[function.name] = function
    return assigning


def test_a_client_holds_a_connection_only_after_the_launch_check():
    assigning = _functions_assigning_a_connection()

    assert assigning, "ZMQClient no longer assigns _connection where this guard looks"
    for name, function in assigning.items():
        if name == "__init__":
            continue
        called = {
            node.func.attr
            for node in ast.walk(function)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
        }
        assert called & LAUNCH_CHECKS, (
            f"ZMQClient.{name} establishes a connection without checking "
            "the server's launch"
        )


def test_socket_paths_come_from_the_socket_root():
    for module in (zmqruntime.transport_modes, zmqruntime.client):
        assert "Path.home()" not in inspect.getsource(module), module.__name__
    # ZMQ endpoints only. The MCP resident-server socket (openhcs/mcp/socket.py)
    # is a different transport and already names its checkout; it is U4's.
    for package in ("runtime", "agent", "core", "pyqt_gui"):
        for source in (REPOSITORY_ROOT / "openhcs" / package).rglob("*.py"):
            if source.name == "zmq_config.py":
                continue
            text = source.read_text(encoding="utf-8")
            assert "ipc_socket_dir" not in text or "Path.home()" not in text, source


def test_the_harness_picks_no_free_port_for_an_execution_server():
    for source in (REPOSITORY_ROOT / "benchmark").glob("*.py"):
        assert "DataControlPortPairAuthority" not in source.read_text(
            encoding="utf-8"
        ), source


def test_client_and_server_state_the_import_root_as_their_code_root():
    import_root = str(OpenHCSRuntimeImportAuthority.current().import_root)

    assert ZMQExecutionClient.code_root() == import_root
    assert ZMQExecutionServer.code_root() == import_root

    class ScriptClient(ZMQExecutionClient):
        """A subclass defined elsewhere is still this checkout's client."""

    assert ScriptClient.code_root() == import_root


def test_each_checkout_has_its_own_socket_root(monkeypatch, tmp_path):
    assert OPENHCS_ZMQ_CONFIG.socket_root() != ZMQConfig(app_name="openhcs").socket_root()

    monkeypatch.delenv(SOCKET_ROOT_ENV)
    here = OPENHCS_ZMQ_CONFIG.socket_root()
    assert here == checkout_socket_root()

    other_checkout = tmp_path / "checkout"
    (other_checkout / "openhcs").mkdir(parents=True)
    (other_checkout / "openhcs" / "__init__.py").write_text("", encoding="utf-8")
    monkeypatch.setattr(
        OpenHCSRuntimeImportAuthority,
        "current",
        classmethod(lambda cls: cls(other_checkout)),
    )
    assert OPENHCS_ZMQ_CONFIG.socket_root() != here

    monkeypatch.setenv(SOCKET_ROOT_ENV, str(tmp_path))
    assert OPENHCS_ZMQ_CONFIG.socket_root() == tmp_path


def test_this_test_run_has_a_private_socket_root():
    root = OPENHCS_ZMQ_CONFIG.socket_root()

    assert root.parent == checkout_socket_root()
    assert root.is_dir()


_CHILD_REPORT = """
import json
from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

client = ZMQExecutionClient(port=65000, persistent=False)
print(json.dumps({
    "socket_root": str(client.config.socket_root()),
    "code_root": client.launch().code_root,
    "audience": client.launch().audience,
    "control_url": client.endpoint.control_url(client.config),
}))
"""


def _report(environment: dict[str, str]) -> dict[str, str]:
    completed = subprocess.run(
        [sys.executable, "-c", _CHILD_REPORT],
        env={**environment, "PYTHONPATH": str(REPOSITORY_ROOT)},
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert completed.returncode == 0, completed.stderr[-2000:]
    return json.loads(completed.stdout.splitlines()[-1])


def test_a_child_process_computes_its_parents_socket_root_and_launch():
    """A server or CLI started by this process looks where this process looks."""

    client = ZMQExecutionClient(port=65000, persistent=False)

    assert _report(dict(os.environ)) == {
        "socket_root": str(client.config.socket_root()),
        "code_root": client.launch().code_root,
        "audience": client.launch().audience,
        "control_url": client.endpoint.control_url(client.config),
    }


def test_a_private_socket_root_can_be_bound_whatever_tmpdir_is(tmp_path):
    """The test run's sockets do not move with ``TMPDIR`` (a deep one cannot bind)."""

    deep_tmpdir = tmp_path / ("d" * 120)
    deep_tmpdir.mkdir()
    child = (
        "from openhcs.runtime.zmq_config import use_private_socket_root\n"
        "use_private_socket_root()\n" + _CHILD_REPORT
    )
    completed = subprocess.run(
        [sys.executable, "-c", child],
        env={
            **os.environ,
            "PYTHONPATH": str(REPOSITORY_ROOT),
            "TMPDIR": str(deep_tmpdir),
        },
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert completed.returncode == 0, completed.stderr[-2000:]
    report = json.loads(completed.stdout.splitlines()[-1])

    assert Path(report["socket_root"]).parent == checkout_socket_root()
    assert not Path(report["socket_root"]).exists()
    require_bindable_address(report["control_url"])


def test_a_client_refuses_a_socket_path_no_server_can_bind(monkeypatch, tmp_path):
    """It raises before starting a server, and names the path and the limit."""

    root = tmp_path / ("r" * 120)
    monkeypatch.setenv(SOCKET_ROOT_ENV, str(root))
    client = ZMQExecutionClient(port=65000, persistent=False)
    monkeypatch.setattr(
        client, "_spawn_server_process", lambda: pytest.fail("a server was started")
    )

    with pytest.raises(SocketPathTooLongError) as refusal:
        client.connect(timeout=5)

    assert str(root) in str(refusal.value)
    assert str(zmq.IPC_PATH_MAX_LEN) in str(refusal.value)
    assert SOCKET_ROOT_ENV in str(refusal.value)
