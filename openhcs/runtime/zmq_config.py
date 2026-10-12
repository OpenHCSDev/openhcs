"""OpenHCS execution transport configuration."""

from __future__ import annotations

import atexit
import hashlib
import os
import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path

import zmq
from zmqruntime.config import NonBlankString
from zmqruntime.execution.config import ExecutionTransportConfig

from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority

SOCKET_ROOT_ENV = "OPENHCS_SOCKET_ROOT"
"""Directory that replaces the socket root for one process tree.

Child processes inherit it, so a test run or a script and every server and
viewer it starts share one namespace that nothing else on the machine sees.
"""


def checkout_socket_root() -> Path:
    """Socket root of this OpenHCS checkout or installation.

    Port ``n`` names one socket file per root. Deriving the root from the
    import root keeps two checkouts run by one user from sharing addresses.
    """

    import_root = OpenHCSRuntimeImportAuthority.current().import_root
    digest = hashlib.sha256(str(import_root).encode("utf-8")).hexdigest()[:8]
    return Path.home() / ".openhcs" / digest


def use_private_socket_root() -> Path:
    """Give this process and its children a socket root of their own.

    The root is a new directory beneath the checkout's socket root, so its
    length does not depend on ``TMPDIR``: a socket path longer than
    ``zmq.IPC_PATH_MAX_LEN`` cannot be bound. It is removed at exit.
    """

    parent = checkout_socket_root()
    parent.mkdir(parents=True, exist_ok=True)
    root = Path(tempfile.mkdtemp(prefix="run-", dir=parent))
    os.environ[SOCKET_ROOT_ENV] = str(root)
    atexit.register(shutil.rmtree, root, ignore_errors=True)
    return root


class SocketPathTooLongError(ValueError):
    """An IPC socket path that no server can bind."""


def require_bindable_address(url: str) -> None:
    """Refuse an IPC address the operating system cannot bind.

    A server asked to bind such a path fails at startup, and its client would
    only learn that the server never became ready.
    """

    scheme, _, path = url.partition("://")
    if scheme == "ipc" and len(os.fsencode(path)) > zmq.IPC_PATH_MAX_LEN:
        raise SocketPathTooLongError(
            f"Socket path {path} is {len(os.fsencode(path))} bytes; the limit "
            f"is {zmq.IPC_PATH_MAX_LEN}. Set {SOCKET_ROOT_ENV} to a shorter "
            "directory (a private server takes its directory from TMPDIR)."
        )


@dataclass(frozen=True, slots=True)
class OpenHCSZMQConfig(ExecutionTransportConfig):
    """zmqruntime's execution transport under OpenHCS's application names."""

    ipc_socket_prefix: NonBlankString = "openhcs-zmq"
    """OpenHCS namespace prefix for generated IPC data and control sockets."""

    app_name: NonBlankString = "openhcs"
    """OpenHCS application namespace used in transport identities and runtime paths."""

    def socket_root(self) -> Path:
        declared = os.environ.get(SOCKET_ROOT_ENV)
        return Path(declared) if declared else checkout_socket_root()


OPENHCS_ZMQ_CONFIG = OpenHCSZMQConfig()
