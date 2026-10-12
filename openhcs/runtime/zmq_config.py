"""OpenHCS execution transport configuration."""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass
from pathlib import Path

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
