"""OpenHCS execution transport configuration."""

from __future__ import annotations

from dataclasses import dataclass

from zmqruntime.config import NonBlankString
from zmqruntime.execution.config import ExecutionTransportConfig


@dataclass(frozen=True, slots=True)
class OpenHCSZMQConfig(ExecutionTransportConfig):
    """zmqruntime's execution transport under OpenHCS's application names."""

    ipc_socket_prefix: NonBlankString = "openhcs-zmq"
    """OpenHCS namespace prefix for generated IPC data and control sockets."""

    app_name: NonBlankString = "openhcs"
    """OpenHCS application namespace used in transport identities and runtime paths."""


OPENHCS_ZMQ_CONFIG = OpenHCSZMQConfig()
