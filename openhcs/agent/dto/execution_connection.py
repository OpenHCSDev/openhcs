"""Typed connection declaration shared by execution and lightweight clients."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import TYPE_CHECKING

from python_introspect import project_dataclass, validate_annotated_dataclass
from zmqruntime.config import NonBlankString, SocketPort, TransportMode
from zmqruntime.transport import TransportEndpoint, resolve_transport_mode

from openhcs.agent.dto.common import JsonObject

if TYPE_CHECKING:
    from openhcs.runtime.zmq_config import OpenHCSZMQConfig
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient


@dataclass(frozen=True, slots=True)
class ExecutionConnectionSpec:
    host: NonBlankString = "localhost"
    port: SocketPort | None = None
    transport_mode: TransportMode | None = None
    persistent: bool = True

    def __post_init__(self) -> None:
        validate_annotated_dataclass(self)

    def require_port(self, purpose: str) -> int:
        if self.port is None:
            raise ValueError(f"{purpose} requires an explicit port.")
        return self.port

    def transport_mode_value(self) -> str | None:
        return TransportMode.optional_to_text(self.transport_mode)

    def runtime_arguments(self) -> dict[str, object]:
        """Project exact typed constructor arguments for this connection."""

        return asdict(self.public_connection())

    def specified_runtime_arguments(self) -> dict[str, object]:
        """Project typed constructor arguments while omitting unset optionals."""

        return {
            name: value
            for name, value in self.runtime_arguments().items()
            if value is not None
        }

    def tool_arguments(self) -> JsonObject:
        """Project the canonical JSON-compatible tool argument fields."""

        arguments = self.runtime_arguments()
        arguments["transport_mode"] = self.transport_mode_value()
        return arguments

    def public_connection(self) -> ExecutionConnectionSpec:
        """Return the credential-free base connection declaration."""

        return project_dataclass(ExecutionConnectionSpec, self)

    def zmq_data_url(self, config) -> str:
        from zmqruntime.transport import get_zmq_transport_url

        return get_zmq_transport_url(
            self.require_port("ZMQ data URL"),
            host=self.host,
            mode=self.transport_mode,
            config=config,
        )

    def zmq_control_port(self, config) -> int:
        from zmqruntime.transport import get_control_port

        return get_control_port(self.require_port("ZMQ control port"), config)

    def zmq_control_url(self, config) -> str:
        from zmqruntime.transport import get_control_url

        return get_control_url(
            self.require_port("ZMQ control URL"),
            self.transport_mode,
            host=self.host,
            config=config,
        )

    def transport_endpoint(self) -> TransportEndpoint:
        """Project this connection declaration to its generic endpoint identity."""

        return TransportEndpoint(
            host=self.host,
            port=self.require_port("ZMQ transport endpoint"),
            transport_mode=resolve_transport_mode(self.transport_mode),
        )

    def execution_client(
        self,
        config: OpenHCSZMQConfig,
    ) -> ZMQExecutionClient:
        """Construct the OpenHCS execution client for this exact connection."""

        from openhcs.runtime.zmq_execution_client import ZMQExecutionClient

        return ZMQExecutionClient(
            port=self.port,
            host=self.host,
            persistent=self.persistent,
            transport_mode=self.transport_mode,
            config=config,
        )
