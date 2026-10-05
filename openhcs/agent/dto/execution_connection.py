"""Typed connection declaration shared by execution and lightweight clients."""

from __future__ import annotations

from dataclasses import asdict, dataclass, replace
from typing import TYPE_CHECKING

from python_introspect import project_dataclass, validate_annotated_dataclass
from zmqruntime.config import NonBlankString, SocketPort, TransportMode
from zmqruntime.transport import TransportEndpoint

from openhcs.agent.dto.common import AgentDataclassCliRequest, JsonObject
from openhcs.runtime.zmq_config import OPENHCS_ZMQ_CONFIG, OpenHCSZMQConfig

if TYPE_CHECKING:
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient


@dataclass(frozen=True, slots=True)
class ExecutionConnectionSpec(AgentDataclassCliRequest):
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

    def zmq_data_url(self, config: OpenHCSZMQConfig) -> str:
        return self.transport_endpoint(config, purpose="ZMQ data URL").data_url(config)

    def zmq_control_port(self, config: OpenHCSZMQConfig) -> int:
        return self.transport_endpoint(config, purpose="ZMQ control port").control_port(config)

    def zmq_control_url(self, config: OpenHCSZMQConfig) -> str:
        return self.transport_endpoint(config, purpose="ZMQ control URL").control_url(config)

    def transport_endpoint(
        self,
        config: OpenHCSZMQConfig = OPENHCS_ZMQ_CONFIG,
        *,
        purpose: str = "ZMQ transport endpoint",
    ) -> TransportEndpoint:
        """Project the exact route using the supplied execution config owner."""

        return config.client_endpoint(
            self.require_port(purpose),
            host=self.host,
            transport_mode=self.transport_mode,
        )

    def resolved(self, config: OpenHCSZMQConfig) -> ExecutionConnectionSpec:
        """Retain effective routing in the public nominal connection."""

        return replace(
            self.public_connection(),
            transport_mode=self.transport_endpoint(config).transport_mode,
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
