"""Typed connection declaration shared by execution and lightweight clients."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from formbridge.connection import EndpointConnectionFields, EndpointConnectionSpec
from python_introspect import project_dataclass

from openhcs.runtime.zmq_config import OpenHCSZMQConfig

if TYPE_CHECKING:
    from openhcs.runtime.zmq_execution_client import ZMQExecutionClient


@dataclass(frozen=True, slots=True)
class ExecutionConnectionSpec(EndpointConnectionSpec):
    """Connection to an OpenHCS execution server."""

    def public_connection(self) -> ExecutionConnectionSpec:
        """Return the credential-free execution connection declaration."""

        return project_dataclass(ExecutionConnectionSpec, self)

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


@dataclass(frozen=True, kw_only=True)
class ExecutionConnectionFields(EndpointConnectionFields):
    """A request or result that carries one execution connection."""

    connection: ExecutionConnectionSpec = field(default_factory=ExecutionConnectionSpec)
