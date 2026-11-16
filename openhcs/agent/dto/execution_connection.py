"""Typed connection declaration shared by execution and lightweight clients."""

from __future__ import annotations

from dataclasses import dataclass, field

from formbridge.connection import EndpointConnectionFields, EndpointConnectionSpec
from python_introspect import project_dataclass



@dataclass(frozen=True, slots=True)
class ExecutionConnectionSpec(EndpointConnectionSpec):
    """Connection to an OpenHCS execution server."""

    def public_connection(self) -> ExecutionConnectionSpec:
        """Return the credential-free execution connection declaration."""

        return project_dataclass(ExecutionConnectionSpec, self)


@dataclass(frozen=True, kw_only=True)
class ExecutionConnectionFields(EndpointConnectionFields):
    """A request or result that carries one execution connection."""

    connection: ExecutionConnectionSpec = field(default_factory=ExecutionConnectionSpec)
