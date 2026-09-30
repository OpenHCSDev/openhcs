"""Diagnostic client launch projection; no alternative import authority."""

from dataclasses import dataclass

from openhcs.mcp.dev_client_core import McpDevServerSpec
from openhcs.mcp.memory_diagnostic import DIAGNOSTIC_MODULE


@dataclass(frozen=True, slots=True)
class DiagnosticServerSpec(McpDevServerSpec):
    """Instrumented server using the normal exact-root launch projection."""

    module_name: str = DIAGNOSTIC_MODULE
    data_directory: str = ""

    def process_args(self) -> tuple[str, ...]:
        return (*McpDevServerSpec.process_args(self), "--server")

    def environment(self) -> dict[str, str]:
        return {
            **McpDevServerSpec.environment(self),
            "XDG_DATA_HOME": self.data_directory,
            "XDG_CACHE_HOME": self.data_directory,
            "XDG_CONFIG_HOME": self.data_directory,
        }
