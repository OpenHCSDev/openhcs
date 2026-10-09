"""Diagnostic client launch projection from the selected checkout root."""

from dataclasses import dataclass

from openhcs.mcp.dev_client_core import McpDevServerSpec
from openhcs.runtime.import_authority import OpenHCSRuntimeImportAuthority
from scripts.mcp_memory_diagnostic import DIAGNOSTIC_MODULE


@dataclass(frozen=True, slots=True)
class DiagnosticServerSpec(McpDevServerSpec):
    """Instrumented server launched from the parent's exact import root."""

    module_name: str = DIAGNOSTIC_MODULE
    data_directory: str = ""

    def process_args(self) -> tuple[str, ...]:
        import_root = OpenHCSRuntimeImportAuthority.current().import_root
        return (
            "-c",
            "import runpy, sys; "
            f"sys.path.insert(0, {str(import_root)!r}); "
            f"runpy.run_module({self.module_name!r}, run_name='__main__', "
            "alter_sys=True)",
            "--surface",
            self.surface_profile.name,
            "--server",
        )

    def environment(self) -> dict[str, str]:
        return {
            **McpDevServerSpec.environment(self),
            "XDG_DATA_HOME": self.data_directory,
            "XDG_CACHE_HOME": self.data_directory,
            "XDG_CONFIG_HOME": self.data_directory,
        }
