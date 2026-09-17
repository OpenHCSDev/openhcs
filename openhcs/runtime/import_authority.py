"""Authoritative Python import provenance for OpenHCS child processes."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Self


class OpenHCSRuntimeImportError(RuntimeError):
    """Raised when the loaded OpenHCS import root cannot be proved."""


@dataclass(frozen=True, slots=True)
class OpenHCSRuntimeImportAuthority:
    """Own the exact import root inherited by OpenHCS child processes.

    The root is derived from the already-loaded OpenHCS package rather than
    from a working directory or environment search path.  Child interpreters
    therefore import the same checkout or installation as their parent even
    when a runtime-specific working directory is required.
    """

    import_root: Path

    package_name = "openhcs"

    def __post_init__(self) -> None:
        resolved_root = self.import_root.resolve(strict=False)
        package_init = resolved_root / self.package_name / "__init__.py"
        if not package_init.is_file():
            raise OpenHCSRuntimeImportError(
                "OpenHCS runtime import root does not contain the loaded package: "
                f"{resolved_root}"
            )
        object.__setattr__(self, "import_root", resolved_root)

    @classmethod
    def current(cls) -> Self:
        """Derive the import root from this loaded authority declaration."""

        package_root = Path(__file__).resolve().parents[1]
        if package_root.name != cls.package_name:
            raise OpenHCSRuntimeImportError(
                "Loaded runtime authority is not inside the OpenHCS package: "
                f"{package_root}"
            )
        return cls(package_root.parent)

    def module_bootstrap_code(self, module_name: str) -> str:
        """Return code that runs one OpenHCS module from this exact root."""

        if module_name != self.package_name and not module_name.startswith(
            f"{self.package_name}."
        ):
            raise OpenHCSRuntimeImportError(
                "Runtime import authority only launches OpenHCS modules, got "
                f"{module_name!r}."
            )
        return (
            "import runpy, sys; "
            f"sys.path.insert(0, {str(self.import_root)!r}); "
            f"runpy.run_module({module_name!r}, run_name='__main__', alter_sys=True)"
        )

    def module_process_arguments(self, module_name: str) -> tuple[str, str]:
        """Project one module launch to interpreter arguments."""

        return "-c", self.module_bootstrap_code(module_name)
