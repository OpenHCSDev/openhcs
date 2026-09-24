"""Execution-server environment evidence for ordinary pipeline observations."""

from __future__ import annotations

import platform
import sys
from dataclasses import dataclass
from importlib.metadata import distributions
from pathlib import Path


@dataclass(frozen=True, slots=True)
class InstalledDistributionVersion:
    """One installed distribution visible to the execution server."""

    name: str
    version: str


@dataclass(frozen=True, slots=True)
class RuntimeEnvironmentSnapshot:
    """Process-owned dependency inventory, captured before accepting jobs."""

    python_executable: str
    python_version: str
    python_implementation: str
    sys_platform: str
    machine: str
    installed_distributions: tuple[InstalledDistributionVersion, ...]

    @classmethod
    def current(cls) -> RuntimeEnvironmentSnapshot:
        installed = {
            InstalledDistributionVersion(item.name, item.version)
            for item in distributions()
        }
        return cls(
            python_executable=str(Path(sys.executable).resolve()),
            python_version=platform.python_version(),
            python_implementation=platform.python_implementation(),
            sys_platform=sys.platform,
            machine=platform.machine(),
            installed_distributions=tuple(
                sorted(installed, key=lambda item: (item.name.casefold(), item.version))
            ),
        )
