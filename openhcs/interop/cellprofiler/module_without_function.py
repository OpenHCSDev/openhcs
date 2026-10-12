"""A CellProfiler module OpenHCS declares before it has the function to run it.

Such a module converts like any other: its settings bind to step kwargs and
its outputs are wired into the dataflow. Its file defines the step's function
with those kwargs, and that function cannot run. Compilation is refused twice
over, in the order a user can act on: first for a distribution the file
requires and that is not installed (the validator names the extra), then for
what OpenHCS itself still lacks.
"""

from __future__ import annotations

from typing import TYPE_CHECKING, ClassVar, NoReturn

from openhcs.interop.cellprofiler.module_declarations import CellProfilerModule
from openhcs.processing.backends.lib_registry.openhcs_registry import (
    distributions_not_installed,
)

if TYPE_CHECKING:
    from openhcs.core.function_patterns import NormalizedFunctionItem


def cellprofiler_binary(value: str) -> bool:
    """Read a CellProfiler ``Binary`` setting as CellProfiler does: only "Yes" is true.

    CellProfiler loads settings by position, so a file saved by one revision of
    a plugin and read by another can hold another setting's value in a Binary
    row. CellProfiler reads any such value as false.
    """

    return value.strip() == "Yes"


class ModuleWithoutFunction(CellProfilerModule):
    """Parent of declared modules whose function OpenHCS cannot run yet."""

    what_openhcs_lacks: ClassVar[str]
    """What must exist in OpenHCS before the module can run, as one sentence."""

    @classmethod
    def cannot_run_message(cls) -> str:
        """Say which module cannot run and what OpenHCS lacks."""

        return (
            f"CellProfiler module {cls.require_module_name()!r} is declared, so its "
            f"settings convert, but it cannot run: {cls.what_openhcs_lacks} "
            "Replace the step's function to run the pipeline."
        )

    @classmethod
    def cannot_run(cls) -> NoReturn:
        """Body of the module's function until OpenHCS has what it lacks."""

        raise NotImplementedError(cls.cannot_run_message())

    @classmethod
    def validate_compilation(cls, invocation: NormalizedFunctionItem) -> None:
        """Refuse to compile once every distribution the file requires is installed.

        While one is absent the pipeline's validator refuses with the install
        command, which is the first thing the user can do.
        """

        if distributions_not_installed(invocation.contract.func):
            return
        raise ValueError(cls.cannot_run_message())
