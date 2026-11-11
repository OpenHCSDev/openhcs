"""The Cellpose functions, derived from the installed Cellpose."""

from openhcs.processing.backends.lib_registry.model_library import (
    DerivedLibraryRegistry,
)


class CellposeRegistry(DerivedLibraryRegistry):
    """Cellpose's models as catalogue functions."""

    _registry_name = "cellpose"
    DISTRIBUTION = "cellpose"
    DECLARATION_MODULE = "openhcs.processing.backends.lib_registry.derived.cellpose"

    @classmethod
    def supports_cpu_only(cls) -> bool:
        """False: Cellpose imports torch, which a CPU-only process does not load.

        The functions take and return NumPy arrays, so the memory type alone
        would admit them.
        """

        return False
