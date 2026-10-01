"""Shared persistence and export-observation policies for materialized artifacts."""

from .core import MaterializationSpec


class TerminalMaterializationSpec(MaterializationSpec):
    """Retain internal artifacts without declaring an external pipeline export."""

    def participates_in_runtime_export_observation(self) -> bool:
        return False


class StreamingOnlyMaterializationSpec(MaterializationSpec):
    """Prepare viewer outputs without declaring persistent or external exports."""

    def participates_in_runtime_export_observation(self) -> bool:
        return False

    def participates_in_persistent_materialization(self) -> bool:
        return False
