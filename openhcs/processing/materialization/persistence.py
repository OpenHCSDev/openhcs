"""Shared persistence and export-observation policies for materialized artifacts."""

from __future__ import annotations
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from openhcs.core.artifacts.plans import ArtifactOutputPlan

from .core import MaterializationSpec


class TerminalMaterializationSpec(MaterializationSpec):
    """Retain internal artifacts without declaring an external pipeline export."""

    def participates_in_runtime_export_observation(self) -> bool:
        return False

    def filename_qualifier(self, output_plan: ArtifactOutputPlan) -> str | None:
        """Retain the compiled image role without changing its source address."""
        return output_plan.retained_filename_qualifier()


class StreamingOnlyMaterializationSpec(MaterializationSpec):
    """Prepare viewer outputs without declaring persistent or external exports."""

    def participates_in_runtime_export_observation(self) -> bool:
        return False

    def participates_in_persistent_materialization(self) -> bool:
        return False
