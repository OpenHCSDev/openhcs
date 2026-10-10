"""
Materialization flag planner for OpenHCS.

This module provides the MaterializationFlagPlanner class, which is responsible for
determining materialization flags and backend selection for each step in a pipeline.
"""

from __future__ import annotations

import logging
from dataclasses import dataclass, field, replace
from pathlib import Path
from typing import Sequence

from openhcs.constants.constants import Backend
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.steps.abstract import AbstractStep
from openhcs.core.config import GlobalPipelineConfig, MaterializationBackend
from openhcs.core.utils import WellFilterProcessor

from openhcs.core.vfs_protocol import FileManagerLike
from openhcs.core.dataset_sources.source import DatasetSource

logger = logging.getLogger(__name__)


@dataclass(frozen=True, slots=True)
class MaterializationFlagPlanner:
    """Admit source backend and persistence policy for one compilation submission."""

    pipeline_config: GlobalPipelineConfig
    microscope_handler: DatasetSource
    filemanager: FileManagerLike
    input_dir: Path
    available_axis_values: Sequence[str]
    _primary_backend: str | None = field(default=None, init=False, repr=False)
    _materialization_axes: frozenset[str] | None = field(init=False, repr=False)

    def __post_init__(self) -> None:
        path_config = self.pipeline_config.path_planning_config
        object.__setattr__(
            self, "available_axis_values", tuple(self.available_axis_values)
        )
        object.__setattr__(
            self,
            "_materialization_axes",
            (
                None
                if path_config.well_filter is None
                else frozenset(
                    WellFilterProcessor.resolve_filter_with_mode(
                        path_config.well_filter,
                        path_config.well_filter_mode,
                        [str(value) for value in self.available_axis_values],
                    )
                )
            ),
        )

    def resolve_backend(self, declaration: Backend | MaterializationBackend) -> str:
        """Resolve explicit declarations directly and admit AUTO once per submission."""
        if declaration.value != Backend.AUTO.value:
            return declaration.value
        if self._primary_backend is None:
            object.__setattr__(
                self,
                "_primary_backend",
                self.microscope_handler.get_primary_backend(
                    self.input_dir, self.filemanager
                ),
            )
        return self._primary_backend

    def prepare_pipeline_flags(
        self,
        context: ProcessingContext,
        pipeline_definition: Sequence[AbstractStep],
    ) -> None:
        """Derive axis-specific flags from admitted source and persistence policy."""
        vfs_config = self.pipeline_config.vfs_config
        step_plans = context.step_plans
        materializes_main_flow_axis = (
            self._materialization_axes is None
            or str(context.axis_id) in self._materialization_axes
        )
        last_image_materialization_step = self._last_image_materialization_step(
            step_plans,
            len(pipeline_definition),
        )

        for i, step in enumerate(pipeline_definition):
            step_plan = step_plans[i]
            step_plan.main_flow_axis_persistence_enabled = materializes_main_flow_axis
            if i == 0:
                step_plan.read_backend = self.resolve_backend(vfs_config.read_backend)
            elif step_plan.read_backend is None:
                from openhcs.core.steps.abstract import InputSource

                if step.processing_config.input_source == InputSource.PIPELINE_START:
                    if step_plans[0].input_conversion is not None:
                        step_plan.read_backend = Backend.ZARR.value
                        step_plan.input_dir = step_plans[0].input_conversion.output_dir
                    else:
                        step_plan.read_backend = step_plans[0].read_backend
                else:
                    step_plan.read_backend = Backend.MEMORY.value

            if materializes_main_flow_axis and (
                step_plan.zarr_config is not None
                or i == last_image_materialization_step
            ):
                step_plan.write_backend = self.resolve_backend(
                    vfs_config.materialization_backend,
                )
            else:
                step_plan.write_backend = Backend.MEMORY.value

            if step_plan.materialized_output is not None:
                step_plan.materialized_output = replace(
                    step_plan.materialized_output,
                    backend=self.resolve_backend(vfs_config.materialization_backend),
                )

        if not materializes_main_flow_axis:
            logger.info(
                "Path-planning filter keeps axis %s runtime-only; automatic "
                "main-flow output persistence is disabled for this axis.",
                context.axis_id,
            )

    @staticmethod
    def _last_image_materialization_step(step_plans, step_count: int) -> int | None:
        """Return the last step index whose outputs should seed the output plate."""
        for step_index in range(step_count - 1, -1, -1):
            if MaterializationFlagPlanner._step_materializes_images(
                step_plans[step_index]
            ):
                return step_index
        return None

    @staticmethod
    def _step_materializes_images(step_plan) -> bool:
        """Return whether automatic final materialization should flush images."""
        if not step_plan.artifact_outputs:
            return True
        return any(
            output.artifact_type.participates_in_main_flow_output
            and output.materialization is not None
            for output in step_plan.artifact_outputs.values()
        )
