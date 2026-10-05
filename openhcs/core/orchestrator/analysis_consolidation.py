"""Analysis result consolidation for completed compiled plate executions."""

from __future__ import annotations

import logging
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import TYPE_CHECKING

import pandas as pd

from openhcs.constants.constants import AllComponents
from openhcs.core.config import AnalysisConsolidationConfig, PlateMetadataConfig
from openhcs.core.context.processing_context import ProcessingContext
from openhcs.core.orchestrator.execution_result import (
    ExecutionResult,
    RuntimeExecutionObservation,
)
from openhcs.processing.backends.analysis.consolidate_analysis_results import (
    AnalysisSummaryWriter,
    RuntimeAnalysisTableOutput,
    analysis_file_path_is_included,
    consolidate_runtime_analysis_table_output_groups,
    consolidated_analysis_summary_csv,
)

logger = logging.getLogger(__name__)

if TYPE_CHECKING:
    from polystore.filemanager import FileManager
    from openhcs.core.compiled_step_plan import CompiledStepPlan
    from openhcs.core.steps.function_artifact_materialization import (
        MaterializedRuntimeArtifact,
        RuntimeArtifactMaterialization,
    )
    from openhcs.processing.materialization.core import Output


@dataclass(frozen=True, slots=True)
class RuntimeAnalysisSummaryDestination:
    """Compiled persistent destination shared by runtime analysis outputs."""

    backend: str
    images_dir: str


@dataclass(frozen=True, slots=True)
class RuntimeAnalysisDirectoryInputs:
    """One result directory's observed tables and compiled storage context."""

    outputs: tuple[RuntimeAnalysisTableOutput, ...]
    destination: RuntimeAnalysisSummaryDestination


@dataclass(frozen=True, slots=True)
class RuntimeAnalysisConsolidationInputs:
    """Execution-ledger tables and their compiled summary destination."""

    groups: Mapping[Path, RuntimeAnalysisDirectoryInputs]
    destination: RuntimeAnalysisSummaryDestination

    @property
    def outputs_by_directory(
        self,
    ) -> Mapping[Path, tuple[RuntimeAnalysisTableOutput, ...]]:
        return {directory: group.outputs for directory, group in self.groups.items()}

    @classmethod
    def from_saved_outputs(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
        saved: MaterializedRuntimeArtifact,
    ) -> RuntimeAnalysisConsolidationInputs | None:
        """Project the writer's actual saved CSV content without rendering again."""
        if not plan.runtime_artifact_materialization.has_persistent_target:
            return None
        backend = plan.runtime_artifact_materialization.require_persistent_backend()
        return cls._from_table_contents(
            context, plan, saved.materialization,
            (
                (Path(output.path), output.require_text_content())
                for output in saved.outputs_for_backend(backend)
                if analysis_file_path_is_included(
                    Path(output.path),
                    analysis_consolidation_config=context.analysis_consolidation_config,
                )
            ),
        )

    @classmethod
    def from_reused_outputs(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
        materialization: RuntimeArtifactMaterialization,
        outputs: tuple[Output, ...],
    ) -> RuntimeAnalysisConsolidationInputs | None:
        """Read exact historical CSV text for explicitly reused debug outputs."""
        if not plan.runtime_artifact_materialization.has_persistent_target:
            return None
        backend = plan.runtime_artifact_materialization.require_persistent_backend()
        return cls._from_table_contents(
            context, plan, materialization,
            (
                (Path(output.path), context.filemanager.load_text(output.path, backend))
                for output in outputs
                if analysis_file_path_is_included(
                    Path(output.path),
                    analysis_consolidation_config=context.analysis_consolidation_config,
                )
            ),
        )

    @classmethod
    def _from_table_contents(
        cls,
        context: ProcessingContext,
        plan: CompiledStepPlan,
        materialization: RuntimeArtifactMaterialization,
        contents: Iterable[tuple[Path, str]],
    ) -> RuntimeAnalysisConsolidationInputs | None:
        """Bind table identity and destinations from this one materialization."""
        if (
            not materialization.spec.participates_in_runtime_export_observation()
            or not context.analysis_consolidation_config.enabled
        ):
            return None
        backend = plan.runtime_artifact_materialization.require_persistent_backend()
        destination = RuntimeAnalysisSummaryDestination(
            backend=backend, images_dir=plan.artifact_images_dir,
        )
        output_groups: dict[
            tuple[Path, RuntimeAnalysisSummaryDestination], list[RuntimeAnalysisTableOutput]
        ] = {}
        for output_path, content in contents:
            output_groups.setdefault((output_path.parent, destination), []).append(
                runtime_analysis_table_output(
                    materialization,
                    output_path=output_path,
                    csv_content=content,
                    pipeline_position=plan.pipeline_position,
                )
            )
        return cls._from_groups(
            output_groups,
            {RuntimeAnalysisSummaryDestination(backend, str(plan.output_dir))},
        )

    @classmethod
    def combine(
        cls,
        inputs: Iterable[RuntimeAnalysisConsolidationInputs | None],
    ) -> RuntimeAnalysisConsolidationInputs | None:
        """Combine actual rendered projections without revisiting their payloads."""
        output_groups: dict[
            tuple[Path, RuntimeAnalysisSummaryDestination], list[RuntimeAnalysisTableOutput]
        ] = {}
        destinations: set[RuntimeAnalysisSummaryDestination] = set()
        seen_paths: set[tuple[str, Path]] = set()
        for item in inputs:
            if item is None:
                continue
            destinations.add(item.destination)
            for directory, group in item.groups.items():
                for output in group.outputs:
                    identity = (group.destination.backend, output.path)
                    if identity in seen_paths:
                        continue
                    seen_paths.add(identity)
                    output_groups.setdefault((directory, group.destination), []).append(output)
        return cls._from_groups(output_groups, destinations)

    @classmethod
    def from_observations(
        cls,
        compiled_contexts: Mapping[str, ProcessingContext],
        observations: tuple[RuntimeExecutionObservation, ...],
    ) -> RuntimeAnalysisConsolidationInputs | None:
        """Admit execution contexts and combine their actual rendered outputs."""
        inputs = []
        for observation in observations:
            for context_observation in observation.contexts:
                if context_observation.context_key not in compiled_contexts:
                    raise KeyError(
                        "Runtime observation references unknown compiled context "
                        f"{context_observation.context_key!r}."
                    )
                inputs.append(context_observation.analysis_inputs)
        return cls.combine(inputs)

    @classmethod
    def _from_groups(
        cls,
        output_groups: Mapping[
            tuple[Path, RuntimeAnalysisSummaryDestination], list[RuntimeAnalysisTableOutput]
        ],
        destinations: set[RuntimeAnalysisSummaryDestination],
    ) -> RuntimeAnalysisConsolidationInputs | None:
        """Admit the single compiled summary destination for projected tables."""
        if not output_groups:
            return None
        if len(destinations) != 1:
            raise RuntimeError(
                "Analysis outputs do not share one compiled main-flow summary destination: "
                f"{sorted(destinations, key=lambda value: (value.backend, value.images_dir))!r}."
            )
        return cls(
            groups={
                directory: RuntimeAnalysisDirectoryInputs(
                    outputs=tuple(outputs), destination=destination,
                )
                for (directory, destination), outputs in output_groups.items()
            },
            destination=next(iter(destinations)),
        )


@dataclass(frozen=True, slots=True)
class FileManagerAnalysisSummaryWriter(AnalysisSummaryWriter):
    """Persist summaries through the compiled PolyStore destination."""

    filemanager: FileManager
    destinations: Mapping[Path, RuntimeAnalysisSummaryDestination]

    def write(
        self,
        summary_df: pd.DataFrame,
        *,
        output_path: Path,
        results_dir: Path,
        analysis_consolidation_config: AnalysisConsolidationConfig,
        plate_metadata_config: PlateMetadataConfig,
    ) -> None:
        destination = self.destinations[results_dir]
        content = consolidated_analysis_summary_csv(
            summary_df,
            results_dir,
            analysis_consolidation_config,
            plate_metadata_config,
        )
        self.filemanager.ensure_directory(
            output_path.parent,
            destination.backend,
        )
        save_kwargs = self.filemanager.contextual_save_kwargs(
            destination.backend,
            images_dir=destination.images_dir,
        )
        self.filemanager.save(
            content,
            str(output_path),
            destination.backend,
            **save_kwargs,
        )


def consolidate_analysis_outputs(
    compiled_contexts: Mapping[str, ProcessingContext],
    execution_results: Mapping[str, ExecutionResult],
    *,
    plate_runtime_observation: RuntimeExecutionObservation,
) -> None:
    """Consolidate analysis tables materialized by this execution only."""

    first_context = next(iter(compiled_contexts.values()))
    analysis_consolidation_config = first_context.analysis_consolidation_config

    if not analysis_consolidation_config.enabled:
        logger.info("⏭️ CONSOLIDATION: Disabled")
        return

    runtime_observations = tuple(
        result.runtime_observation for result in execution_results.values()
    ) + (plate_runtime_observation,)
    consolidation_inputs = RuntimeAnalysisConsolidationInputs.from_observations(
        compiled_contexts,
        runtime_observations,
    )
    if consolidation_inputs is None:
        return

    if first_context.output_plate_root is None:
        raise ValueError(
            "Analysis consolidation requires the compiled output plate root."
        )
    output_plate_root = Path(first_context.output_plate_root)

    successful_dirs, failed_dirs = consolidate_runtime_analysis_table_output_groups(
        analysis_outputs_by_directory=consolidation_inputs.outputs_by_directory,
        plate_path=output_plate_root,
        analysis_consolidation_config=analysis_consolidation_config,
        plate_metadata_config=first_context.plate_metadata_config,
        summary_writer=FileManagerAnalysisSummaryWriter(
            filemanager=first_context.filemanager,
            destinations={
                **{
                    directory: group.destination
                    for directory, group in consolidation_inputs.groups.items()
                },
                output_plate_root: consolidation_inputs.destination,
            },
        ),
    )

    if failed_dirs:
        raise RuntimeError(
            "Analysis consolidation failed for execution-owned outputs: "
            f"{failed_dirs!r}."
        )
    logger.info(
        "CONSOLIDATION: %d directories consolidated",
        len(successful_dirs),
    )


def runtime_analysis_table_output(
    materialization: RuntimeArtifactMaterialization,
    *,
    output_path: Path,
    csv_content: str,
    pipeline_position: int,
) -> RuntimeAnalysisTableOutput:
    """Project table identity from the typed runtime address, never its filename."""

    scope = materialization.record.key.scope
    well_id = scope.value_text_for_component(AllComponents.WELL)
    if well_id is None:
        raise ValueError(
            "Analysis consolidation requires a well coordinate in the runtime "
            f"artifact scope for {materialization.output_plan.name!r}."
        )
    coordinate_segments = tuple(
        f"{component.value}-{value}"
        for component, value in scope.presentation_component_values
        if component is not AllComponents.WELL
    )
    analysis_type = "_".join(
        (
            *coordinate_segments,
            f"{materialization.output_plan.name}_step{pipeline_position}",
        )
    )
    return RuntimeAnalysisTableOutput(
        path=output_path,
        well_id=well_id,
        analysis_type=analysis_type,
        csv_content=csv_content,
    )
