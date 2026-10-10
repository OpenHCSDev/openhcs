"""Compile a pipeline document in-process and summarize its artifact plan."""

from __future__ import annotations

import logging
from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path

from zmqruntime.startup import EndpointStartupPhase, EndpointStartupStatus

from openhcs.agent.dto.common import SCHEMA_VERSION, AgentError, AgentWarning
from python_introspect import JsonObject, to_jsonable
from openhcs.agent.dto.execution import (
    ArtifactInputPlanSummary,
    ArtifactMaterializationPathSummary,
    ArtifactMaterializationPlanSummary,
    ArtifactPlanInspection,
    ArtifactPlanSummary,
    CompiledStepPlanSummary,
    MainFlowMaterializationPlanSummary,
    PipelineSourceArtifactPlanInspectionRequest,
    SourceWorkspaceFileRecord,
    SourceWorkspaceSummary,
    ViewerStreamingPlanSummary,
)
from openhcs.agent.exceptions import AgentFacingErrorMixin
from openhcs.agent.path_policy import AgentPathPolicy
from openhcs.agent.services.config_service import ConfigService
from openhcs.core.compiled_execution import CompiledExecutionBundle
from openhcs.core.compiled_step_plan import CompiledStepPlan
from openhcs.core.config import GlobalPipelineConfig
from openhcs.core.pipeline.path_planner import MissingArtifactInputError
from openhcs.core.pipeline_document import PipelineDocument, PipelineDocumentCodec
from openhcs.core.progress import ProgressEvent, ProgressQueue
from openhcs.core.source_workspace_projection import (
    VirtualWorkspacePathLookup,
    VirtualWorkspaceSourceProjection,
)
from openhcs.core.steps.function_artifact_materialization import (
    planned_materialization_preview,
)
from openhcs.core.virtual_workspace_metadata import METADATA_CONFIG
from openhcs.core.dataset_sources.exceptions import PixelSizeUnavailableError

MAX_INSPECTION_AXES = 8
MAX_INSPECTION_STEPS = 24
MAX_INSPECTION_ARTIFACT_INPUTS_PER_STEP = 16
MAX_INSPECTION_ARTIFACT_OUTPUTS_PER_STEP = 16
MAX_INSPECTION_SOURCE_WORKSPACE_FILES = 64
logger = logging.getLogger(__name__)


class AgentProgressQueue(ProgressQueue):
    def __init__(self) -> None:
        self.events: list[ProgressEvent] = []

    def put(self, event: dict) -> None:
        progress = ProgressEvent.from_dict(event)
        self.events.append(progress)
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            f"{progress.phase.value}: {progress.status.value}: "
            f"{progress.axis_id}: {progress.step_name}: "
            f"{progress.completed}/{progress.total}",
        ).publish()


@dataclass(frozen=True, slots=True)
class CompileInspectionInput:
    plate: Path
    pipeline_document: PipelineDocument
    axis_filter: tuple[str, ...]
    global_pipeline_config: GlobalPipelineConfig
    progress_queue: AgentProgressQueue


@dataclass(frozen=True, slots=True)
class CompileInspectionResult:
    """Compiler-owned bundle joined to its inspection-only source projection."""

    execution_bundle: CompiledExecutionBundle
    source_workspace_projection: VirtualWorkspaceSourceProjection


class CompileInspectionGatewayABC(ABC):
    def compile(self, request: CompileInspectionInput) -> CompileInspectionResult:
        """Publish the authoritative lifetime of any inspection compiler hook."""
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            "Preparing source inspection compiler",
        ).publish()
        try:
            result = self._compile(request)
        except Exception:
            EndpointStartupStatus(
                EndpointStartupPhase.FAILED, "Source inspection compiler failed",
            ).publish()
            raise
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            "Source inspection compilation and source projection completed",
        ).publish()
        return result

    @abstractmethod
    def _compile(self, request: CompileInspectionInput) -> CompileInspectionResult:
        raise NotImplementedError


class InProcessCompileInspectionGateway(CompileInspectionGatewayABC):
    def _compile(self, request: CompileInspectionInput) -> CompileInspectionResult:
        from objectstate.lazy_factory import ensure_global_config_context

        from openhcs.core.config import GlobalPipelineConfig
        from openhcs.core.orchestrator.orchestrator import PipelineOrchestrator
        from openhcs.core.progress import set_progress_queue

        ensure_global_config_context(
            GlobalPipelineConfig,
            request.global_pipeline_config,
        )
        orchestrator = PipelineOrchestrator(
            plate_path=request.plate,
            pipeline_config=request.pipeline_document.pipeline_config,
            progress_callback=None,
        )
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            "Initializing microscope source workspace and metadata",
        ).publish()
        orchestrator.initialize()
        EndpointStartupStatus(
            EndpointStartupPhase.PREPARING_CAPABILITIES,
            "Compiling declared pipeline artifacts on the original main thread",
        ).publish()
        set_progress_queue(request.progress_queue)
        try:
            execution_bundle = orchestrator.compile_pipelines(
                pipeline_definition=request.pipeline_document.pipeline_steps,
                well_filter=list(request.axis_filter) or None,
                is_zmq_execution=True,
            )
            EndpointStartupStatus(
                EndpointStartupPhase.PREPARING_CAPABILITIES,
                "Projecting compiled source workspace",
            ).publish()
            return CompileInspectionResult(
                execution_bundle=execution_bundle,
                source_workspace_projection=(
                    orchestrator.source_workspace_projection()
                ),
            )
        finally:
            set_progress_queue(None)


@dataclass(frozen=True, slots=True)
class GlobalConfigSelection:
    config_id: str | None

    def resolve(self, config_service: ConfigService) -> GlobalPipelineConfig:
        if self.config_id is None:
            return GlobalPipelineConfig()
        config = config_service.resolve_ref(self.config_id)
        if not isinstance(config, GlobalPipelineConfig):
            raise TypeError("global_config_id must resolve to GlobalPipelineConfig")
        return config


class ArtifactPlanInspectionService:
    """Compile a pipeline document against a dataset and summarize the plan."""

    def __init__(
        self,
        *,
        path_policy: AgentPathPolicy,
        config_service: ConfigService,
        compile_inspection_gateway: CompileInspectionGatewayABC | None = None,
    ) -> None:
        self._path_policy = path_policy
        self._config_service = config_service
        self._compile_inspection_gateway = (
            compile_inspection_gateway or InProcessCompileInspectionGateway()
        )

    def inspect(
        self,
        request: PipelineSourceArtifactPlanInspectionRequest,
    ) -> ArtifactPlanInspection:
        progress_queue = AgentProgressQueue()
        plate = self._path_policy.assert_readable(request.plate_path)
        axis_filter = request.axis_filter
        # Initialization persists workspace metadata even when nothing executes;
        # admit that write before the compiler creates metadata or locks.
        self._path_policy.assert_writable(plate)
        for destination in METADATA_CONFIG.managed_paths(plate):
            self._path_policy.assert_writable(destination)
            # Atomic replacement stages temporary files next to the destination.
            self._path_policy.assert_writable(destination.parent)
        metadata_path = METADATA_CONFIG.metadata_path(plate)
        metadata_existed_before = metadata_path.exists()

        def failed(errors: tuple[AgentError, ...]) -> ArtifactPlanInspection:
            return ArtifactPlanInspection(
                schema_version=SCHEMA_VERSION,
                plate_path=str(plate),
                axis_filter=axis_filter,
                progress_event_count=len(progress_queue.events),
                warnings=_compile_inspection_workspace_warnings(
                    metadata_path, metadata_existed_before
                ),
                errors=errors,
            )

        try:
            EndpointStartupStatus(
                EndpointStartupPhase.PREPARING_CAPABILITIES,
                "Resolving pipeline source document",
            ).publish()
            document = PipelineDocumentCodec.from_source(request.pipeline_source)
        except Exception as exc:
            return failed((_pipeline_document_error(exc),))
        try:
            compilation = self._compile_inspection_gateway.compile(
                CompileInspectionInput(
                    plate=plate,
                    pipeline_document=document,
                    axis_filter=axis_filter,
                    global_pipeline_config=GlobalConfigSelection(
                        request.global_config_id
                    ).resolve(self._config_service),
                    progress_queue=progress_queue,
                )
            )
        except Exception as exc:
            return failed((_compile_inspection_error(exc),))
        return artifact_plan_inspection_from_compilation(
            plate_path=str(plate),
            axis_filter=axis_filter,
            compilation=compilation,
            progress_event_count=len(progress_queue.events),
            warnings=_compile_inspection_workspace_warnings(
                metadata_path, metadata_existed_before
            ),
        )


def artifact_plan_inspection_from_compilation(
    *,
    plate_path: str,
    axis_filter: tuple[str, ...],
    compilation: CompileInspectionResult,
    progress_event_count: int,
    warnings: tuple[AgentWarning, ...] = (),
) -> ArtifactPlanInspection:
    execution_bundle = compilation.execution_bundle
    compiled_contexts = dict(execution_bundle.runtime_contexts)
    axes = tuple(sorted(str(axis_id) for axis_id in compiled_contexts))
    source_workspace_axes = axes or axis_filter
    step_summaries = tuple(
        _bounded_step_summaries(compiled_contexts, axes[:MAX_INSPECTION_AXES])
    )
    return ArtifactPlanInspection(
        schema_version=SCHEMA_VERSION,
        plate_path=plate_path,
        axis_filter=axis_filter,
        axis_count=len(axes),
        axes=axes[:MAX_INSPECTION_AXES],
        truncated_axis_count=max(0, len(axes) - MAX_INSPECTION_AXES),
        step_count=sum(
            len(context.step_plans) for context in compiled_contexts.values()
        ),
        steps=step_summaries,
        truncated_step_count=max(
            0,
            sum(len(context.step_plans) for context in compiled_contexts.values())
            - len(step_summaries),
        ),
        worker_assignments={
            str(worker): [str(axis_id) for axis_id in axis_ids]
            for worker, axis_ids in execution_bundle.worker_assignments.items()
        },
        source_workspace=_source_workspace_summary(
            compilation.source_workspace_projection,
            axes=source_workspace_axes,
        ),
        progress_event_count=progress_event_count,
        warnings=warnings,
    )


def _compile_inspection_workspace_warnings(
    metadata_path: Path,
    existed_before: bool,
) -> tuple[AgentWarning, ...]:
    if existed_before or not metadata_path.exists():
        return ()
    return (
        AgentWarning(
            code="compile_inspection_initialized_workspace",
            message=(
                "Compile inspection initialized OpenHCS workspace metadata at "
                f"{metadata_path}."
            ),
            hint=(
                "Raw microscope layouts can require virtual workspace metadata "
                "before compilation or execution. Run openhcs_inspect_plate_path "
                "first to preview whether workspace preparation is required."
            ),
        ),
    )


def _compile_inspection_error(exception: Exception) -> AgentError:
    if isinstance(exception, AgentFacingErrorMixin):
        return exception.to_agent_error()
    if isinstance(exception, MissingArtifactInputError):
        return AgentError.from_exception(
            "compile_inspection_missing_artifact_input",
            exception,
            hint=(
                f"Step {exception.step_id} requires artifact input "
                f"{exception.artifact_key!r}. Add an earlier FunctionStep that "
                "declares that artifact output, configure source bindings that "
                "provide it from the plate workspace, or inspect "
                "openhcs_function_patterns and "
                "openhcs_architecture_quick_start#compile-before-execution before "
                "retrying artifact-plan."
            ),
        )
    if isinstance(exception, PixelSizeUnavailableError):
        return AgentError.from_exception(
            "compile_inspection_pixel_size_unavailable",
            exception,
            hint=(
                "Run openhcs_inspect_plate_path first and check its warnings. "
                "Use the true microscope plate root, initialize the workspace "
                "when required, or provide microscope metadata that includes "
                "physical pixel size before retrying compile inspection."
            ),
            path=str(exception.image_path),
        )
    return AgentError.from_exception(
        "compile_inspection_failed",
        exception,
        hint=(
            "Check plate inspection, the embedded pipeline config, and the external "
            "global config before retrying compile inspection."
        ),
    )


def _pipeline_document_error(exception: Exception) -> AgentError:
    code = (
        "pipeline_source_syntax_error"
        if isinstance(exception, SyntaxError)
        else "pipeline_source_invalid_document"
    )
    return AgentError.from_exception(
        code,
        exception,
        hint=(
            "Provide a pipeline document defining a typed pipeline_steps "
            "assignment. Omit pipeline_config only to use PipelineConfig(), or "
            "render an MCP draft with openhcs_render_pipeline_source."
        ),
    )


def _bounded_step_summaries(compiled_contexts, axes: tuple[str, ...]):
    emitted = 0
    for axis_id in axes:
        context = compiled_contexts[axis_id]
        for step_plan in context.step_plans.values():
            if emitted >= MAX_INSPECTION_STEPS:
                return
            emitted += 1
            artifact_inputs = tuple(
                _artifact_input_summary(plan)
                for _input_key, plan in tuple(step_plan.artifact_inputs.items())[
                    :MAX_INSPECTION_ARTIFACT_INPUTS_PER_STEP
                ]
            )
            artifact_outputs = tuple(
                _artifact_summary(context, step_plan, plan.name, plan)
                for plan in tuple(step_plan.artifact_outputs.values())[
                    :MAX_INSPECTION_ARTIFACT_OUTPUTS_PER_STEP
                ]
            )
            yield CompiledStepPlanSummary(
                step_index=int(step_plan.step_index),
                step_name=str(step_plan.step_name),
                axis_id=str(step_plan.axis_id),
                output_dir=_optional_path_text(step_plan.output_dir),
                main_flow_axis_persistence_enabled=(
                    step_plan.main_flow_axis_persistence_enabled
                ),
                execution_groups=step_plan.execution_group_scope.keys,
                main_flow_materialization=(
                    _main_flow_materialization_summary(step_plan)
                ),
                viewer_streaming=_viewer_streaming_summaries(step_plan),
                artifact_inputs=artifact_inputs,
                artifact_outputs=artifact_outputs,
                truncated_artifact_input_count=max(
                    0,
                    len(step_plan.artifact_inputs)
                    - MAX_INSPECTION_ARTIFACT_INPUTS_PER_STEP,
                ),
                truncated_artifact_output_count=max(
                    0,
                    len(step_plan.artifact_outputs)
                    - MAX_INSPECTION_ARTIFACT_OUTPUTS_PER_STEP,
                ),
            )


def _main_flow_materialization_summary(
    step_plan: CompiledStepPlan,
) -> MainFlowMaterializationPlanSummary | None:
    plan = step_plan.materialized_output
    if plan is None:
        return None
    return MainFlowMaterializationPlanSummary(
        output_dir=str(plan.output_dir),
        backend=str(plan.backend),
        plate_root=str(plan.plate_root),
        sub_dir=str(plan.sub_dir),
        analysis_results_dir=(
            None
            if plan.analysis_results_dir is None
            else str(plan.analysis_results_dir)
        ),
    )


def _viewer_streaming_summaries(
    step_plan: CompiledStepPlan,
) -> tuple[ViewerStreamingPlanSummary, ...]:
    summaries = []
    for config_key, config in step_plan.streaming_configs.items():
        effective_config = to_jsonable(config)
        if not isinstance(effective_config, dict):
            raise TypeError(
                "Compiled streaming config projection must be a JSON object; "
                f"got {type(effective_config).__name__}."
            )
        summaries.append(
            ViewerStreamingPlanSummary(
                config_key=str(config_key),
                viewer_type=config.viewer_family.viewer_type(),
                backend=str(config.viewer_family.backend.value),
                effective_config=effective_config,
            )
        )
    return tuple(summaries)


def _artifact_input_summary(plan) -> ArtifactInputPlanSummary:
    return ArtifactInputPlanSummary(
        name=str(plan.name),
        kind=str(plan.artifact_type.value),
        path=str(plan.path),
        group_keys=tuple(plan.group_keys),
        paths_by_group=_artifact_paths_by_group(plan),
        source_step_id=plan.source_step_id,
        source_step_scope_id=plan.source_step_scope_id,
    )


def _artifact_summary(
    context,
    step_plan: CompiledStepPlan,
    output_key: str,
    plan,
) -> ArtifactPlanSummary:
    return ArtifactPlanSummary(
        name=str(plan.name),
        kind=str(plan.artifact_type.value),
        path=str(plan.path),
        group_keys=tuple(plan.group_keys),
        paths_by_group=_artifact_paths_by_group(plan),
        materialization=_artifact_materialization_summary(
            context,
            step_plan,
            output_key,
            plan,
        ),
    )


def _artifact_paths_by_group(plan) -> tuple[JsonObject, ...]:
    if plan.paths_by_group is None:
        return ()
    return tuple(
        {"group_key": group_key, "path": path}
        for group_key, path in plan.paths_by_group.items()
    )


def _artifact_materialization_summary(
    context,
    step_plan: CompiledStepPlan,
    output_key: str,
    output_plan,
) -> ArtifactMaterializationPlanSummary | None:
    persistent_plan = step_plan.runtime_artifact_materialization
    if output_plan.materialization is None:
        return None

    step_plan.require_function_execution_ready()

    preview = planned_materialization_preview(
        context=context,
        plan=step_plan,
        output_key=output_key,
        output_plan=output_plan,
    )
    paths = ()
    filename_uses_source_identity = (
        output_plan.materialization_uses_source_identity_filename()
    )
    runtime_metadata_can_refine_paths = False
    if preview is not None:
        paths = tuple(
            ArtifactMaterializationPathSummary(
                group_key=path.group_key,
                shared_output_stem=path.shared_output_stem,
                candidate_paths=path.candidate_paths,
            )
            for path in preview.paths
        )
        filename_uses_source_identity = preview.filename_uses_source_identity
        runtime_metadata_can_refine_paths = preview.runtime_metadata_can_refine_paths

    note = None
    if runtime_metadata_can_refine_paths:
        note = "Runtime payload metadata can split or refine candidate filenames."

    return ArtifactMaterializationPlanSummary(
        persistent_enabled=persistent_plan.persistent_enabled,
        persistent_backend=persistent_plan.persistent_backend,
        analysis_output_dir=str(step_plan.artifact_analysis_output_dir),
        paths=paths,
        runtime_resolved=False,
        filename_uses_source_identity=filename_uses_source_identity,
        runtime_metadata_can_refine_paths=runtime_metadata_can_refine_paths,
        note=note,
    )


def _source_workspace_summary(
    projection,
    *,
    axes: tuple[str, ...],
) -> SourceWorkspaceSummary:
    if not isinstance(projection, VirtualWorkspaceSourceProjection):
        return SourceWorkspaceSummary()

    full_virtual_paths = projection.pipeline_start_files()
    records = tuple(
        _source_workspace_record(projection, full_virtual_path)
        for full_virtual_path in full_virtual_paths[
            :MAX_INSPECTION_SOURCE_WORKSPACE_FILES
        ]
    )
    return SourceWorkspaceSummary(
        file_count=len(full_virtual_paths),
        files=records,
        truncated_file_count=max(0, len(full_virtual_paths) - len(records)),
        axis_file_counts={
            axis: len(projection.pipeline_start_files(axis_id=axis))
            for axis in axes[:MAX_INSPECTION_AXES]
        },
    )


def _source_workspace_record(
    projection: VirtualWorkspaceSourceProjection,
    full_virtual_path: str,
) -> SourceWorkspaceFileRecord:
    virtual_path = _relative_virtual_path(projection, full_virtual_path)
    lookup = VirtualWorkspacePathLookup.from_paths(virtual_path, full_virtual_path)
    metadata = projection.source_metadata_for(lookup)
    source_metadata = {} if metadata is None else to_jsonable(metadata)
    if not isinstance(source_metadata, dict):
        source_metadata = {}
    return SourceWorkspaceFileRecord(
        virtual_path=virtual_path,
        full_virtual_path=full_virtual_path,
        source_path=projection.source_path_for(lookup),
        source_metadata=source_metadata,
    )


def _relative_virtual_path(
    projection: VirtualWorkspaceSourceProjection,
    full_virtual_path: str,
) -> str:
    if projection.workspace_root is None:
        return full_virtual_path
    try:
        return str(Path(full_virtual_path).relative_to(projection.workspace_root))
    except ValueError:
        return full_virtual_path


def _optional_path_text(path: Path | None) -> str | None:
    if path is None:
        return None
    return str(path)
