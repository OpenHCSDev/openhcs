"""Typed pipeline authoring, planning and execution presentation owners."""

from __future__ import annotations

from inspect import getdoc

from openhcs.agent.capabilities import agent_capabilities
from openhcs.agent.dto.common import AgentError, RenderedSource
from openhcs.agent.dto.execution import (
    ArtifactInputPlanSummary,
    ArtifactMaterializationPlanSummary,
    ArtifactPlanInspection,
    CompiledStepPlanSummary,
    ExecutionJobRef,
    ExecutionJobIdentity,
    ExecutionJobStatus,
    OrchestratorSessionRef,
    SourceWorkspaceSummary,
)
from openhcs.agent.dto.pipeline import (
    FunctionStepSpec,
    PipelineRef,
    PipelineSpec,
    PipelineValidationResult,
)
from openhcs.mcp.dev_client_core import McpDevToolBatchResponse
from openhcs.mcp.dev_client_rendering import (
    CodeDocumentRenderOptions,
    McpDevOutputRenderOptions,
    McpDevOutputRenderer,
    diagnostic_lines,
)


def _sequence_text(values) -> str:
    return ",".join(str(value) for value in values)


def _mapping_text(values) -> str:
    return ", ".join(
        f"{key}={McpDevOutputRenderer.text(value)}" for key, value in values.items()
    )


class PipelineReferenceRenderer(McpDevOutputRenderer):
    output_contract = PipelineRef

    @classmethod
    def render_payload(
        cls, payload: PipelineRef, options: McpDevOutputRenderOptions
    ) -> str:
        return f"Pipeline: id={payload.pipeline_id} uri={payload.uri}"


class PipelineSpecRenderer(McpDevOutputRenderer):
    output_contract = PipelineSpec

    @classmethod
    def render_payload(
        cls, payload: PipelineSpec, options: McpDevOutputRenderOptions
    ) -> str:
        return "\n".join(
            (
                f"Pipeline: id={payload.pipeline_id} steps={len(payload.steps)}",
                *cls.step_lines(payload.steps),
            )
        )

    @staticmethod
    def step_lines(steps: tuple[FunctionStepSpec, ...]) -> list[str]:
        return [
            f"- {step.step_id}: name={McpDevOutputRenderer.quoted(step.name)} "
            f"enabled={step.enabled} functions={','.join(function.function_id for function in step.functions) or '<none>'}"
            for step in steps
        ]


class PipelineValidationRenderer(McpDevOutputRenderer):
    output_contract = PipelineValidationResult

    @classmethod
    def render_payload(
        cls, payload: PipelineValidationResult, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"Pipeline validation: id={payload.pipeline_ref.pipeline_id} valid={payload.valid}"
        ]
        return "\n".join(lines)


class PipelineSourceRenderer(McpDevOutputRenderer):
    output_contract = RenderedSource
    render_options_type = CodeDocumentRenderOptions

    @classmethod
    def render_payload(
        cls, payload: RenderedSource, options: CodeDocumentRenderOptions
    ) -> str:
        lines = [
            f"Source: title={McpDevOutputRenderer.quoted(payload.title)} bytes={len(payload.source)}"
        ]
        if options.include_source:
            lines.append(options.source_text(payload.source))
        return "\n".join(lines)


class PipelineDraftStepRenderer:
    """Composite presentation of the same decoded production authoring results."""

    @classmethod
    def render(cls, response, *, max_source_chars: int = 2_000) -> str:
        decoded = McpDevToolBatchResponse.for_rendering(response)
        created: PipelineRef | None = decoded.payload_for(
            agent_capabilities.create_pipeline
        )
        added: PipelineSpec | None = decoded.payload_for(
            agent_capabilities.add_function_step
        )
        validated: PipelineValidationResult | None = decoded.payload_for(
            agent_capabilities.validate_pipeline
        )
        source: RenderedSource | None = decoded.payload_for(
            agent_capabilities.render_pipeline_source
        )
        steps = () if added is None else added.steps
        lines = [
            f"Pipeline draft: id={McpDevOutputRenderer.text(None if created is None else created.pipeline_id)} "
            f"valid={'<not-run>' if validated is None else validated.valid} steps={len(steps)}"
        ]
        if created is not None:
            lines.append(f"Ref: uri={created.uri}")
        if validated is not None and validated.errors:
            lines.append("Validate errors:")
        lines.extend(
            diagnostic_lines(decoded.diagnostic_errors())
        )
        if validated is not None:
            if validated.warnings:
                lines.append("Validate warnings:")
                lines.extend(diagnostic_lines(validated.warnings))
            cls._append_repair_hints(lines, validated.errors, steps)
        if steps:
            lines.append("Steps:")
            lines.extend(PipelineSpecRenderer.step_lines(steps))
        if source is not None:
            lines.append(
                PipelineSourceRenderer.render_payload(
                    source, CodeDocumentRenderOptions(max_source_chars=max_source_chars)
                )
            )
        return "\n".join(lines)

    @classmethod
    def _append_repair_hints(
        cls,
        lines: list[str],
        errors: tuple[AgentError, ...],
        steps: tuple[FunctionStepSpec, ...],
    ) -> None:
        missing_kwargs = cls._missing_function_kwargs(errors)
        functions = tuple(function for step in steps for function in step.functions)
        if not missing_kwargs or not functions:
            return
        function_id = functions[0].function_id
        kwargs_shape = ", ".join(f'"{name}": <value>' for name in missing_kwargs)
        lines.append(f"Next: function {function_id}")
        lines.append(
            f"Retry shape: draft-pipeline-step {function_id} --kwargs '{{{kwargs_shape}}}'"
        )

    @classmethod
    def _missing_function_kwargs(
        cls, errors: tuple[AgentError, ...]
    ) -> tuple[str, ...]:
        for error in errors:
            if error.code == "missing_function_kwargs":
                for text in (error.hint, error.message):
                    if text is not None:
                        names = cls._parse_missing_kwargs(text)
                        if names:
                            return names
        return ()

    @staticmethod
    def _parse_missing_kwargs(text: str) -> tuple[str, ...]:
        marker = "required agent kwargs:"
        if marker in text:
            tail = text.split(marker, 1)[1]
        elif ": " in text:
            tail = text.rsplit(": ", 1)[1]
        else:
            return ()
        tail = tail.strip().rstrip(".")
        return tuple(
            name.strip().strip("`'") for name in tail.split(",") if name.strip()
        )


class PipelineArtifactPlanRenderer(McpDevOutputRenderer):
    output_contract = ArtifactPlanInspection

    @classmethod
    def render_payload(
        cls, payload: ArtifactPlanInspection, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [
            f"Artifact plan: plate={payload.plate_path} axes={payload.axis_count} steps={payload.step_count} progress_events={payload.progress_event_count}"
        ]
        if payload.axes:
            lines.append(f"Axes: {_sequence_text(payload.axes)}")
        if payload.axis_filter:
            lines.append(f"Axis filter: {_sequence_text(payload.axis_filter)}")
        lines.extend(cls._source_workspace_lines(payload.source_workspace))
        if payload.worker_assignments:
            lines.append(
                "Workers: "
                + ", ".join(
                    f"{worker}=[{_sequence_text(axes)}]"
                    for worker, axes in payload.worker_assignments.items()
                )
            )
        if payload.steps:
            lines.append("Steps:")
            lines.extend(cls._step_lines(payload.steps))
        return "\n".join(lines)

    @staticmethod
    def _source_workspace_lines(source_workspace: SourceWorkspaceSummary) -> list[str]:
        lines = [
            f"Source workspace (source-bound files): files={source_workspace.file_count} truncated={source_workspace.truncated_file_count}"
        ]
        if source_workspace.axis_file_counts:
            lines.append(
                f"  axis files: {_mapping_text(source_workspace.axis_file_counts)}"
            )
        if source_workspace.file_count == 0:
            lines.append(f"  note: {getdoc(SourceWorkspaceSummary)}")
        for record in source_workspace.files[:5]:
            line = f"  - {record.virtual_path}"
            if record.source_path and record.source_path != record.virtual_path:
                line += f" -> {record.source_path}"
            if record.source_metadata:
                line += f" components={_mapping_text(record.source_metadata)}"
            lines.append(line)
        if len(source_workspace.files) > 5:
            lines.append("  - ...")
        return lines

    @classmethod
    def _step_lines(cls, steps: tuple[CompiledStepPlanSummary, ...]) -> list[str]:
        lines: list[str] = []
        for step in steps:
            lines.append(
                f"- {step.step_index}: {step.step_name} axis={step.axis_id} groups={_sequence_text(step.execution_groups)}"
            )
            lines.extend(
                cls.optional_lines(
                    step.main_flow_axis_persistence_enabled,
                    lambda enabled: (
                        "  main-flow axis persistence: "
                        + ("enabled" if enabled else "runtime-only"),
                    ),
                )
            )
            lines.extend(
                cls.optional_lines(
                    step.main_flow_materialization,
                    lambda checkpoint: (
                        f"  main-flow checkpoint: backend={checkpoint.backend} output_dir={checkpoint.output_dir} sub_dir={checkpoint.sub_dir}",
                    ),
                )
            )
            for viewer in step.viewer_streaming:
                line = f"  viewer stream: viewer={viewer.viewer_type.value} config={viewer.config_key} backend={viewer.backend}"
                if viewer.effective_config:
                    line += f" effective={_mapping_text(viewer.effective_config)}"
                lines.append(line)
            for artifact in step.artifact_inputs:
                lines.append(cls._artifact_input_line(artifact))
            for artifact in step.artifact_outputs:
                lines.append(
                    f"  artifact {artifact.name}: kind={artifact.kind} path={artifact.path} groups={_sequence_text(artifact.group_keys)}"
                )
                lines.extend(
                    cls.optional_lines(
                        artifact.materialization, cls._materialization_lines
                    )
                )
            if step.truncated_artifact_input_count > 0:
                lines.append(
                    f"  artifact input ... truncated={step.truncated_artifact_input_count}"
                )
            if step.truncated_artifact_output_count > 0:
                lines.append(
                    f"  artifact ... truncated={step.truncated_artifact_output_count}"
                )
        return lines

    @classmethod
    def _artifact_input_line(cls, artifact: ArtifactInputPlanSummary) -> str:
        source_parts: list[str] = []
        source_parts.extend(
            cls.optional_lines(
                artifact.source_step_id, lambda value: (f"source_step={value}",)
            )
        )
        source_parts.extend(
            cls.optional_lines(
                artifact.source_step_scope_id, lambda value: (f"source_scope={value}",)
            )
        )
        suffix = f" {' '.join(source_parts)}" if source_parts else ""
        return f"  artifact input {artifact.name}: kind={artifact.kind} path={artifact.path} groups={_sequence_text(artifact.group_keys)}{suffix}"

    @classmethod
    def _materialization_lines(
        cls,
        materialization: ArtifactMaterializationPlanSummary,
    ) -> list[str]:
        mode = (
            "disabled"
            if materialization.disabled
            else "runtime-resolved"
            if materialization.runtime_resolved
            else "explicit"
        )
        parts = [mode, f"persistent={materialization.persistent_enabled}"]
        parts.extend(
            cls.optional_lines(
                materialization.persistent_backend, lambda value: (f"backend={value}",)
            )
        )
        parts.extend(
            cls.optional_lines(
                materialization.analysis_output_dir,
                lambda value: (f"analysis_dir={value}",),
            )
        )
        if materialization.filename_uses_source_identity:
            parts.append("source-identity-filenames")
        if materialization.runtime_metadata_can_refine_paths:
            parts.append("runtime-metadata-filenames")
        lines = [f"    materialization: {' '.join(parts)}"]
        for path in materialization.paths[:3]:
            lines.append(
                f"      candidates group={McpDevOutputRenderer.text(path.group_key)}: {', '.join(path.candidate_paths)}"
            )
        if len(materialization.paths) > 3:
            lines.append(
                f"      candidates ... truncated={len(materialization.paths) - 3}"
            )
        lines.extend(
            cls.optional_lines(
                materialization.note, lambda value: (f"      note: {value}",)
            )
        )
        return lines


class OrchestratorSessionReferenceRenderer(McpDevOutputRenderer):
    output_contract = OrchestratorSessionRef

    @classmethod
    def render_payload(
        cls, payload: OrchestratorSessionRef, options: McpDevOutputRenderOptions
    ) -> str:
        return f"Session: id={payload.session_id} uri={payload.uri}"


class ExecutionJobRenderer(McpDevOutputRenderer):
    """Presentation shared by the actual job-identity family, not sibling DTOs."""

    @staticmethod
    def identity_line(payload: ExecutionJobIdentity, status: str) -> str:
        return f"Job: id={payload.job_id} kind={payload.kind} status={status} server_execution={McpDevOutputRenderer.text(payload.server_execution_id)}"


class ExecutionJobReferenceRenderer(ExecutionJobRenderer):
    output_contract = ExecutionJobRef

    @classmethod
    def render_payload(
        cls, payload: ExecutionJobRef, options: McpDevOutputRenderOptions
    ) -> str:
        return cls.identity_line(payload, payload.status)


class ExecutionJobStatusRenderer(ExecutionJobRenderer):
    output_contract = ExecutionJobStatus

    @classmethod
    def render_payload(
        cls, payload: ExecutionJobStatus, options: McpDevOutputRenderOptions
    ) -> str:
        lines = [cls.identity_line(payload, payload.status)]
        if payload.response:
            lines.append(
                "Response: "
                + " ".join(f"{key}={value}" for key, value in payload.response.items())
            )
        lines.extend(
            cls.optional_lines(payload.progress, lambda value: (f"Progress: {value}",))
        )
        return "\n".join(lines)


class ExecuteSourceRenderer:
    @classmethod
    def render(cls, response) -> str:
        decoded = McpDevToolBatchResponse.for_rendering(response)
        session: OrchestratorSessionRef | None = decoded.payload_for(
            agent_capabilities.create_orchestrator_session_from_pipeline_source
        )
        job: ExecutionJobRef | ExecutionJobStatus | None = decoded.payload_for(
            agent_capabilities.submit_pipeline_execution
        )
        options = McpDevOutputRenderOptions()
        lines = ["Headless source execution:"]
        lines.append(
            "Session: <not created>"
            if session is None
            else OrchestratorSessionReferenceRenderer.render_payload(session, options)
        )
        lines.append(
            "Job: <not submitted>"
            if job is None
            else McpDevOutputRenderer.render_payload_value(job, options)
        )
        lines.extend(
            diagnostic_lines(decoded.diagnostic_errors())
        )
        return "\n".join(lines)
