"""Operations on the current dataset's pipeline."""

from __future__ import annotations

from openhcs.agent.dto.common import AgentError
from openhcs.agent.dto.session import (
    DatasetRequest,
    PipelineFileRequest,
    PipelineStepTargetsRequest,
    SessionOperationResult,
)
from openhcs.authoring.session.operations import (
    HeadlessOperation,
    RendererOperation,
    SessionOperation,
)


class InitializedDatasetOperation(SessionOperation):
    """Needs the request's dataset to be initialized."""

    selection_mode = "current"

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        if not request.scope_id:
            return AgentError(
                code="dataset_selection_required",
                message=f"{cls.label} needs a current dataset.",
            )
        if not session.is_initialized(request.scope_id):
            return AgentError(
                code="dataset_not_initialized",
                message=f"{cls.label} needs an initialized dataset.",
            )
        return None


class EditablePipelineOperation(InitializedDatasetOperation):
    """Also needs the dataset's definition not to be in preparation."""

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        if session.has_pending_definition_work(request.scope_id):
            return AgentError(
                code="dataset_definition_pending",
                message="The dataset is initializing or compiling.",
            )
        return None


class CurrentDatasetRequestMixin(SessionOperation):
    request = DatasetRequest

    @classmethod
    def request_for_selection(cls, session, scope_ids):
        return cls.request(scope_id=session.current_scope_id)


class SelectedStepsOperation(EditablePipelineOperation):
    request = PipelineStepTargetsRequest
    selection_mode = "selected"

    @classmethod
    def request_for_selection(cls, session, scope_ids):
        return cls.request(
            scope_id=session.current_scope_id,
            step_scope_ids=tuple(scope_ids),
        )

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        if not request.step_scope_ids:
            return AgentError(
                code="step_selection_required",
                message=f"{cls.label} needs selected steps.",
            )
        return None


class AddPipelineStep(CurrentDatasetRequestMixin, EditablePipelineOperation, RendererOperation):
    operation_id = "add_step"
    label = "Add"
    tooltip = "Add new pipeline step"
    description = "Opens the step editor for a new step."
    side_effects = ("opens_step_editor", "may_mutate_pipeline")
    confirmation_required = True


class DeletePipelineSteps(SelectedStepsOperation, HeadlessOperation):
    operation_id = "delete_steps"
    label = "Del"
    tooltip = "Delete selected steps"
    description = "Deletes steps from one dataset's pipeline."
    side_effects = ("mutates_pipeline",)

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.delete_steps(request.scope_id, request.step_scope_ids)
        return cls.completed(session, request.step_scope_ids)


class EditPipelineStep(SelectedStepsOperation, RendererOperation):
    operation_id = "edit_step"
    label = "Edit"
    tooltip = "Edit selected step"
    description = "Opens the step editor for the selected step."
    side_effects = ("opens_step_editor", "may_mutate_step")
    confirmation_required = True


class LoadExamplePipeline(
    CurrentDatasetRequestMixin, EditablePipelineOperation, HeadlessOperation
):
    operation_id = "load_example_pipeline"
    label = "Auto"
    tooltip = "Load the example pipeline (basic_pipeline.py)"
    description = "Replaces the dataset's pipeline with OpenHCS's example pipeline."
    side_effects = ("mutates_pipeline",)

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.load_example_pipeline(request.scope_id)
        return cls.completed(session, (request.scope_id,))


class LoadPipelineFile(HeadlessOperation):
    operation_id = "load_pipeline_file"
    label = "Load pipeline"
    tooltip = "Load the dataset's pipeline from a file"
    description = (
        "Replaces one dataset's pipeline with a pipeline file in any registered "
        "format (OpenHCS .py documents; CellProfiler .cppipe)."
    )
    request = PipelineFileRequest
    side_effects = ("mutates_pipeline",)

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        if request.scope_id not in session.dataset_scope_ids():
            return AgentError(
                code="unknown_dataset",
                message=f"Unknown dataset scope id: {request.scope_id}.",
            )
        return None

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.load_pipeline_file(request.scope_id, request.path)
        return cls.completed(session, (request.scope_id,))


class ShowPipelineCode(
    CurrentDatasetRequestMixin, InitializedDatasetOperation, RendererOperation
):
    operation_id = "show_pipeline_code"
    label = "Code"
    tooltip = "Edit pipeline as Python code"
    description = "Opens the pipeline code document."
    side_effects = ("opens_code_document_window",)
