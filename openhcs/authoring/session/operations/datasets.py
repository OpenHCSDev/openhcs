"""Operations on the session's datasets: add, delete, initialize, compile, run."""

from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING, ClassVar

from zmqruntime.startup import EndpointStartupPresentationTarget

from openhcs.agent.dto.common import AgentError
from openhcs.agent.dto.session import (
    DatasetPipelineSourceRequest,
    DatasetRootsRequest,
    DatasetRunRequest,
    DatasetTargetsRequest,
    NoArgumentsRequest,
    SessionOperationResult,
    StopExecutionRequest,
)
from openhcs.authoring.session.operations import (
    HeadlessOperation,
    RendererOperation,
    SessionOperation,
)

if TYPE_CHECKING:
    pass


class PromptedOperation(SessionOperation):
    """A renderer asks its user for this operation's request (a dialog)."""


class DatasetTargetsOperation(SessionOperation):
    """An operation on the dataset rows a request names."""

    request = DatasetTargetsRequest

    @classmethod
    def request_for_selection(cls, session, scope_ids):
        return cls.request(scope_ids=tuple(scope_ids))

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        if not request.scope_ids:
            return AgentError(
                code="dataset_selection_required",
                message=f"{cls.label} needs at least one dataset.",
                hint="Select datasets, or pass scope_ids from the dataset list view.",
            )
        unknown = sorted(set(request.scope_ids) - set(session.dataset_scope_ids()))
        if unknown:
            return AgentError(
                code="unknown_dataset",
                message=f"Unknown dataset scope ids: {', '.join(unknown)}.",
            )
        return None


class IdleTargetsOperation(DatasetTargetsOperation):
    """Targets must have no initialization, compilation or execution running."""

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        busy = [s for s in request.scope_ids if session.has_active_work(s)]
        if busy:
            return AgentError(
                code="dataset_busy",
                message=(
                    f"{cls.label} is unavailable while these datasets have active "
                    f"work: {', '.join(busy)}."
                ),
            )
        return None


class InitializedTargetsOperation(DatasetTargetsOperation):
    """Every target must have finished initialization."""

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        uninitialized = [s for s in request.scope_ids if not session.is_initialized(s)]
        if uninitialized:
            return AgentError(
                code="dataset_not_initialized",
                message=(
                    f"{cls.label} needs initialized datasets; initialize "
                    f"{', '.join(uninitialized)} first."
                ),
                hint=f"Next: {InitializeDatasets.operation_id}.",
            )
        return None


class DatasetWorkflowOperation(SessionOperation):
    """One step of the dataset workflow (initialize, compile, run)."""

    workflow_name: ClassVar[str]


class AddDatasets(PromptedOperation, HeadlessOperation):
    operation_id = "add_datasets"
    label = "Add"
    tooltip = "Add dataset directories"
    description = (
        "Adds dataset root directories to the session. A root may become several "
        "rows, for example one per CellProfiler pipeline file it contains."
    )
    request = DatasetRootsRequest
    side_effects = ("mutates_dataset_list",)

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        missing = [root for root in request.roots if not Path(root).exists()]
        if missing:
            return AgentError(
                code="dataset_root_missing",
                message=f"Dataset roots do not exist: {', '.join(missing)}.",
            )
        return None

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        return cls.completed(session, session.add_dataset_roots(request.roots))


class DeleteDatasets(IdleTargetsOperation, HeadlessOperation):
    operation_id = "delete_datasets"
    label = "Del"
    tooltip = "Delete selected datasets"
    description = "Removes datasets and their configuration and pipeline from the session."
    side_effects = ("mutates_dataset_list",)

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.delete_datasets(request.scope_ids)
        return cls.completed(session, request.scope_ids)


class EditDatasetConfig(InitializedTargetsOperation, RendererOperation):
    operation_id = "edit_dataset_config"
    label = "Edit"
    tooltip = "Edit dataset configuration"
    description = "Opens the configuration window of the selected datasets."
    side_effects = ("opens_config_window", "may_mutate_dataset_config")
    confirmation_required = True

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        pending = [s for s in request.scope_ids if session.has_pending_definition_work(s)]
        if pending:
            return AgentError(
                code="dataset_definition_pending",
                message=f"Configuration is locked while {', '.join(pending)} prepares.",
            )
        return None


class InitializeDatasets(IdleTargetsOperation, DatasetWorkflowOperation, HeadlessOperation):
    operation_id = "initialize_datasets"
    workflow_name = "INIT"
    label = "Init"
    tooltip = "Initialize selected datasets"
    description = (
        "Scans each dataset's source metadata (and prepares any input workspace "
        "its scope kind declares). Initialization writes dataset metadata."
    )
    side_effects = ("writes_dataset_metadata",)

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.start(session.initialize_datasets, tuple(request.scope_ids))
        return cls.accepted(session, request.scope_ids)


class _CompileSlot(EndpointStartupPresentationTarget):
    """Which operation the compile button runs, from the endpoint's phase."""

    operation: type[SessionOperation]

    def present_connected(self, message: str) -> None:
        self.operation = CompileDatasets

    def present_disconnected(self, message: str) -> None:
        self.operation = ConnectServer

    def present_checking(self, message: str) -> None:
        self.operation = WaitForServer

    present_warning = present_checking


class CompileDatasets(
    InitializedTargetsOperation,
    IdleTargetsOperation,
    DatasetWorkflowOperation,
    HeadlessOperation,
):
    operation_id = "compile_datasets"
    workflow_name = "COMPILE"
    label = "Compile"
    tooltip = "Compile dataset pipelines"
    description = (
        "Compiles each dataset's pipeline on the execution server (connecting or "
        "starting it as needed)."
    )
    side_effects = ("submits_compile_jobs",)

    @classmethod
    def resolved(cls, session) -> type[SessionOperation]:
        slot = _CompileSlot()
        status = session.endpoint_status()
        status.phase.present(slot, status.message)
        return slot.operation

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        empty = [s for s in request.scope_ids if not session.pipeline_steps(s)]
        if empty:
            return AgentError(
                code="empty_pipeline_definition",
                message=f"These datasets have no pipeline steps: {', '.join(empty)}.",
                hint=f"Set a pipeline with {SetDatasetPipeline.operation_id} first.",
            )
        return None

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.start(session.compile_datasets, tuple(request.scope_ids))
        return cls.accepted(session, request.scope_ids)


class ConnectServer(HeadlessOperation):
    operation_id = "connect_server"
    label = "Connect"
    tooltip = "Connect to the execution server, starting it if needed"
    description = "Connects the session to its execution server, starting one if needed."
    side_effects = ("connects_or_starts_execution_server",)

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.start(session.ensure_server)
        return cls.accepted(session)


class WaitForServer(SessionOperation):
    operation_id = "wait_for_server"
    label = "Connecting…"
    tooltip = "Waiting for the execution server to become ready"
    description = "Shown while the execution server starts; it does nothing."
    confirmation_required = False

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        return AgentError(
            code="execution_server_starting",
            message="The execution server is starting.",
        )

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        raise AssertionError("WaitForServer is never available.")


class RunDatasets(DatasetTargetsOperation, DatasetWorkflowOperation, HeadlessOperation):
    operation_id = "run_datasets"
    workflow_name = "RUN"
    label = "Run"
    tooltip = "Run or stop dataset execution"
    description = (
        "Compiles, then executes the datasets as one batch on the execution "
        "server. Follow progress through the session events."
    )
    request = DatasetRunRequest
    side_effects = ("submits_execution_jobs",)

    @classmethod
    def resolved(cls, session) -> type[SessionOperation]:
        return StopExecution if session.execution_state.busy else cls

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        error = super().available(session, request)
        if error is not None:
            return error
        if session.execution_state.busy:
            return AgentError(
                code="execution_batch_active",
                message="An execution batch is already running.",
            )
        not_compiled = [s for s in request.scope_ids if s not in session.compiled]
        if not_compiled:
            return AgentError(
                code="dataset_not_compiled",
                message=f"Compile first: {', '.join(not_compiled)}.",
                hint=f"Next: {CompileDatasets.operation_id}.",
            )
        if not session.endpoint_status().phase.accepts_requests:
            return AgentError(
                code="execution_server_unavailable",
                message="The execution server is not accepting requests.",
            )
        return None

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.start(
            session.run_datasets,
            tuple(request.scope_ids),
            auxiliary_params=session.observation_export_params(
                request.runtime_observation_export_path,
                request.runtime_observation_export_scope,
            ),
        )
        return cls.accepted(session, request.scope_ids)


class StopExecution(HeadlessOperation):
    operation_id = "stop_execution"
    label = "Stop"
    tooltip = "Stop the running batch; a second stop kills the server"
    description = (
        "Stops the running batch by shutting the execution server down "
        "gracefully; force kills it."
    )
    request = StopExecutionRequest
    side_effects = ("stops_execution_server",)

    @classmethod
    def request_for_selection(cls, session, scope_ids):
        return cls.request()

    @classmethod
    def button_label(cls, session) -> str:
        return session.execution_state.run_button_text

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        state = session.execution_state
        if not state.busy:
            return AgentError(code="no_execution_running", message="Nothing is running.")
        if not state.run_button_enabled(True):
            return AgentError(
                code="execution_stopping",
                message="The batch is already stopping.",
            )
        return None

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.stop_execution(True if request.force else None)
        return cls.accepted(session)


class SetDatasetPipeline(HeadlessOperation):
    operation_id = "set_dataset_pipeline"
    label = "Set pipeline"
    tooltip = "Replace the dataset's pipeline"
    description = (
        "Replaces one dataset's pipeline steps and PipelineConfig with a complete "
        "pycodified PipelineDocument source (from render-pipeline-source)."
    )
    request = DatasetPipelineSourceRequest
    side_effects = ("mutates_dataset_pipeline",)

    @classmethod
    def available(cls, session, request) -> AgentError | None:
        if request.scope_id not in session.dataset_scope_ids():
            return AgentError(
                code="unknown_dataset",
                message=f"Unknown dataset scope id: {request.scope_id}.",
            )
        if session.has_pending_definition_work(request.scope_id):
            return AgentError(
                code="dataset_definition_pending",
                message="The dataset is initializing or compiling.",
            )
        return None

    @classmethod
    def run(cls, session, request) -> SessionOperationResult:
        session.set_pipeline_source(request.scope_id, request.pipeline_source)
        return cls.completed(session, (request.scope_id,))


class ShowDatasetCode(RendererOperation):
    operation_id = "show_dataset_code"
    label = "Code"
    tooltip = "Edit the selected datasets as Python code"
    description = "Opens the dataset code document."
    side_effects = ("opens_code_document_window",)
    request = DatasetTargetsRequest

    @classmethod
    def request_for_selection(cls, session, scope_ids):
        return cls.request(scope_ids=tuple(scope_ids))


class ShowLiveResults(RendererOperation):
    operation_id = "show_live_results"
    label = "Results"
    tooltip = "View live measurement results"
    description = "Opens the live measurement results window."
    side_effects = ("opens_results_window",)
    request = NoArgumentsRequest


class ShowDatasetImages(InitializedTargetsOperation, RendererOperation):
    operation_id = "show_dataset_images"
    label = "Viewer"
    tooltip = "Browse dataset images and metadata"
    description = "Opens the image and metadata browser of the selected datasets."
    side_effects = ("opens_dataset_viewer_window",)

