"""The OpenHCS UI-bridge state surfaces: datasets, pipeline editor, debug session, live measurements."""

from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from python_introspect import (
    JsonObject,
)
import openhcs.agent.ui_bridge_application  # noqa: F401  (declares the OpenHCS bridge application)
from openhcs.agent.dto.session import DatasetRowState, PipelineStepState
from formbridge.contracts import (
    AGENT_PARAMETER_DESCRIPTION_METADATA_KEY,
    AGENT_PARAMETER_PRODUCER_OUTPUT_CONTRACT_METADATA_KEY,
    AgentCliRequest,
    AgentError,
    AgentWarning,
)
from openhcs.authoring.session.operations import SessionOperation
from openhcs.authoring.session.operations.datasets import DatasetWorkflowOperation
from openhcs.agent.ui_bridge_identities import DatasetListStateSurfaceIdentity
from formbridge.selection import (
    SelectedScopeIdsArgument,
    SelectedScopeIdsCarrier,
)
from formbridge.bridge.dto import (
    UiActionCatalog,
    UiActionInvokeResult,
    UiBridgeConfirmationRequirement,
    UiBridgeConfirmationRequirementCarrier,
    UiCodeDocumentCurrentRevision,
    UiCurrentSnapshotState,
    UiMutationRequestToken,
    UiMutationRequestTokenCarrier,
    UiStateSurfaceEnvelope,
)
from openhcs.core.progress.live_measurements import LiveMeasurementTablePreview


def _dataset_workflow_enum() -> type[Enum]:
    """The dataset workflow operations, as a wire enum of operation ids."""
    members = {
        operation.workflow_name: operation.operation_id
        for operation in SessionOperation.all()
        if issubclass(operation, DatasetWorkflowOperation)
    }
    return Enum("UiSelectedPlateWorkflowKind", members, type=str)


UiSelectedPlateWorkflowKind = _dataset_workflow_enum()


@dataclass(frozen=True, slots=True)
class UiPlateManagerState(
    UiStateSurfaceEnvelope,
    UiCodeDocumentCurrentRevision,
    UiCurrentSnapshotState,
    SelectedScopeIdsCarrier,
):
    object_state_token: int
    manager_execution_state: str
    rows: tuple[DatasetRowState, ...]


@dataclass(frozen=True, slots=True)
class UiLiveMeasurementEntryState:
    """One retained progress event paired with its authoritative table preview."""

    sequence_id: int
    execution_id: str
    subject_id: str
    axis_id: str
    step_name: str
    preview: LiveMeasurementTablePreview
    truncated_preview_group: bool


@dataclass(frozen=True, slots=True)
class UiLiveMeasurementsState(
    UiStateSurfaceEnvelope,
    UiCodeDocumentCurrentRevision,
    UiCurrentSnapshotState,
    SelectedScopeIdsCarrier,
):
    """Bounded live measurement tables retained by the running Plate Manager."""

    object_state_token: int
    retained_entry_count: int
    visible_entry_count: int
    total_row_count: int
    latest_sequence_id: int | None
    entries: tuple[UiLiveMeasurementEntryState, ...]


@dataclass(frozen=True, slots=True)
class UiPipelineEditorState(
    UiStateSurfaceEnvelope,
    UiCodeDocumentCurrentRevision,
    UiCurrentSnapshotState,
    SelectedScopeIdsCarrier,
):
    object_state_token: int
    current_plate_scope_id: str | None
    pipeline_scope_id: str | None
    steps: tuple[PipelineStepState, ...]


@dataclass(frozen=True, slots=True)
class UiDebugActionState(SelectedScopeIdsCarrier):
    action_id: str
    label: str
    placement: str
    enabled: bool
    side_effects: tuple[str, ...]
    confirmation_required: bool
    requires_active_debug_session: bool
    disabled_error: AgentError | None = None


@dataclass(frozen=True, slots=True)
class UiDebugCursorState:
    step_index: int
    step_scope_id: str | None
    group_key: str | None
    invocation_key: str | None
    pattern_group_identity: str | None
    dirty: bool = False


@dataclass(frozen=True, slots=True)
class UiDebugTerminalSummaryState:
    debug_session_id: str
    plate_scope_id: str
    terminal_status: str
    command_type: str | None
    axis_id: str | None
    snapshot_id: str | None
    snapshot_store_ref: str | None
    snapshot_store_backend: str | None
    step_name: str | None
    callable_name: str | None
    cursor: UiDebugCursorState | None
    completed_at_unix: float | None


@dataclass(frozen=True)
class UiDebugSessionIdentityCarrier:
    debug_session_id: str


@dataclass(frozen=True)
class UiDebugSnapshotStoreRefCarrier:
    snapshot_store_ref: str | None
    snapshot_store_backend: str | None


@dataclass(frozen=True, slots=True)
class UiProgressIdentityState:
    execution_id: str
    subject_id: str
    axis_id: str
    step_name: str


@dataclass(frozen=True, slots=True)
class UiDebugRuntimeFrameState(
    UiDebugSessionIdentityCarrier,
    UiDebugSnapshotStoreRefCarrier,
):
    progress_identity: UiProgressIdentityState
    cursor: UiDebugCursorState
    event_type: str
    step_name: str
    callable_name: str | None
    snapshot_id: str | None
    timestamp: float


@dataclass(frozen=True, slots=True)
class UiPipelineDebugSessionState(
    UiStateSurfaceEnvelope,
    UiCodeDocumentCurrentRevision,
    UiCurrentSnapshotState,
    SelectedScopeIdsCarrier,
):
    object_state_token: int
    current_plate_scope_id: str | None
    pipeline_scope_id: str | None
    manager_execution_state: str
    initialized: bool
    compiled: bool
    phase: str
    active_session_id: str | None
    execution_id: str | None
    axis_id: str | None
    selected_source_group: str | None
    snapshot_store_ref: str | None
    snapshot_store_backend: str | None
    terminal_status: str | None
    cursor: UiDebugCursorState | None
    terminal_summary: UiDebugTerminalSummaryState | None
    actions: tuple[UiDebugActionState, ...]
    current_frame: UiDebugRuntimeFrameState | None = None
    last_frame: UiDebugRuntimeFrameState | None = None


@dataclass(frozen=True, slots=True)
class UiSelectedPlateWorkflowRequest(
    SelectedScopeIdsCarrier,
    UiBridgeConfirmationRequirementCarrier,
    UiMutationRequestTokenCarrier,
    AgentCliRequest,
):
    workflow: UiSelectedPlateWorkflowKind
    observed_selection_revision_token: str | None = field(
        default=None,
        metadata={
            AGENT_PARAMETER_DESCRIPTION_METADATA_KEY: (
                "Action-selection revision returned as selection_revision_token by "
                "the action-catalog producer for the same selected-plate workflow; "
                "do not pass a PlateManager state revision token."
            ),
            AGENT_PARAMETER_PRODUCER_OUTPUT_CONTRACT_METADATA_KEY: UiActionCatalog,
        },
    )

    @classmethod
    def from_fields(
        cls,
        *,
        workflow: UiSelectedPlateWorkflowKind,
        target_scope_ids: list[str] | None = None,
        observed_selection_revision_token: str | None = None,
        request_token: str | None = None,
        require_confirmation: bool = False,
    ) -> "UiSelectedPlateWorkflowRequest":
        selected_scope_ids = SelectedScopeIdsArgument.from_optional_iterable(
            target_scope_ids
        )
        return cls(
            workflow=workflow,
            selected_scope_ids=selected_scope_ids.selected_scope_ids,
            observed_selection_revision_token=observed_selection_revision_token,
            request_token=UiMutationRequestToken(value=request_token),
            confirmation_requirement=UiBridgeConfirmationRequirement.from_flag(
                require_confirmation
            ),
        )

    def as_tool_arguments(self) -> JsonObject:
        """Project the declared workflow factory fields to MCP arguments."""

        return {
            "workflow": self.workflow.value,
            "target_scope_ids": list(self.selected_scope_ids),
            "observed_selection_revision_token": (
                self.observed_selection_revision_token
            ),
            "request_token": self.request_token.value,
            "require_confirmation": self.confirmation_is_required(),
        }


@dataclass(frozen=True, slots=True)
class UiSelectedPlateWorkflowResult:
    schema_version: str
    workflow: UiSelectedPlateWorkflowKind
    action_result: UiActionInvokeResult
    state_surface_id: str = DatasetListStateSurfaceIdentity.require_value()
    errors: tuple[AgentError, ...] = ()
    warnings: tuple[AgentWarning, ...] = ()
