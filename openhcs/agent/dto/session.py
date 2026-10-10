"""Request, result and state DTOs of the OpenHCS session operations."""

from __future__ import annotations

from dataclasses import dataclass, field

from openhcs.agent.dto.common import (
    SCHEMA_VERSION,
    AgentDataclassCliRequest,
    AgentError,
    AgentWarning,
)


@dataclass(frozen=True, slots=True)
class NoArgumentsRequest(AgentDataclassCliRequest):
    """An operation that needs nothing beyond the session."""


@dataclass(frozen=True, slots=True)
class DatasetRootsRequest(AgentDataclassCliRequest):
    """Dataset root directories to add; each root may offer several rows."""

    roots: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class DatasetTargetsRequest(AgentDataclassCliRequest):
    """The dataset scope ids an operation acts on."""

    scope_ids: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class DatasetRunRequest(AgentDataclassCliRequest):
    """Datasets to compile and execute in one batch.

    ``runtime_observation_export_path`` (writable under the agent path policy)
    exports runtime evidence; ``runtime_observation_export_scope`` is
    ``values`` (full values) or ``outcomes`` (no array values).
    """

    scope_ids: tuple[str, ...]
    runtime_observation_export_path: str | None = None
    runtime_observation_export_scope: str = "values"


@dataclass(frozen=True, slots=True)
class StopExecutionRequest(AgentDataclassCliRequest):
    """Stop the running batch; ``force`` kills the execution server."""

    force: bool = False


@dataclass(frozen=True, slots=True)
class DatasetPipelineSourceRequest(AgentDataclassCliRequest):
    """Replace one dataset's pipeline with a complete PipelineDocument source."""

    scope_id: str
    pipeline_source: str


@dataclass(frozen=True, slots=True)
class SessionEventsRequest(AgentDataclassCliRequest):
    """Events published after ``after_sequence``, waiting up to the timeout."""

    after_sequence: int = 0
    timeout_seconds: float = 0.0


@dataclass(frozen=True, slots=True)
class SessionOperationResult:
    """What one operation did: completed, accepted (work continues) or rejected."""

    operation_id: str
    status: str
    target_scope_ids: tuple[str, ...] = ()
    event_sequence: int = 0
    errors: tuple[AgentError, ...] = ()
    warnings: tuple[AgentWarning, ...] = ()
    schema_version: str = SCHEMA_VERSION

    @property
    def accepted(self) -> bool:
        return not self.errors


@dataclass(frozen=True, slots=True)
class SessionEventSummary:
    sequence: int
    kind: str
    scope_id: str
    message: str


@dataclass(frozen=True, slots=True)
class SessionEventBatch:
    events: tuple[SessionEventSummary, ...]
    last_sequence: int
    schema_version: str = SCHEMA_VERSION


@dataclass(frozen=True, slots=True)
class DatasetRowState:
    """One dataset row as every client sees it."""

    scope_id: str
    name: str
    root: str
    pipeline_path: str | None
    selected: bool
    initialized: bool
    compiled: bool
    init_pending: bool
    compile_pending: bool
    execution_active: bool
    status_prefix: str
    orchestrator_state: str | None
    execution_id: str | None
    terminal_status: str | None
    runtime_state: str | None
    runtime_percent: float | None
    queue_position: int | None
    output_scope_id: str | None = None
    output_root: str | None = None
    source_scope_id: str | None = None
    source_root: str | None = None
    debug_phase: str | None = None
    debug_session_id: str | None = None
    scope_accent_color: str | None = None


@dataclass(frozen=True, slots=True)
class DatasetListState:
    """The session's dataset list."""

    rows: tuple[DatasetRowState, ...]
    selected_scope_ids: tuple[str, ...]
    execution_state: str
    available_operation_ids: tuple[str, ...] = ()
    event_sequence: int = 0
    schema_version: str = SCHEMA_VERSION


@dataclass(frozen=True, slots=True)
class PipelineStepState:
    step_scope_id: str | None
    index: int
    name: str
    enabled: bool
    selected: bool
    dirty: bool
    default_diff: bool
    description: str | None = None
    debug_pause: bool = False
    function_names: tuple[str, ...] = ()
    function_ids: tuple[str, ...] = ()


@dataclass(frozen=True, slots=True)
class PipelineStepsState:
    """The current dataset's pipeline steps."""

    scope_id: str | None
    pipeline_scope_id: str | None
    steps: tuple[PipelineStepState, ...] = field(default=())
    event_sequence: int = 0
    schema_version: str = SCHEMA_VERSION


@dataclass(frozen=True, slots=True)
class DatasetRequest(AgentDataclassCliRequest):
    """The one dataset an operation acts on."""

    scope_id: str


@dataclass(frozen=True, slots=True)
class PipelineStepTargetsRequest(AgentDataclassCliRequest):
    """Steps of one dataset's pipeline, by their ObjectState scope ids."""

    scope_id: str
    step_scope_ids: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class PipelineFileRequest(AgentDataclassCliRequest):
    """Load one dataset's pipeline from a pipeline file (any registered format)."""

    scope_id: str
    path: str
